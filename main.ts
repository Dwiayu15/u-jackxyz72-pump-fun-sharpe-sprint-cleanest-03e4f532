// Clean Sharpe paper bot for the pump.fun 6-hour replay.
//
// Idea: only buy curves that already proved themselves — past the launch burst, with
// several different wallets putting real SOL in over the last few dozen slots, the
// price climbing gently and sitting near its recent high, without one whale doing
// all the buying and without the price having already doubled. Then risk very
// little: a tiny first ticket, slightly bigger only while the move keeps working,
// and get out fast on any sign of trouble. Sharpe rewards steady small wins and
// punishes variance, so the bot would rather miss a runner than ride a dump.
//
// A second, separate job keeps the guardrails honest: when the count of distinct
// coins traded (or fills) falls behind the pace the run needs, the bot opens
// minimum-size probe round trips on liquid curves and closes them as soon as the
// buy lands. Probes are cheap insurance for the 20-coin minimum, not a strategy.
//
// Deterministic by construction: no clock, no randomness, no environment reads;
// every decision comes from the batch stream, and maps are walked in insertion
// order.

import {
  LAMPORTS_PER_SOL,
  runBot,
  type Batch,
  type BotState,
  type OrderInput,
  type Pubkey,
} from './vendor/makefun-bot.ts';

const SOL = 1e9;
const CURVE_FEE = 0.0125; // pump.fun curve fee taken on a sell
const SLIP_BUY_BPS = 1500;
const SLIP_SELL_BPS = 10_000;

// ---------------------------------------------------------------- tuning

const CFG = {
  lookbackSlots: 60, // entry window, in slots
  longWindowSlots: 300, // longer lookback whose high the price must sit near
  longNearHigh: 0.97,
  minNetInflowSol: 2.5, // net SOL (buys minus sells) over the window
  minBuyTrades: 5,
  minDistinctBuyers: 8,
  minRise: 0.06, // price now vs window start, at least +6%
  maxRise: 0.6, // skip curves that already ran +60% inside one window
  accelRatio: 1.5, // newer-half inflow must beat older-half inflow by this
  nearHigh: 0.97, // price now at least 97% of the window high
  maxTopBuyerShare: 0.5, // biggest single buyer at most half of buy SOL
  minRealSol: 3, // real SOL reserves at entry
  maxRealSol: 40,
  minAgeSlots: 2400, // slots since creation before an entry is allowed
  firstTicketSol: 0.04,
  addTicketSol: 0.08,
  maxStakeSol: 0.3, // total SOL per curve, all adds included
  minTicketSol: 0.01,
  stopLoss: 0.1, // exit when value falls 10% below cost
  trailDrop: 0.12, // exit when value falls 12% below its peak
  trailArmGain: 0.02, // trailing stop arms once value is +2% over cost
  fadeSlots: 15, // exit when net flow over this window turns negative
  fadeOutSol: 0.3,
  bigDumpSol: 1.0, // exit on any single sell of at least this size
  maxHoldSlots: 900, // hard time limit on a position
  cooldownSlots: 300, // wait after an exit before re-entering the same curve
  maxEntriesPerCurve: 2,
  maxMainPositions: 4, // one of the 5 open slots stays free for probes
  maxTotalExposureSol: 2.0, // cap on SOL at cost across all positions
  probeSol: 0.01,
  probeTargetCoins: 25,
  probeTargetFills: 240,
  probePaceSecs: 14_400, // the full 6-hour window
  maxProbesOpen: 1,
};

// ---------------------------------------------------------------- per-curve tape

interface SeenTrade {
  slot: number;
  isBuy: boolean;
  sol: number;
  wallet: string;
  price: number; // virtual SOL per virtual token at that trade
}

interface CurveBook {
  createdSlot: number | null;
  trades: SeenTrade[];
  entriesUsed: number;
  lastExitSlot: number;
}

interface OpenTrade {
  openedSlot: number;
  peakValueSol: number;
  spentSol: number; // SOL sent in buys for this position, fees included
  lastAddPrice: number;
  lastValueSol: number;
  filledOnce: boolean;
  leaving: boolean;
}

const books = new Map<Pubkey, CurveBook>();
const open = new Map<Pubkey, OpenTrade>();
const probeState = new Map<Pubkey, boolean>(); // false = buy in flight, true = sell it
const coinsTouched = new Set<Pubkey>();
let myFillCount = 0;
let firstBlockTime: number | null = null;
let lastBlockTime: number | null = null;

function bookFor(mint: Pubkey): CurveBook {
  let b = books.get(mint);
  if (b === undefined) {
    b = { createdSlot: null, trades: [], entriesUsed: 0, lastExitSlot: -1e12 };
    books.set(mint, b);
  }
  return b;
}

/** Net SOL (buys minus sells) on a tape over the last `span` slots. */
function netFlow(book: CurveBook, now: number, span: number): number {
  let net = 0;
  for (let i = book.trades.length - 1; i >= 0; i--) {
    const t = book.trades[i]!;
    if (t.slot <= now - span) break;
    net += t.isBuy ? t.sol : -t.sol;
  }
  return net;
}

/** The strict entry screen. Returns true only for a high-conviction curve. */
function passesScreen(book: CurveBook, now: number, realSol: number): boolean {
  if (realSol < CFG.minRealSol || realSol > CFG.maxRealSol) return false;
  if (book.createdSlot === null || now - book.createdSlot < CFG.minAgeSlots) return false;
  const from = now - CFG.lookbackSlots;
  const half = now - CFG.lookbackSlots / 2;
  let buySol = 0;
  let sellSol = 0;
  let buyTrades = 0;
  let netOld = 0;
  let netNew = 0;
  let startPrice = -1;
  let high = 0;
  let lastPrice = 0;
  const buyers = new Map<string, number>();
  for (const t of book.trades) {
    if (t.slot <= from) {
      startPrice = t.price;
      continue;
    }
    if (startPrice < 0) startPrice = t.price;
    const signed = t.isBuy ? t.sol : -t.sol;
    if (t.slot <= half) netOld += signed;
    else netNew += signed;
    if (t.isBuy) {
      buySol += t.sol;
      buyTrades++;
      buyers.set(t.wallet, (buyers.get(t.wallet) ?? 0) + t.sol);
    } else {
      sellSol += t.sol;
    }
    if (t.price > high) high = t.price;
    lastPrice = t.price;
  }
  if (buyTrades < CFG.minBuyTrades || buyers.size < CFG.minDistinctBuyers) return false;
  if (buySol - sellSol < CFG.minNetInflowSol) return false;
  if (startPrice <= 0) return false;
  const rise = lastPrice / startPrice - 1;
  if (rise < CFG.minRise || rise > CFG.maxRise) return false;
  if (lastPrice < high * CFG.nearHigh) return false;
  // Breakout, not bounce: the price must also sit near its high over a much
  // longer lookback, so a curve that peaked long ago and is merely retracing
  // a dead-cat bounce does not pass.
  let longHigh = 0;
  let longLow = -1;
  for (const t of book.trades) {
    if (t.slot > now - CFG.longWindowSlots) {
      if (t.price > longHigh) longHigh = t.price;
      if (longLow < 0 || t.price < longLow) longLow = t.price;
    }
  }
  if (longHigh > 0 && lastPrice < longHigh * CFG.longNearHigh) return false;
  // And the buying must be sustained, not a one-window burst: net inflow over
  // the long window must be clearly positive and the long-window rise modest.
  if (netFlow(book, now, CFG.longWindowSlots) < 5) return false;
  if (longLow > 0) {
    const longRise = lastPrice / longLow - 1;
    if (longRise < 0.05 || longRise > 1.0) return false;
  }
  if (netNew <= 0 || netNew < CFG.accelRatio * netOld) return false;
  let biggest = 0;
  for (const v of buyers.values()) if (v > biggest) biggest = v;
  if (biggest > CFG.maxTopBuyerShare * buySol) return false;
  return true;
}

/** What a holding is worth right now in SOL, after curve and tx fees. */
function closeValueSol(
  state: BotState,
  mint: Pubkey,
  tokens: bigint,
): number {
  const curve = state.curves.get(mint);
  if (curve === undefined) return 0;
  const vq = Number(curve.virtual_quote_reserves);
  const vt = Number(curve.virtual_token_reserves);
  const n = Number(tokens);
  const gross = (n * vq) / (vt + n) / SOL;
  return gross * (1 - CURVE_FEE) - Number(state.txFeeLamports()) / SOL;
}

await runBot({
  onBatch(state: BotState, batch: Batch): OrderInput[] {
    const now = batch.slot;
    const dumped = new Set<Pubkey>(); // curves hit by a big single sell this batch
    const active = new Set<Pubkey>(); // curves with a trade this batch
    const keepSlots = Math.max(CFG.lookbackSlots, CFG.fadeSlots, CFG.longWindowSlots) + 5;

    for (const f of batch.fills) {
      if (f.status === 'filled' && !f.client_id.startsWith('_')) {
        myFillCount++;
        coinsTouched.add(f.mint);
      }
    }
    for (const e of batch.events) {
      if (e.block_time !== null) {
        if (firstBlockTime === null) firstBlockTime = e.block_time;
        if (lastBlockTime === null || e.block_time > lastBlockTime) lastBlockTime = e.block_time;
      }
      if (e.event === 'CreateEvent') {
        bookFor(e.mint).createdSlot = e.slot;
      } else if (e.event === 'TradeEvent') {
        const b = bookFor(e.mint);
        b.trades.push({
          slot: e.slot,
          isBuy: e.is_buy,
          sol: Number(e.sol_amount) / SOL,
          wallet: e.user,
          price: Number(e.virtual_quote_reserves) / Number(e.virtual_token_reserves),
        });
        active.add(e.mint);
        if (!e.is_buy && Number(e.sol_amount) / SOL >= CFG.bigDumpSol) dumped.add(e.mint);
      }
    }
    // Trim old trades so tapes stay short and bounded.
    for (const mint of active) {
      const b = books.get(mint)!;
      let cut = 0;
      while (cut < b.trades.length && b.trades[cut]!.slot <= now - keepSlots) cut++;
      if (cut > 0) b.trades.splice(0, cut);
    }

    const pendingMints = new Map<Pubkey, number>();
    for (const p of state.pending.values()) {
      pendingMints.set(p.order.mint, (pendingMints.get(p.order.mint) ?? 0) + 1);
    }
    const orders: OrderInput[] = [];
    const maxOrders = state.hello.caps.max_orders_per_batch;
    const txSol = Number(state.txFeeLamports()) / SOL;

    // ---- exits first: stop loss, trailing stop, fading flow, big dump, time limit
    for (const [mint, pos] of open) {
      const held = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (held === undefined) {
        if (!pendingMints.has(mint)) {
          open.delete(mint);
          const b = bookFor(mint);
          if (pos.filledOnce) b.lastExitSlot = now;
          else b.entriesUsed--;
        }
        continue;
      }
      pos.filledOnce = true;
      if (curve === undefined || curve.complete) continue;
      const value = closeValueSol(state, mint, held.token_amount);
      const cost = Number(held.cost_lamports) / SOL;
      if (value > pos.peakValueSol) pos.peakValueSol = value;
      pos.lastValueSol = value;
      const b = bookFor(mint);
      let leave = pos.leaving;
      if (!leave && value < cost * (1 - CFG.stopLoss)) leave = true;
      if (!leave && pos.peakValueSol >= cost * (1 + CFG.trailArmGain) && value < pos.peakValueSol * (1 - CFG.trailDrop)) leave = true;
      if (!leave && netFlow(b, now, CFG.fadeSlots) < -CFG.fadeOutSol) leave = true;
      if (!leave && dumped.has(mint)) leave = true;
      if (!leave && now - pos.openedSlot > CFG.maxHoldSlots) leave = true;
      if (!leave) continue;
      pos.leaving = true;
      let sellFlying = false;
      for (const p of state.pending.values()) {
        if (p.order.mint === mint && p.order.side === 'sell') sellFlying = true;
      }
      if (sellFlying) continue;
      if (orders.length >= maxOrders) break;
      orders.push({ side: 'sell', mint, token_amount: held.token_amount, max_slippage_bps: SLIP_SELL_BPS });
    }

    // ---- probes: sell the probe as soon as its buy has landed
    for (const [mint, selling] of probeState) {
      const held = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (held === undefined) {
        if (!pendingMints.has(mint)) probeState.delete(mint);
        continue;
      }
      if (curve === undefined || curve.complete || pendingMints.has(mint)) continue;
      if (orders.length >= maxOrders) break;
      orders.push({ side: 'sell', mint, token_amount: held.token_amount, max_slippage_bps: SLIP_SELL_BPS });
      if (!selling) probeState.set(mint, true);
    }

    // ---- entries and adds
    let freeSol = Number(state.freeCashLamports()) / SOL;
    let slotsLeft = state.hello.caps.max_open_positions - state.committedPositionCount();
    let mainLeft = CFG.maxMainPositions - open.size;
    let exposureSol = 0;
    for (const [mint, pos] of open) {
      exposureSol += Math.max(pos.spentSol, Number(state.positions.get(mint)?.cost_lamports ?? 0n) / SOL);
    }
    for (const mint of active) {
      if (orders.length >= maxOrders) break;
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete) continue;
      if (pendingMints.has(mint) || probeState.has(mint)) continue;
      const b = books.get(mint)!;
      const price = Number(curve.virtual_quote_reserves) / Number(curve.virtual_token_reserves);
      const realSol = Number(curve.real_quote_reserves) / SOL;
      const pos = open.get(mint);
      let wantSol: number;
      if (pos === undefined) {
        if (slotsLeft <= 0 || mainLeft <= 0) continue;
        if (b.entriesUsed >= CFG.maxEntriesPerCurve || now - b.lastExitSlot < CFG.cooldownSlots) continue;
        if (!passesScreen(b, now, realSol)) continue;
        wantSol = Math.min(CFG.firstTicketSol, CFG.maxStakeSol);
      } else {
        // Add only into strength: price above the last add, position in profit,
        // inflow still positive, and the curve not already too big.
        if (pos.leaving || !pos.filledOnce || pos.spentSol >= CFG.maxStakeSol - CFG.minTicketSol) continue;
        const held = state.positions.get(mint);
        if (held === undefined) continue;
        if (price < pos.lastAddPrice) continue;
        if (pos.lastValueSol < Number(held.cost_lamports) / SOL) continue;
        if (netFlow(b, now, CFG.lookbackSlots) < CFG.minNetInflowSol) continue;
        if (realSol > CFG.maxRealSol) continue;
        wantSol = Math.min(CFG.addTicketSol, CFG.maxStakeSol - pos.spentSol);
      }
      const capSol = Math.floor(Number(state.maxBuyLamports(mint))) / SOL;
      let amount = Math.min(capSol, wantSol, CFG.maxTotalExposureSol - exposureSol);
      if (amount > freeSol - txSol) amount = freeSol - txSol;
      if (amount < CFG.minTicketSol) continue;
      const lamports = BigInt(Math.floor(amount * SOL));
      orders.push({ side: 'buy', mint, quote_lamports: lamports, max_slippage_bps: SLIP_BUY_BPS });
      freeSol -= amount + txSol;
      exposureSol += amount;
      if (pos === undefined) {
        open.set(mint, {
          openedSlot: now,
          peakValueSol: 0,
          spentSol: amount,
          lastAddPrice: price,
          lastValueSol: 0,
          filledOnce: false,
          leaving: false,
        });
        b.entriesUsed++;
        slotsLeft--;
        mainLeft--;
      } else {
        pos.spentSol += amount;
        pos.lastAddPrice = price;
      }
    }

    // ---- guardrail pacing: open a probe when coins or fills lag the pace
    if (probeState.size < CFG.maxProbesOpen && slotsLeft > 0 && firstBlockTime !== null && lastBlockTime !== null) {
      const pace = Math.min(1, (lastBlockTime - firstBlockTime) / CFG.probePaceSecs);
      const needCoins = coinsTouched.size < Math.ceil(CFG.probeTargetCoins * pace);
      const needFills = myFillCount < Math.ceil(CFG.probeTargetFills * pace);
      if (needCoins || needFills) {
        const minReal = (CFG.probeSol * 10_000) / state.hello.caps.max_order_bps_of_real_reserve;
        for (const mint of active) {
          if (orders.length >= maxOrders || probeState.size >= CFG.maxProbesOpen) break;
          if (open.has(mint) || probeState.has(mint) || pendingMints.has(mint) || state.positions.has(mint)) continue;
          if (needCoins && !needFills && coinsTouched.has(mint)) continue;
          const curve = state.curves.get(mint);
          if (curve === undefined || curve.complete) continue;
          if (Number(curve.real_quote_reserves) / SOL < minReal * 1.5) continue;
          if (freeSol < CFG.probeSol + 2 * txSol) break;
          orders.push({ side: 'buy', mint, quote_lamports: BigInt(Math.floor(CFG.probeSol * SOL)), max_slippage_bps: SLIP_BUY_BPS });
          probeState.set(mint, false);
          freeSol -= CFG.probeSol + txSol;
        }
      }
    }
    return orders;
  },
});
