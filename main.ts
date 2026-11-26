// Steadyhand — a pump.fun paper bot built for the Sharpe sprint.
//
// The score is an hourly Sharpe ratio, so this bot is not trying to make the
// most SOL; it is trying to make a little SOL very evenly. Lumpy returns are
// punished twice — once in the mean when a dump lands, and again in the
// denominator — so every rule below shaves variance first and chases profit
// second:
//
//   * Entries need a crowd, not a hero: many distinct wallets buying over a
//     full window of slots, net inflow still accelerating, price hugging its
//     highs on both a short and a long lookback. One wallet supplying half
//     the buying, or one trade teleporting the price, disqualifies the
//     curve — both are variance wearing a costume.
//   * Stakes are deliberately small and capped per curve and per book, so
//     no single coin can dominate one hour, let alone the whole window.
//   * Exits are impatient: a hard stop, a trailing stop once a position has
//     proven itself, an exit when the tape's flow rolls over, an exit when
//     a whale dumps, a hard time limit — and a stall exit for positions
//     that went nowhere, because a slot parked in a dead curve is pure
//     tail risk with no drift to show for it.
//   * The harness wants at least 20 distinct coins traded. A probe engine
//     keeps that guardrail on pace with minimum-size round trips, spread
//     across the window so their small cost lands a little in every hour
//     instead of all in one.
//
// Nothing here reads a clock, an environment variable or a random source:
// the batch stream is the only input, so two runs over the same tape give
// the same orders byte for byte.

import {
  LAMPORTS_PER_SOL,
  runBot,
  type Batch,
  type BotState,
  type OrderInput,
  type Pubkey,
} from './vendor/makefun-bot.ts';

// The harness quotes amounts in lamports; the strategy thinks in SOL.
const SOL = Number(LAMPORTS_PER_SOL);
const SELL_CURVE_FEE = 0.0125; // the curve keeps 1.25% of a sell's gross
const BUY_SLIP_BPS = 1500; // entries tolerate 15%: we only buy into strength
const SELL_SLIP_BPS = 10_000; // exits never block on price — getting out is the point

// ------------------------------------------------------------------ windows
// Slots run at roughly 0.4 s of chain time. The short window is about twenty
// seconds of tape: long enough that one sniper cannot fake momentum, short
// enough that the move is still alive when we act on it. The long window
// (about two minutes) exists to tell a breakout from a bounce off an old peak.
const SHORT_SPAN = 48;
const LONG_SPAN = 280;
const FLOW_SPAN = 12; // slots of tape watched for a held position's flow rolling over

// ------------------------------------------------------------- entry gates
const MIN_CURVE_AGE = 2_000; // slots a curve must survive before it can be trusted
const MIN_REAL_SOL = 3; // thinner than this and the exit door is too narrow
const MAX_REAL_SOL = 35; // deeper than this and the easy part of the move is gone
const MIN_NET_INFLOW = 2.2; // SOL, buys minus sells, over the short window
const MIN_LONG_INFLOW = 4.5; // SOL over the long window: demand must be sustained
const MIN_BUY_PRINTS = 5; // separate buy trades inside the short window
const MIN_WALLETS = 8; // distinct buyers — a crowd, not a syndicate of one
const WHALE_LIMIT = 0.45; // no single buyer may supply more than this share of buy SOL
const MIN_RISE = 0.05; // short-window price gain must clear this …
const MAX_RISE = 0.55; // … and not this: +55% inside a minute is a blow-off, not a trend
const MIN_LONG_RISE = 0.05;
const MAX_LONG_RISE = 0.9;
const PEAK_TOLERANCE = 0.97; // price must sit within 3% of the short-window high
const LONG_PEAK_TOLERANCE = 0.97; // … and within 3% of the long-window high
const ACCEL_MIN = 1.4; // the newer half's net flow must beat the older half's by this
const MAX_PRICE_STEP = 0.35; // one print moving price more than this marks a jumpy tape

// ------------------------------------------------------------------ sizing
const OPEN_TICKET = 0.035; // first bite, SOL
const ADD_TICKET = 0.07; // added only while the position keeps proving itself
const MAX_PER_CURVE = 0.28; // hard cap per curve, adds included
const MAX_BOOK = 1.8; // hard cap on SOL at cost across the whole book
const MIN_TICKET = 0.01; // smallest buy still worth its transaction fee
const REENTRY_WAIT = 300; // slots to sit out a curve after leaving it
const MAX_TRIES = 2; // main entries per curve per window

// ------------------------------------------------------------------- exits
const HARD_STOP = 0.09; // value 9% under cost: out, no debate
const TRAIL_ARM = 0.02; // the trailing stop arms once value is 2% over cost
const TRAIL_GIVEBACK = 0.11; // … and an 11% fall from the peak then ends it
const FLOW_EXIT = -0.25; // net flow over FLOW_SPAN below this many SOL: out
const DUMP_ALARM = 1.0; // a single sell of this size (SOL) on our curve: out
const MAX_HOLD = 800; // slots; nothing rides longer than this
const STALL_AGE = 240; // a position this old that never gained is dead weight
const STALL_GAIN = 0.015; // "never gained" means its peak stayed under cost + 1.5%

// ------------------------------------------------------------ probe engine
// Probes are minimum-size round trips on deep curves, opened only when the
// pace says the guardrail is behind, and never twice in quick succession:
// their cost is a little spread plus fees, and spreading it across the
// window keeps every hour's returns alike — the whole game in a Sharpe rank.
const PROBE_TICKET = 0.01;
const PROBE_COINS = 25; // aim a little past the 20-coin floor
const PROBE_FILLS = 240;
const PROBE_GAP = 120; // minimum slots between two probe opens
const MAX_PROBES_OPEN = 1; // probes are seasoning, not a second strategy
const WINDOW_SECONDS = 14_400; // the scored window is six hours

// -------------------------------------------------------------- tape ledger
interface Print {
  slot: number;
  buy: boolean;
  sol: number;
  who: string;
  px: number; // virtual quote per virtual token just after this trade
}

interface Ledger {
  born: number | null; // slot of the CreateEvent, when seen
  prints: Print[]; // oldest first, pruned to what the rules can still look back over
  tries: number; // main entries already spent on this curve
  outAt: number; // slot of our last completed exit (-Infinity while never)
}

interface Stake {
  openedAt: number;
  highWater: number; // best exit value seen so far, SOL
  spent: number; // SOL paid in across all buys, fees included
  addPx: number; // tape price at the latest buy
  lastValue: number; // exit value at the latest batch, SOL
  filled: boolean; // at least one buy has actually landed
  closing: boolean; // an exit decision has been taken
}

const ledgers = new Map<Pubkey, Ledger>();
const stakes = new Map<Pubkey, Stake>();
const probes = new Map<Pubkey, 'buying' | 'selling'>();
const tradedCoins = new Set<Pubkey>();
let ownFills = 0;
let tapeStart: number | null = null; // first block_time seen on the tape
let tapeNow: number | null = null; // latest block_time seen
let lastProbeSlot = -1e12;

function ledgerOf(mint: Pubkey): Ledger {
  let led = ledgers.get(mint);
  if (led === undefined) {
    led = { born: null, prints: [], tries: 0, outAt: -1e12 };
    ledgers.set(mint, led);
  }
  return led;
}

/** Signed SOL flow (buys positive, sells negative) over the newest `span` slots. */
function flowOver(led: Ledger, now: number, span: number): number {
  let net = 0;
  for (let i = led.prints.length - 1; i >= 0; i--) {
    const p = led.prints[i]!;
    if (p.slot <= now - span) break;
    net += p.buy ? p.sol : -p.sol;
  }
  return net;
}

// ------------------------------------------------------------ window snapshot
interface WindowView {
  buySol: number;
  sellSol: number;
  buyCount: number;
  wallets: Map<string, number>; // buyer -> SOL bought inside the window
  olderNet: number; // signed flow in the window's first half
  newerNet: number; // signed flow in its second half
  firstPx: number; // price at the window's edge (-1 when the tape is empty there)
  lastPx: number;
  peakPx: number;
  worstStep: number; // largest one-print relative price move, either direction
}

function viewWindow(led: Ledger, now: number, span: number): WindowView {
  const from = now - span;
  const mid = now - span / 2;
  const v: WindowView = {
    buySol: 0,
    sellSol: 0,
    buyCount: 0,
    wallets: new Map(),
    olderNet: 0,
    newerNet: 0,
    firstPx: -1,
    lastPx: 0,
    peakPx: 0,
    worstStep: 0,
  };
  let prevPx = -1;
  for (const p of led.prints) {
    if (p.slot <= from) {
      // Prints at or before the edge set the base the window is measured from.
      v.firstPx = p.px;
      prevPx = p.px;
      continue;
    }
    if (v.firstPx < 0) v.firstPx = p.px;
    if (prevPx > 0) {
      const step = Math.abs(p.px / prevPx - 1);
      if (step > v.worstStep) v.worstStep = step;
    }
    prevPx = p.px;
    const signed = p.buy ? p.sol : -p.sol;
    if (p.slot <= mid) v.olderNet += signed;
    else v.newerNet += signed;
    if (p.buy) {
      v.buySol += p.sol;
      v.buyCount++;
      v.wallets.set(p.who, (v.wallets.get(p.who) ?? 0) + p.sol);
    } else {
      v.sellSol += p.sol;
    }
    if (p.px > v.peakPx) v.peakPx = p.px;
    v.lastPx = p.px;
  }
  return v;
}

/** Highest and lowest print prices inside the long window. */
function longExtremes(led: Ledger, now: number): { peak: number; trough: number } {
  let peak = 0;
  let trough = -1;
  for (const p of led.prints) {
    if (p.slot <= now - LONG_SPAN) continue;
    if (p.px > peak) peak = p.px;
    if (trough < 0 || p.px < trough) trough = p.px;
  }
  return { peak, trough };
}

// --------------------------------------------------------------- entry judge
// The screen runs as stages, cheapest rejections first. A curve has to pass
// every stage; failing any one is final for this batch.
function judgeEntry(led: Ledger, now: number, realSol: number): boolean {
  // Stage 0 — the curve itself: old enough to have survived its launch
  // burst, deep enough to exit through, not so deep the move is spent.
  if (realSol < MIN_REAL_SOL || realSol > MAX_REAL_SOL) return false;
  if (led.born === null || now - led.born < MIN_CURVE_AGE) return false;

  const v = viewWindow(led, now, SHORT_SPAN);

  // Stage 1 — participation. Enough separate buyers that no one wallet is
  // the market: a whale-led tape can vanish in a single sell, a crowd's
  // demand cannot.
  if (v.buyCount < MIN_BUY_PRINTS || v.wallets.size < MIN_WALLETS) return false;
  let whale = 0;
  for (const s of v.wallets.values()) if (s > whale) whale = s;
  if (v.buySol <= 0 || whale > WHALE_LIMIT * v.buySol) return false;

  // Stage 2 — direction. Money must still be arriving, on both lookbacks,
  // and arriving faster than it was a moment ago; decelerating inflow is
  // how these moves end.
  if (v.buySol - v.sellSol < MIN_NET_INFLOW) return false;
  if (v.newerNet <= 0 || v.newerNet < ACCEL_MIN * v.olderNet) return false;
  if (flowOver(led, now, LONG_SPAN) < MIN_LONG_INFLOW) return false;

  // Stage 3 — shape. A measured climb that is still at its highs on both
  // lookbacks. Too flat is noise, too steep is a blow-off, and below the
  // long peak is a bounce — bounces are where Sharpe goes to die.
  if (v.firstPx <= 0 || v.peakPx <= 0) return false;
  const gain = v.lastPx / v.firstPx - 1;
  if (gain < MIN_RISE || gain > MAX_RISE) return false;
  if (v.lastPx < v.peakPx * PEAK_TOLERANCE) return false;
  const ext = longExtremes(led, now);
  if (ext.peak > 0 && v.lastPx < ext.peak * LONG_PEAK_TOLERANCE) return false;
  if (ext.trough > 0) {
    const longGain = v.lastPx / ext.trough - 1;
    if (longGain < MIN_LONG_RISE || longGain > MAX_LONG_RISE) return false;
  }

  // Stage 4 — smoothness. Reject a tape where a single print teleported
  // the price: smooth tapes drift, jumpy tapes gap, and gaps are variance.
  if (v.worstStep > MAX_PRICE_STEP) return false;
  return true;
}

// ---------------------------------------------------------------- valuation
/** What closing a holding pays right now, in SOL, after curve and tx fees. */
function exitValueSol(state: BotState, mint: Pubkey, tokens: bigint): number {
  const curve = state.curves.get(mint);
  if (curve === undefined) return 0;
  const vq = Number(curve.virtual_quote_reserves);
  const vt = Number(curve.virtual_token_reserves);
  const n = Number(tokens);
  const grossSol = (n * vq) / (vt + n) / SOL;
  return grossSol * (1 - SELL_CURVE_FEE) - Number(state.txFeeLamports()) / SOL;
}

// ------------------------------------------------------------- batch phases
interface Ctx {
  state: BotState;
  now: number;
  orders: OrderInput[];
  orderCap: number; // harness cap on orders per reply
  txSol: number; // one transaction's fee, in SOL
  pendingOn: Map<Pubkey, number>; // mint -> orders of ours still in flight
  hot: Set<Pubkey>; // curves that printed a trade in this batch
  dumped: Set<Pubkey>; // curves hit by a whale-sized single sell in this batch
  freeSol: number; // spendable cash, decremented as orders are queued
  room: number; // open-position slots left, decremented as entries are queued
}

/** Fold one batch into the ledgers: our fills, curve births, every print. */
function absorb(ctx: Ctx, batch: Batch): void {
  for (const f of batch.fills) {
    // Harness closes carry client_ids starting with '_'; only our own
    // fills count toward the fill guardrail and the traded-coin set.
    if (f.status === 'filled' && !f.client_id.startsWith('_')) {
      ownFills++;
      tradedCoins.add(f.mint);
    }
  }
  for (const e of batch.events) {
    if (e.block_time !== null) {
      if (tapeStart === null) tapeStart = e.block_time;
      if (tapeNow === null || e.block_time > tapeNow) tapeNow = e.block_time;
    }
    if (e.event === 'CreateEvent') {
      ledgerOf(e.mint).born = e.slot;
    } else if (e.event === 'TradeEvent') {
      const led = ledgerOf(e.mint);
      const sol = Number(e.sol_amount) / SOL;
      led.prints.push({
        slot: e.slot,
        buy: e.is_buy,
        sol,
        who: e.user,
        px: Number(e.virtual_quote_reserves) / Number(e.virtual_token_reserves),
      });
      ctx.hot.add(e.mint);
      if (!e.is_buy && sol >= DUMP_ALARM) ctx.dumped.add(e.mint);
    }
  }
  // Prune prints older than the deepest lookback any rule still uses.
  const keep = LONG_SPAN + FLOW_SPAN + 8;
  for (const mint of ctx.hot) {
    const led = ledgers.get(mint)!;
    let cut = 0;
    while (cut < led.prints.length && led.prints[cut]!.slot <= ctx.now - keep) cut++;
    if (cut > 0) led.prints.splice(0, cut);
  }
}

function sellAll(ctx: Ctx, mint: Pubkey, tokens: bigint): void {
  ctx.orders.push({ side: 'sell', mint, token_amount: tokens, max_slippage_bps: SELL_SLIP_BPS });
}

/** Positions are managed before anything new is bought: exits come first. */
function manageExits(ctx: Ctx): void {
  for (const [mint, st] of stakes) {
    const held = ctx.state.positions.get(mint);
    if (held === undefined) {
      // Nothing held and nothing in flight: the exit landed (or the entry
      // never did). A buy that never filled must not burn one of the
      // curve's tries, so hand it back.
      if (!ctx.pendingOn.has(mint)) {
        stakes.delete(mint);
        const led = ledgerOf(mint);
        if (st.filled) led.outAt = ctx.now;
        else led.tries--;
      }
      continue;
    }
    st.filled = true;
    const curve = ctx.state.curves.get(mint);
    if (curve === undefined || curve.complete) continue;
    const value = exitValueSol(ctx.state, mint, held.token_amount);
    const cost = Number(held.cost_lamports) / SOL;
    if (value > st.highWater) st.highWater = value;
    st.lastValue = value;
    const led = ledgerOf(mint);
    let out = st.closing;
    if (!out && value < cost * (1 - HARD_STOP)) out = true;
    if (!out && st.highWater >= cost * (1 + TRAIL_ARM) && value < st.highWater * (1 - TRAIL_GIVEBACK)) out = true;
    if (!out && flowOver(led, ctx.now, FLOW_SPAN) < FLOW_EXIT) out = true;
    if (!out && ctx.dumped.has(mint)) out = true;
    if (!out && ctx.now - st.openedAt > MAX_HOLD) out = true;
    // Stall rule: old and never in profit. Whatever this slot might still
    // do here, a fresh screened entry is the better Sharpe bet.
    if (!out && ctx.now - st.openedAt > STALL_AGE && st.highWater < cost * (1 + STALL_GAIN)) out = true;
    if (!out) continue;
    st.closing = true;
    let sellPending = false;
    for (const p of ctx.state.pending.values()) {
      if (p.order.mint === mint && p.order.side === 'sell') {
        sellPending = true;
        break;
      }
    }
    if (sellPending) continue; // one exit order per position is enough
    if (ctx.orders.length >= ctx.orderCap) break;
    sellAll(ctx, mint, held.token_amount);
  }
}

/** A probe's sell goes out on the first batch after its buy has landed. */
function manageProbes(ctx: Ctx): void {
  for (const [mint, phase] of probes) {
    const held = ctx.state.positions.get(mint);
    if (held === undefined) {
      if (!ctx.pendingOn.has(mint)) probes.delete(mint);
      continue;
    }
    const curve = ctx.state.curves.get(mint);
    if (curve === undefined || curve.complete || ctx.pendingOn.has(mint)) continue;
    if (ctx.orders.length >= ctx.orderCap) break;
    sellAll(ctx, mint, held.token_amount);
    if (phase === 'buying') probes.set(mint, 'selling');
  }
}

// ------------------------------------------------------------------ entries
function manageEntries(ctx: Ctx): void {
  const caps = ctx.state.hello.caps;
  // One position slot always stays free so a probe can open when it needs to.
  const mainCap = Math.min(4, Math.max(0, caps.max_open_positions - 1));
  let mainOpen = stakes.size;
  let bookSol = 0;
  for (const [mint, st] of stakes) {
    bookSol += Math.max(st.spent, Number(ctx.state.positions.get(mint)?.cost_lamports ?? 0n) / SOL);
  }
  for (const mint of ctx.hot) {
    if (ctx.orders.length >= ctx.orderCap) break;
    const curve = ctx.state.curves.get(mint);
    if (curve === undefined || curve.complete) continue;
    if (ctx.pendingOn.has(mint) || probes.has(mint)) continue;
    const led = ledgers.get(mint)!;
    const px = Number(curve.virtual_quote_reserves) / Number(curve.virtual_token_reserves);
    const realSol = Number(curve.real_quote_reserves) / SOL;
    const st = stakes.get(mint);
    let want = 0;
    if (st === undefined) {
      if (ctx.room <= 0 || mainOpen >= mainCap) continue;
      if (led.tries >= MAX_TRIES || ctx.now - led.outAt < REENTRY_WAIT) continue;
      if (!judgeEntry(led, ctx.now, realSol)) continue;
      want = Math.min(OPEN_TICKET, MAX_PER_CURVE);
    } else {
      // Adds are earned, never automatic: price above the last buy, the
      // position in profit on its latest mark, inflow still clearing the
      // entry bar, and room left under the per-curve cap.
      if (st.closing || !st.filled) continue;
      if (st.spent >= MAX_PER_CURVE - MIN_TICKET) continue;
      const held = ctx.state.positions.get(mint);
      if (held === undefined) continue;
      if (px < st.addPx) continue;
      if (st.lastValue < Number(held.cost_lamports) / SOL) continue;
      if (flowOver(led, ctx.now, SHORT_SPAN) < MIN_NET_INFLOW) continue;
      if (realSol > MAX_REAL_SOL) continue;
      want = Math.min(ADD_TICKET, MAX_PER_CURVE - st.spent);
    }
    // The harness caps one batch's buys on a curve by its real reserves;
    // the book cap and the cash on hand cap them further. Whatever survives
    // all three, and is still worth its fee, goes out.
    const sizeCap = Math.floor(Number(ctx.state.maxBuyLamports(mint))) / SOL;
    let amount = Math.min(sizeCap, want, MAX_BOOK - bookSol);
    if (amount > ctx.freeSol - ctx.txSol) amount = ctx.freeSol - ctx.txSol;
    if (amount < MIN_TICKET) continue;
    ctx.orders.push({
      side: 'buy',
      mint,
      quote_lamports: BigInt(Math.floor(amount * SOL)),
      max_slippage_bps: BUY_SLIP_BPS,
    });
    ctx.freeSol -= amount + ctx.txSol;
    bookSol += amount;
    if (st === undefined) {
      stakes.set(mint, {
        openedAt: ctx.now,
        highWater: 0,
        spent: amount,
        addPx: px,
        lastValue: 0,
        filled: false,
        closing: false,
      });
      led.tries++;
      ctx.room--;
      mainOpen++;
    } else {
      st.spent += amount;
      st.addPx = px;
    }
  }
}

// -------------------------------------------------------------- probe opens
function maybeProbe(ctx: Ctx): void {
  if (probes.size >= MAX_PROBES_OPEN || ctx.room <= 0) return;
  if (tapeStart === null || tapeNow === null) return;
  if (ctx.now - lastProbeSlot < PROBE_GAP) return; // spread the cost across hours
  // Pace is measured against the share of the six-hour window already gone:
  // coins and fills should both be at least that far along.
  const elapsed = Math.min(1, (tapeNow - tapeStart) / WINDOW_SECONDS);
  const behindCoins = tradedCoins.size < Math.ceil(PROBE_COINS * elapsed);
  const behindFills = ownFills < Math.ceil(PROBE_FILLS * elapsed);
  if (!behindCoins && !behindFills) return;
  // A probe curve must be deep enough that the minimum ticket is a small
  // share of its real reserves (the harness caps order size by that share).
  const minReal = (PROBE_TICKET * 10_000) / ctx.state.hello.caps.max_order_bps_of_real_reserve;
  for (const mint of ctx.hot) {
    if (ctx.orders.length >= ctx.orderCap) break;
    if (stakes.has(mint) || probes.has(mint) || ctx.pendingOn.has(mint)) continue;
    if (ctx.state.positions.has(mint)) continue;
    if (behindCoins && !behindFills && tradedCoins.has(mint)) continue;
    const curve = ctx.state.curves.get(mint);
    if (curve === undefined || curve.complete) continue;
    if (Number(curve.real_quote_reserves) / SOL < minReal * 1.5) continue;
    if (ctx.freeSol < PROBE_TICKET + 2 * ctx.txSol) break;
    ctx.orders.push({
      side: 'buy',
      mint,
      quote_lamports: BigInt(Math.floor(PROBE_TICKET * SOL)),
      max_slippage_bps: BUY_SLIP_BPS,
    });
    probes.set(mint, 'buying');
    lastProbeSlot = ctx.now;
    ctx.freeSol -= PROBE_TICKET + ctx.txSol;
    break; // one probe per batch at most — the gap rule does the pacing
  }
}

// -------------------------------------------------------------------- main
await runBot({
  onBatch(state: BotState, batch: Batch): OrderInput[] {
    const pendingOn = new Map<Pubkey, number>();
    for (const p of state.pending.values()) {
      pendingOn.set(p.order.mint, (pendingOn.get(p.order.mint) ?? 0) + 1);
    }
    const ctx: Ctx = {
      state,
      now: batch.slot,
      orders: [],
      orderCap: state.hello.caps.max_orders_per_batch,
      txSol: Number(state.txFeeLamports()) / SOL,
      pendingOn,
      hot: new Set<Pubkey>(),
      dumped: new Set<Pubkey>(),
      freeSol: Number(state.freeCashLamports()) / SOL,
      room: state.hello.caps.max_open_positions - state.committedPositionCount(),
    };
    absorb(ctx, batch);
    manageExits(ctx); // exits before entries, always
    manageProbes(ctx); // close probes whose buys landed
    manageEntries(ctx); // new stakes and earned adds
    maybeProbe(ctx); // top up the guardrail if the pace demands it
    return ctx.orders;
  },
});
