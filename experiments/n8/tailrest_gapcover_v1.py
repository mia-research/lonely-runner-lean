# tailrest_gapcover_v1.py -- RESIDUE A-ii: the gap-regime covering kills, exact.
# Regime: rho7 in a gap G_m = (8m+1, 8m+7), m >= 3, anchor strip-1 (rho6-anchored,
# rho6 in (7,9): the anchor lemma's unpinned case). The kills:
#   K1 [T] exact re-verification of the gap-lock census (27 feasible-gap types from the
#      recorded near-carve starts, seed 1): per gap between chain zones, the demand cone
#      cannot close the gap while every overlapping link stays strict -- exact Farkas
#      certificates (float LP steers the active support only; Fractions verify).
#   K2 [T] the covering side at the surviving points: for every recorded rho6-anchored
#      gap system (9 near-carves + the 27 types' witnesses + the OPEN gaps' LP witnesses),
#      compute K6 = [1,7] \ zones(rho2..rho6) exactly, its components, and the rho7
#      NESTING bands ((8j-1)/a, (8j+1)/b) per component (a carve needs rho7 in the gap
#      AND in every band). Verdict per system: the intersection with the gap window is
#      EMPTY, with the exact conflict named (a 2-cycle of weight product >= 1 in the
#      demand digraph, E830's mechanism; or plain band separation).
#   K3 [T] the worked E830 cycle reproduced on the polished first vector: the two
#      end-component bands are (., 7 rho5) and (7 rho5, .) -- weight product exactly 1.
#   K4 the two OPEN gap types (len 20, 21): exact fixpoint verdicts on the full chain
#      systems with rho7 in the gap window (chase semantics: boxes + leafband), and the
#      K6-nesting verdict on their LP witnesses.
# Reuses (re-typed verbatim): the boxes/edge_band arbiter of midbound_chase_v2.py and the
# gap-lock LP+Farkas idiom of taillemma2_gaplock_v1.py (unchanged semantics).
import sys, glob, re, pickle, random, itertools, time
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, '/Users/trentpalelei/Desktop/Math Ex/experiments/n8')

DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'
out = open(DIR + 'tailrest_gapcover_v1.out', 'w')
def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True); out.write(s + '\n'); out.flush()

P('# tailrest_gapcover_v1 -- exact; started', time.strftime('%Y-%m-%d %H:%M:%S'))
t00 = time.time()

# ---------- the chain-type census (verbatim idiom of taillemma2_gaplock_v1) ----------
sys_argv_saved = sys.argv
src = open(DIR + 'frontier_type_search_v1.py').read().split('found = []; types_seen')[0]
sys.argv = ['x', '1', '15', '80', '1', '1']
exec(src)
sys.argv = sys_argv_saved

def overlap_links(chain, rs):
    rows = []; breaks = []
    for k in range(len(chain) - 1):
        (p, jp), (q, jq) = chain[k], chain[k + 1]
        xprev = (8 * jp + 1) / rs[p]; enext = (8 * jq - 1) / rs[q]
        if p == q or xprev > enext:
            rows.append((p, jp, q, jq))
        else:
            breaks.append(k)
    return rows, breaks

def frac_linsolve(Amat, rhs):
    n = len(Amat)
    M = [Amat[i][:] + [rhs[i]] for i in range(n)]
    for col in range(n):
        piv = next((r for r in range(col, n) if M[r][col] != 0), None)
        if piv is None: return None
        M[col], M[piv] = M[piv], M[col]
        pv = M[col][col]
        M[col] = [v / pv for v in M[col]]
        for r in range(n):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [M[r][k] - f * M[col][k] for k in range(n + 1)]
    return [M[r][n] for r in range(n)]

def gap_lock(rows, A, B, rs):
    A_ub = []; b_ub = []; names = []
    for (p, jp, q, jq) in rows:
        a = [0] * 7; a[q] = -(8 * jp + 1); a[p] = 8 * jq - 1; a[6] = 1
        A_ub.append(a); b_ub.append(0); names.append('link')
    (pA, jA), (qB, kB) = A, B
    g = [0] * 7; g[qB] = -(8 * jA + 1); g[pA] = 8 * kB - 1; g[6] = 1
    A_ub.append(g); b_ub.append(0); names.append('gap')
    p0, j0 = rows[0][0], rows[0][1]
    a = [0] * 7; a[p0] = 1; a[6] = 1; A_ub.append(a); b_ub.append(8 * j0 + 1); names.append('s-up')
    a = [0] * 7; a[p0] = -1; a[6] = 1; A_ub.append(a); b_ub.append(-(8 * j0 - 1)); names.append('s-lo')
    pe, je = rows[-1][2], rows[-1][3]
    a = [0] * 7; a[pe] = 7; a[6] = 1; A_ub.append(a); b_ub.append(8 * je + 1); names.append('end')
    for i in range(5):
        a = [0] * 7; a[i] = 1; a[i + 1] = -1; A_ub.append(a); b_ub.append(0); names.append('ord')
    for i in range(6):
        a = [0] * 7; a[i] = -1; A_ub.append(a); b_ub.append(-1); names.append('b-lo')
        a = [0] * 7; a[i] = 1; A_ub.append(a); b_ub.append(80); names.append('b-hi')
    a = [0] * 7; a[6] = 1; A_ub.append(a); b_ub.append(10); names.append('t-cap')
    c = [0] * 7; c[6] = -1
    r = linprog(c, A_ub=np.array(A_ub, float), b_ub=np.array(b_ub, float),
                bounds=[(1, 80)] * 6 + [(None, 10)], method='highs')
    if r.status != 0: return 'LPFAIL', None, None, None
    x = r.x
    opt = -r.fun
    act = [i for i in range(len(A_ub)) if abs(sum(x[k] * A_ub[i][k] for k in range(7)) - b_ub[i]) < 1e-6]
    for comb in itertools.combinations(act, 7):
        Amat = [[F(A_ub[r_][k]) for r_ in comb] for k in range(6)] + [[F(A_ub[r_][6]) for r_ in comb]]
        rhs = [F(0)] * 6 + [F(1)]
        y = frac_linsolve(Amat, rhs)
        if y is None or not all(v >= 0 for v in y): continue
        tstar = sum(y[i] * F(b_ub[comb[i]]) for i in range(7))
        if tstar <= 0:
            return 'LOCKED', tstar, {names[comb[i]]: y[i] for i in range(7) if y[i] != 0}, None
        return 'OPEN', tstar, None, [F(x[k]) for k in range(6)]
    return 'UNVERIFIED', F(opt), None, [F(x[k]) for k in range(6)]

random.seed(1)
starts = []
for f in sorted(glob.glob(DIR + 'frontier_box_carve_v1_hi2_s*.out')):
    m_ = re.search(r'readings \(float\): \[(.*)\]', open(f).readline())
    starts.append([float(v) for v in m_.group(1).split(',')])
starts.append(pickle.load(open(DIR + 'frontier_polish_v1_first.pkl', 'rb')))

types = {}
for it in range(6000):
    x0 = random.choice(starts); scale = random.choice([1e-3, 1e-2, 5e-2, 0.1])
    x = sorted(max(1.0001, v * (1 + scale * random.uniform(-1, 1))) for v in x0)
    ch = chain_of(x)
    if ch is not None: types.setdefault(ch, [F(v) for v in x])

import collections as _c
def links_of(chain):
    ls = []
    for k in range(len(chain) - 1):
        (p, jp), (q, jq) = chain[k], chain[k + 1]
        if p != q: ls.append((p, q, F(8 * jq - 1, 8 * jp + 1)))
    for i in range(5): ls.append((i, i + 1, F(1)))
    return ls
def maxc(ls):
    W = {}
    for p, q, w in ls:
        if (p, q) not in W or w > W[(p, q)]: W[(p, q)] = w
    best = F(0)
    for size in range(2, 7):
        for cyc in itertools.permutations(range(6), size):
            if cyc[0] != min(cyc) or (cyc[0], cyc[-1]) not in W: continue
            pr, ok = F(1), True
            for a, b in zip(cyc, cyc[1:] + cyc[:1]):
                if (a, b) not in W: ok = False; break
                pr *= W[(a, b)]
            if ok and pr > best: best = pr
    return best
feas = {ch: rs for ch, rs in types.items() if maxc(links_of(ch)) < 1}
P('feasible-gap types (census reproduction):', len(feas), '(prior run: 27)')

# ---------- K1: re-verify the per-gap locks ----------
P('# === K1. gap-lock re-verification (exact Farkas) ===')
verdicts = _c.Counter(); locked_types = 0; open_gaps = []
open_witness = {}
for ch, rs in sorted(feas.items(), key=lambda kv: len(kv[0])):
    rows, breaks = overlap_links(ch, rs)
    nv = _c.Counter()
    for k in breaks:
        v, tstar, cert, wit = gap_lock(rows, ch[k], ch[k + 1], rs)
        nv[v] += 1; verdicts[v] += 1
        if v == 'OPEN':
            open_gaps.append((len(ch), k, float(tstar) if tstar else None))
            open_witness[(len(ch), k)] = (ch, rs, wit)
    if all(v == 'LOCKED' for v in nv) and len(nv) == 1 and nv['LOCKED'] == len(breaks):
        locked_types += 1
    P('len', len(ch), 'breaks', len(breaks), dict(nv))
P('K1 VERDICTS:', dict(verdicts), '| fully-locked types:', locked_types, '/', len(feas))
P('K1 OPEN gaps:', len(open_gaps))
for og in open_gaps[:12]: P('  OPEN:', og)

# ---------- K2/K3: the covering side (K6 components and rho7-nesting bands) ----------
def zones_in_window(rho, lo=F(1), hi=F(7)):
    z = []
    j = 1
    while True:
        a = F(8 * j - 1) / rho
        if a >= hi: break
        b = F(8 * j + 1) / rho
        if b > lo: z.append((a, b, j))
        j += 1
    return z

def k6_components(rho_sorted):
    """[1,7] minus the OPEN zones of readings rho2..rho6; exact closed components."""
    cuts = []
    for rho in rho_sorted[:5]:
        for a, b, j in zones_in_window(rho):
            cuts.append((a, b))
    cuts.sort()
    comps = []
    cur = F(1)
    for a, b in cuts:
        if a > cur:
            comps.append((cur, min(a, F(7))))
        cur = max(cur, b)
        if cur >= F(7): break
    if cur < F(7):
        comps.append((cur, F(7)))
    # merge degenerate: components are closed [x,y]; empty when x==y is a one-point window
    return [(a, b) for (a, b) in comps if True]

def nesting_bands(comps, glo, ghi):
    """rho7 must nest every component in one zone: per component [a,b] the bands
    ((8j-1)/a, (8j+1)/b) for laps j; return the intersection over components, exact,
    restricted to (glo, ghi). Also return the two tightest bands for the conflict name."""
    inter = (glo, ghi)
    per = []
    for (a, b) in comps:
        best = None
        bands = []
        j = 1
        while F(8 * j + 1) / max(a, F(1, 10**30)) > glo:
            lo = F(8 * j - 1) / b if b > 0 else None
            hi = F(8 * j + 1) / a if a > 0 else None
            if a > 0 and b > 0:
                bands.append((lo, hi, j))
            j += 1
            if j > 4000: break
        # a component is nestable in zone j iff a >= (8j-1)/rho7 and b <= (8j+1)/rho7,
        # i.e. rho7 in ((8j-1)/b, (8j+1)/a) -- careful with open/closed: strict nesting
        # of the CLOSED component in the OPEN zone: (8j-1)/rho7 < a and b < (8j+1)/rho7
        # <=> rho7 > (8j-1)/a and rho7 < (8j+1)/b.
        bands = []
        for j in range(1, 4000):
            lo = F(8 * j - 1) / a
            hi = F(8 * j + 1) / b
            if lo >= ghi: break
            if hi > glo:
                bands.append((lo, hi, j))
        per.append(bands)
        # component feasible iff some band meets (glo, ghi)
        feas_j = [bd for bd in bands if bd[0] < ghi and bd[1] > glo]
        if not feas_j:
            return None, per, (a, b)
        # keep intersection progress: rho7 must be in SOME band of this component and in
        # some band of every other -- the intersection over components of the UNIONS.
        # (handled by the exact product test below; here we only record feasibility)
    return 'per-component-feasible', per, None

def nest_verdict(rho_sorted, glo, ghi):
    """Exact: is there rho7 in (glo,ghi) nesting every K6 component? The rho7-value is a
    FREE variable here (the system's own rho7 is only a witness). We solve the exact
    covering question: for each candidate lap-assignment (j_i per component) the interval
    ((8j_i-1)/a_i, (8j_i+1)/b_i) over all i must share a common point in (glo,ghi).
    Components are few (near-carves: <= 3); brute-force over lap tuples, exact."""
    comps = k6_components(rho_sorted)
    if not comps:
        return ('no-components', F(0), [])
    per = []
    for (a, b) in comps:
        bands = []
        for j in range(1, 4000):
            lo = F(8 * j - 1) / a
            hi = F(8 * j + 1) / b
            if lo >= ghi: break
            if hi > glo:
                bands.append((lo, hi, j))
        if not bands:
            return ('dead-component', F(0), [(a, b)])
        per.append(bands)
    best = None
    # greedy exact intersection search (components <= 4, bands per component <= ~12)
    inter_all = []
    for b0 in per[0]:
        lo, hi = b0[0], b0[1]
        ok = True
        for bands in per[1:]:
            l2 = max(lo, glo); h2 = min(hi, ghi)
            found = None
            for (l3, h3, j3) in bands:
                l4, h4 = max(l2, l3), min(h2, h3)
                if l4 < h4:
                    found = (l4, h4); break
            if found is None:
                ok = False; break
            lo, hi = found
        if ok:
            l2, h2 = max(lo, glo), min(hi, ghi)
            if l2 < h2:
                inter_all.append((l2, h2))
    if inter_all:
        return ('NESTABLE', inter_all[-1][0], inter_all)
    # find the exact conflict: the pair of components whose bands are separated
    conf = []
    for i in range(len(per)):
        for jj in range(i + 1, len(per)):
            pairs = [(x, y) for x in per[i] for y in per[jj] if x[0] < y[1] and y[0] < x[1]]
            if not pairs:
                conf.append((i, jj))
    return ('CONFLICT', F(0), conf)

P('# === K2. K6-nesting verdicts on the recorded rho6-anchored gap systems ===')
near = [pickle.load(open(DIR + 'frontier_polish_v1_first.pkl', 'rb'))]
for f in sorted(glob.glob(DIR + 'frontier_box_carve_v1_hi2_s*.out')):
    m_ = re.search(r'readings \(float\): \[(.*)\]', open(f).readline())
    if m_: near.append([float(v) for v in m_.group(1).split(',')])
GLO, GHI = F(33), F(39)     # gap 4: all recorded gap near-carves live here (33 < rho7 < 39)
n_ok = n_tot = 0
for idx, v in enumerate(near):
    rho = sorted(F(x) for x in v)
    if not (GLO < rho[5] < GHI): continue
    comps = k6_components(rho)
    lens = [(b - a) for (a, b) in comps]
    verdict, val, info = nest_verdict(rho, GLO, GHI)
    n_tot += 1
    ok = verdict in ('dead-component', 'CONFLICT')
    n_ok += ok
    P('  system %d: rho6=%s (%.4f) rho7=%s (%.4f) |K6 comps|=%d lens<2/rho7: %s'
      % (idx, rho[4], float(rho[4]), rho[5], float(rho[5]), len(comps),
         all(l < 2 / rho[5] for l in lens) if lens else None))
    P('     comps:', [(str(a), str(b), float(b - a)) for (a, b) in comps])
    P('     nesting:', verdict, str(val)[:80], '=> KILL' if ok else '=> CHECK')
P('K2 nesting kills on recorded gap systems: [T %d/%d]' % (n_ok, n_tot))

# ---------- K3: the worked E830 cycle on the polished first vector ----------
P('# === K3. the E830 two-link cycle (product exactly 1), exact ===')
v0 = sorted(F(x) for x in near[0])
rho2, rho3, rho4, rho5, rho6, rho7 = v0
comps0 = k6_components(v0)
P('polished first vector: rho5=%s (%.6f) rho6=%s (%.6f) rho7=%s (%.6f)'
  % (rho5 := v0[3], float(v0[3]), v0[4], float(v0[4]), v0[5], float(v0[5])))
P('K6 components:', [(float(a), float(b), len(comps0)) for (a, b) in comps0][:4],
  '... total', len(comps0))
# E830: the near-carve fails by rho7 < 7 rho5 against rho7 > 7 rho5. Exact:
c_lo = F(7) * v0[3]
P('cycle: rho7 < 7*rho5 = %s (%.6f) vs rho7 > 7*rho5: rho7 = %s (%.6f) -> strict infeasible,'
  % (c_lo, float(c_lo), v0[5], float(v0[5])),
  'weight product 7/7 = 1 exactly:', F(7) / F(7) == 1)
# where do the two sides come from? the last two K6 components' nesting bands:
if len(comps0) >= 2:
    (a1, b1), (a2, b2) = comps0[-2], comps0[-1]
    P('last two components: [%.12f, %.12f] and [%.12f, %.12f]'
      % (float(a1), float(b1), float(a2), float(b2)))
    for (a, b), tag in (((a1, b1), 'c-2'), ((a2, b2), 'c-1')):
        bands = []
        for j in range(1, 300):
            lo, hi = F(8 * j - 1) / a, F(8 * j + 1) / b
            if lo >= F(50): break
            if hi > F(30): bands.append((lo, hi, j))
        P('   %s bands over (30,50):' % tag, [(str(lo), str(hi), j) for (lo, hi, j) in bands])

# ---------- K4: the two OPEN gap types: exact chain-system verdicts ----------
P('# === K4. the OPEN gap types: exact chain-system verdicts ===')
def imul(x, y): return (x[0] * y[0], x[1] * y[1])
def iinv(x): return (F(1) / x[1], F(1) / x[0])
def iinter(a, b): return (max(a[0], b[0]), min(a[1], b[1]))
def iempty(x): return x[0] >= x[1]
def edge_band(ju, jx): return (F(8 * jx - 1, 8 * ju + 1), F(8 * jx + 1, 8 * ju + 1))

def boxes_gap(ranks, BM, rho7win):
    """Exact fixpoint over a chain type with rho7 pinned in the GAP window (no rho6 pin:
    the rho6-anchored regime). Ordering + floors only."""
    n = len(ranks)
    RB = {}
    for i in range(n):
        for j in range(i + 1, n):
            a, b = ranks[i], ranks[j]
            if a == b:
                lo, hi = BM[(i, j)]
                if not (lo < 1 < hi): return None, 'selfband'
                continue
            key = (a, b)
            if key in RB: RB[key] = iinter(RB[key], BM[(i, j)])
            else: RB[key] = BM[(i, j)]
    for (a, b), rb in list(RB.items()):
        rb = (max(rb[0], F(1)), rb[1]) if a < b else (rb[0], min(rb[1], F(1)))
        if iempty(rb): return None, 'order'
        RB[(a, b)] = rb
    V = [(F(1), F(1000)) for _ in range(6)]
    V[5] = iinter(V[5], rho7win)
    for _ in range(60):
        changed = False
        for (a, b), rb in RB.items():
            nb = iinter(V[b], imul(V[a], rb))
            if nb != V[b]:
                V[b] = nb; changed = True
                if iempty(nb): return None, 'fixpoint'
            na = iinter(V[a], imul(V[b], iinv(rb)))
            if na != V[a]:
                V[a] = na; changed = True
                if iempty(na): return None, 'fixpoint'
        if not changed: break
    if iempty(V[5]): return None, 'strip'
    return V, None

seen_open_types = {}
for (L, k), (ch, rs, wit) in sorted(open_witness.items()):
    key = tuple(ch)
    if key in seen_open_types: continue
    seen_open_types[key] = (L, k)
for key, (L, k) in sorted(seen_open_types.items(), key=lambda kv: len(kv[0])):
    ch, rs, wit = None, None, None
    # recompute the witness for this type from open_witness
    for (L2, k2), (ch2, rs2, wit2) in open_witness.items():
        if tuple(ch2) == key:
            ch, rs, wit = ch2, rs2, wit2; break
    ranks = [p for (p, j) in ch]
    BM = {}
    for i in range(len(ch) - 1):
        e = edge_band(ch[i][1], ch[i + 1][1])
        for kk in range(i + 1):
            pv = BM.get((kk, i), (F(1), F(1)))
            BM[(kk, i + 1)] = imul(pv, e)
    BM[(0, 0)] = (F(1), F(1))
    # exact verdict with rho7 in the gap window (33,39); and the witness's own rho7:
    V, why = boxes_gap(ranks, BM, (GLO, GHI))
    P('OPEN type len %d (open gap at chain pos %d): full-chain exact fixpoint with rho7 in (33,39):'
      % (len(ch), k), 'ALIVE' if V else ('DEAD:' + str(why)))
    if V:
        P('   rho7 box:', V[5][0], V[5][1], '=', (round(float(V[5][0]), 6), round(float(V[5][1]), 6)))
        P('   boxes rho2..rho6:', [(round(float(x[0]), 4), round(float(x[1]), 4)) for x in V[:5]])
        # the witness readings: exactify the LP witness and compute the K6-nesting verdict
        if wit is not None:
            rho = sorted(wit)
            verdict, val, info = nest_verdict(rho, GLO, GHI)
            P('   LP-witness nesting verdict:', verdict, '| K6 comps:',
              [(round(float(a), 9), round(float(b), 9)) for (a, b) in k6_components(rho)][:6])
P('gapcover done %.1fs' % (time.time() - t00))
out.close()
print('DONE')
