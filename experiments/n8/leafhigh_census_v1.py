# leafhigh_census_v1.py -- rule-22 census of the 3,765 uncertified D=64 leaves of the taildeep band
# rho7 in [95,97) (taildeep_leaves_95_97.txt, fixed-R0 certifier leftovers; first nonzero leaf count
# above [49,51)).  Reuses the leaves3739 / taildeep_leaf_cycles / outcome_classes machinery (read-only).
# Exact Fractions for every conclusion; floats steer only (LP margins), except where a separation
# bound makes float ordering provably exact (stated where used).
# Sections:
#  [0] inputs, heights (n7 histogram, sub-bands)
#  [1] reading-ratio clusters at centres (exact): rho7/rho5, rho7/rho6, rho6/rho5 distributions
#      + proximity to comb ratios (8*jq-1)/(8*jp+1) and small rationals
#  [2] exact greedy zone-chain at every leaf centre: chain census, covered/stuck, first-gap pairs
#  [3] exact common lonely set per leaf at D=64 (fixed-R0 datum): EMPTY/POINTONLY/POS classes
#  [4] corner-level first-gap census on a stratified subsample (exact Fractions) -> tie-plane
#      candidates (8*jq-1)*rho_p - (8*jp+1)*rho_q = 0; also margin LP per distinct chain (float steer)
#      with exact nullspace of tight binding rows (product-1 cycle candidates)
#  [5] derived + legacy planes: EXACT straddle/touch census over ALL 3,765 leaves by interval
#      arithmetic (integer) on the box; plane census = the tail-lemma data at this height
#  [6] exact cascade outcome at centres on a stratified sample (W_0 landing? carve?) + cascade check
# usage: python3 leafhigh_census_v1.py
import os, sys, collections, itertools, time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
IN = os.path.join(HERE, 'taildeep_leaves_95_97.txt')
RN = ['rho2', 'rho3', 'rho4', 'rho5', 'rho6', 'rho7']

leaves = []
for l in open(IN):
    v = [int(x) for x in l.split()]
    if len(v) == 7: leaves.append((v[0], tuple(v[1:])))
N = len(leaves)

O = open(os.path.join(HERE, 'leafhigh_census_v1.out'), 'w')
def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s); O.write(s + '\n')

def zones_of(rho, lo=F(1), hi=F(7)):
    z = []
    j = 1
    while True:
        a = F(8 * j - 1) / rho
        if a >= hi: break
        b = F(8 * j + 1) / rho
        if b > lo: z.append((a, b, j))
        j += 1
    return z

def greedy_chain(rhos):
    # exact greedy monotone cover of [1,7]; returns (chain, covered, first-gap).
    # first-gap = ((p,jp),(q,jq)): p = reading whose zone exit bounds the gap left ((8jp+1)/rho_p),
    # q = reading whose zone entry bounds it right ((8jq-1)/rho_q); ends (('1',None)/(('7',None)).
    z = []
    for i, r in enumerate(rhos):
        for a, b, j in zones_of(r):
            z.append((a, b, i + 2, j))
    z.sort(key=lambda t: (t[0], -t[1]))
    cur = F(1); curd = (1, None); chain = []
    for a, b, i, j in z:
        if a > cur:
            return chain, False, (curd, (i, j))
        if b > cur:
            cur = b; curd = (i, j); chain.append((i, j))
            if cur >= 7: break
    if cur < 7: return chain, False, (curd, (7, None))
    return chain, True, None

def lonely_set(D, n):
    # t in [1,7] lonely for EVERY arrangement of the box (leaves3739_mech_v1 verbatim)
    cur = [(F(1), F(7))]
    hist = []
    for i in range(6):
        ivs = []
        j = 0
        while True:
            lo = F((8 * j + 1) * D, n[i]); hi = F((8 * j + 7) * D, n[i] + 1)
            if lo > 7: break
            if hi >= 1: ivs.append((max(lo, F(1)), min(hi, F(7))))
            j += 1
        nxt = []
        for a, b in cur:
            for lo, hi in ivs:
                c, d = (a if a > lo else lo), (b if b < hi else hi)
                if c <= d: nxt.append((c, d))
        nxt.sort()
        m = []
        for c, d in nxt:
            if m and c <= m[-1][1]:
                if d > m[-1][1]: m[-1] = (m[-1][0], d)
            else: m.append((c, d))
        hist.append((i, cur, m, ivs))
        cur = m
        if not cur: return [], hist
    return cur, hist

def comb_planes_near(num, den, lo, hi, jpmax=200):
    # comb ratios (8*jq-1)/(8*jp+1) in [lo,hi] (exact F endpoints); returns (ratio, jq, jp) list
    out = []
    for jp in range(0, jpmax):
        base = 8 * jp + 1
        jlo = (lo * base + 1) // 8 if not (lo * base + 1).denominator == 1 else -(-(lo * base + 1) // 8)
        jlo = max(1, -(-((lo * base + 1)) // 8))
        jhi = -((-(hi * base + 1)) // 8)
        for jq in range(int(jlo), int(jhi) + 1):
            r = F(8 * jq - 1, base)
            if lo <= r <= hi: out.append((r, jp, jq))
    return out

t0 = time.time()
P('== leafhigh_census_v1: rule-22 census of the 3,765 D=64 leaves, band rho7 in [95,97) ==')
P('[0] inputs:', IN)
Ds = collections.Counter(D for D, _ in leaves)
P('    leaves', N, '| D values', dict(Ds))
n7c = collections.Counter(n[5] for _, n in leaves)
P('    rho7 heights: n7 in [%d, %d] (%d distinct values, all 128 grid lanes present: %s)' % (
    min(n7c), max(n7c), len(n7c), len(n7c) == 128))
P('    leaves per n7: min %d max %d mean %.2f' % (min(n7c.values()), max(n7c.values()), N / len(n7c)))
lo = sum(1 for _, n in leaves if n[5] < 64 * 96)
P('    sub-band [95,96): %d leaves | [96,97): %d leaves' % (lo, N - lo))
nmin = [min(n[i] for _, n in leaves) for i in range(6)]
nmax = [max(n[i] for _, n in leaves) for i in range(6)]
P('    n2..n7 ranges:', list(zip(nmin, nmax)))

# ---- [1] reading-ratio clusters at centres (exact)
P('')
P('[1] reading-ratio clusters at centres (exact Fractions; ratio distribution over leaves):')
CENT = lambda n: tuple(F(2 * n[i] + 1, 2 * 64) for i in range(6))
rat = {}
for nm, (i, k) in [('rho7/rho5', (5, 3)), ('rho7/rho6', (5, 4)), ('rho6/rho5', (4, 3))]:
    vals = sorted(CENT(n)[i] / CENT(n)[k] for _, n in leaves)
    rat[nm] = vals
    P('    %s: min %s = %.6f | max %s = %.6f | distinct %d' % (nm, vals[0], float(vals[0]), vals[-1], float(vals[-1]), len(set(vals))))
    # histogram in 1/64-wide bins (float steering for the display only)
    h = collections.Counter(int(float(v) * 64) for v in vals)
    P('      bins (1/64 of the ratio):', sorted((b / 64, c) for b, c in h.items())[:14], '...' if len(h) > 14 else '')
# comb-ratio proximity: which comb ratios (8jq-1)/(8jp+1) lie inside each observed ratio range
P('    comb ratios (8*jq-1)/(8*jp+1) inside the observed centre-ratio range (candidate tie ratios):')
for nm, (i, k) in [('rho7/rho5', (5, 3)), ('rho7/rho6', (5, 4)), ('rho6/rho5', (4, 3))]:
    lo_v, hi_v = F(rat[nm][0]), F(rat[nm][-1])
    cps = comb_planes_near(None, None, lo_v, hi_v, jpmax=120)
    cps.sort()
    P('      %s in [%.6f, %.6f]: %d comb ratios; nearest to the median:' % (nm, float(lo_v), float(hi_v), len(cps)))
    med = rat[nm][N // 2]
    if cps:
        near = sorted(cps, key=lambda t: abs(t[0] - med))[:6]
        for r, jp, jq in near:
            P('        %s = %.6f  (jp=%d lap of rho_p, jq=%d)  |plane %d*rho_p - %d*rho_q|  dist to median %s = %.2e'
              % (r, float(r), jp, jq, 8 * jq - 1, 8 * jp + 1, med, float(abs(r - med))))
    sm = [F(17), F(14), F(55, 4), F(89, 5), F(137, 8), F(27, 2), F(83, 6)]
    inr = [s for s in sm if lo_v <= s <= hi_v]
    P('      small rationals inside range:', [str(s) for s in inr])

# ---- [2] exact greedy chain at every leaf centre
P('')
P('[2] exact greedy zone-chain at all %d leaf centres:' % N)
chc = collections.Counter(); gapc = collections.Counter(); ncov = 0
cent_chains = {}
for D, n in leaves:
    c = CENT(n)
    ch, cov, gap = greedy_chain(c)
    key = (tuple(ch), cov)
    cent_chains[(D, n)] = (ch, cov, gap)
    chc[key] += 1
    gapc[gap] += 1
    ncov += cov
P('    distinct centre chains: %d | centres where greedy covers [1,7]: %d | stuck: %d' % (len(chc), ncov, N - ncov))
P('    chain lengths: min %d max %d' % (min(len(ch) for ch, cov in chc), max(len(ch) for ch, cov in chc)))
P('    first-gap pair census at centres (top 12):')
for gap, c in gapc.most_common(12):
    (pd, qd) = gap
    if qd != (7, None) and pd[1] is not None:
        (p, jp), (q, jq) = pd, qd
        P('      gap exit rho%d lap %d -> entry rho%d lap %d | centres %d | implied plane %d*rho_%d - %d*rho_%d = 0 (rho_q/rho_p = %s = %.6f)'
          % (p, jp, q, jq, c, 8 * jq - 1, p, 8 * jp + 1, q, F(8 * jq - 1, 8 * jp + 1), float(F(8 * jq - 1, 8 * jp + 1))))
    elif qd == (7, None) and pd[1] is not None:
        (p, jp), _ = pd, qd
        P('      gap exit rho%d lap %d -> 7 | centres %d' % (p, jp, c))
    else:
        P('      gap 1 -> entry %s | centres %d' % (qd, c))
P('    most common centre chains (top 6):')
for (ch, cov), c in chc.most_common(6):
    P('      %s chain len %d | centres %d | %s' % ('COVER' if cov else 'stuck', len(ch), c, ch[:10]))

# ---- [3] exact common lonely set per leaf at D=64 (the fixed-R0 datum)
P('')
P('[3] exact common lonely set per leaf at D=64 (fixed-R0 semantics; leaves3739 method):')
cls = collections.Counter(); wmin = None; wmax = F(0); ptex = []
for D, n in leaves:
    ls, hist = lonely_set(D, n)
    pos = [iv for iv in ls if iv[0] < iv[1]]
    pts = [iv[0] for iv in ls if iv[0] == iv[1]]
    if not ls: k = 'EMPTY'
    elif not pos: k = 'POINTONLY'
    elif pts: k = 'HASPOINT'
    else: k = 'POS'
    cls[k] += 1
    if pos:
        w = max(b - a for a, b in pos)
        wmin = w if wmin is None else min(wmin, w); wmax = max(wmax, w)
    if pts: ptex.append((D, n, pts))
P('    classes:', dict(cls), '| max positive-window width seen:', wmax,
  '| min positive-window width:', wmin)
P('    leaves with >=1 isolated lonely point: %d (first 6):' % len(ptex))
for D, n, pts in ptex[:6]:
    P('      n =', n, '| points:', [str(t) for t in pts[:4]])
if cls.get('EMPTY', 0) or cls.get('POINTONLY', 0):
    # kill diagnostic on a few
    shown = 0
    for D, n in leaves:
        ls, hist = lonely_set(D, n)
        if ls: continue
        i_kill = None
        for step in range(6):
            i, prev, cur, ivs = hist[step]
            if not cur and i_kill is None: i_kill = step
        i, prev, cur, ivs = hist[i_kill]
        rows = []
        for a, b in prev:
            cands = []
            for lo2, hi2 in ivs:
                if hi2 < a: cands.append((a - hi2, 'late', lo2, hi2))
                elif lo2 > b: cands.append((lo2 - b, 'early', lo2, hi2))
            if cands: rows.append(min(cands))
        rows.sort(key=lambda r: r[0])
        a, b, delta, kind, lo2, hi2 = rows[0]
        P('      EMPTY example n =', n, '| last surviving t-range [%s, %s] killed by reading %s gap [%s, %s] (%s by exact %s)'
          % (a, b, RN[i], lo2, hi2, kind, delta))
        shown += 1
        if shown >= 4: break

# ---- [4] corner-level first-gap census on a stratified subsample + margin LP
P('')
P('[4] corner-level first-gap census (all 64 corners) on a stratified subsample (every 9th leaf, n7-sorted), exact Fractions:')
sub = sorted(leaves, key=lambda t: t[1][5])[::9]
P('    subsample:', len(sub), 'leaves =', 64 * len(sub), 'corners')
cgap = collections.Counter(); cgapw = {}; cnocov = 0; cchain = collections.Counter()
for D, n in sub:
    box = [(F(n[i], 64), F(n[i] + 1, 64)) for i in range(6)]
    seen = {}
    for bits in itertools.product([0, 1], repeat=6):
        rhos = [box[i][bits[i]] for i in range(6)]
        ch, cov, gap = greedy_chain(rhos)
        if not cov:
            cnocov += 1
            w = None
            if gap[1] != (7, None) and gap[0][1] is not None:
                (p, jp), (q, jq) = gap
                w = F(8 * jq - 1) / rhos[q - 2] - F(8 * jp + 1) / rhos[p - 2]
            elif gap[1] == (7, None) and gap[0][1] is not None:
                (p, jp), _ = gap
                w = F(7) - F(8 * jp + 1) / rhos[p - 2]
            elif gap[0][1] is None:
                (q, jq) = gap[1]
                w = F(8 * jq - 1) / rhos[q - 2] - F(1)
            if w is not None:
                cgap[gap] += 1
                gw = cgapw.setdefault(gap, [w, w]); gw[0] = min(gw[0], w); gw[1] = max(gw[1], w)
        k = (tuple(ch), cov)
        seen[k] = seen.get(k, 0) + 1
    for k, v in seen.items(): cchain[k] += v
P('    uncovered corners: %d of %d' % (cnocov, 64 * len(sub)))
P('    first-gap pair census at corners (top 14):')
for gap, c in cgap.most_common(14):
    (pd, qd) = gap
    w = cgapw[gap]
    if qd != (7, None) and pd[1] is not None:
        (p, jp), (q, jq) = pd, qd
        P('      exit rho%d lap %d -> entry rho%d lap %d | corners %d | gap width in [%s = %.3e, %s = %.3e] | plane %d*rho_%d - %d*rho_%d = 0 (ratio %s = %.6f)'
          % (p, jp, q, jq, c, w[0], float(w[0]), w[1], float(w[1]), 8 * jq - 1, p, 8 * jp + 1, q,
             F(8 * jq - 1, 8 * jp + 1), float(F(8 * jq - 1, 8 * jp + 1))))
    elif qd == (7, None) and pd[1] is not None:
        (p, jp), _ = pd, qd
        P('      exit rho%d lap %d -> 7 | corners %d | width in [%.3e, %.3e]' % (p, jp, c, float(w[0]), float(w[1])))
    else:
        P('      gap 1 -> entry %s | corners %d | width in [%.3e, %.3e]' % (qd, c, float(w[0]), float(w[1])))
P('    distinct corner chains: %d | top 4:' % len(cchain))
for (ch, cov), c in cchain.most_common(4):
    P('      %s len %d | corners %d | %s' % ('COVER' if cov else 'stuck', len(ch), c, ch[:10]))

# margin LP per distinct chain on the subsample (float HiGHS, steering only) -> tight links -> nullspace
P('')
P('    margin LP (float HiGHS, steering only) per distinct chain per subsample leaf:')
try:
    import numpy as np
    from scipy.optimize import linprog
    HAVE_LP = True
except Exception:
    HAVE_LP = False
    P('    (scipy unavailable -- LP skipped)')
if HAVE_LP:
    def lp_margin(box, chain, covered):
        A_ub = []; b_ub = []
        def hard(coeffs, rhs):
            A_ub.append([float(c) for c in coeffs] + [0.0]); b_ub.append(float(rhs))
        for i in range(6):
            lo_r = [F(0)] * 6; lo_r[i] = F(-1); hard(lo_r, -box[i][0])
            hi_r = [F(0)] * 6; hi_r[i] = F(1);  hard(hi_r, box[i][1])
        for i in range(5):
            c = [F(0)] * 6; c[i] = F(1); c[i + 1] = F(-1); hard(c, F(0))
        (i0, j0), (i1, j1) = chain[0], chain[-1]
        c = [F(0)] * 6; c[i0 - 2] = F(-1); hard(c, F(-(8 * j0 - 1)))
        if covered:
            c = [F(0)] * 6; c[i1 - 2] = F(7);  hard(c, F(8 * j1 + 1))
        links = []
        for (p, jp), (q, jq) in zip(chain, chain[1:]):
            c = [F(0)] * 6; c[q - 2] = F(-(8 * jp + 1)); c[p - 2] = F(8 * jq - 1)
            A_ub.append([float(x) for x in c] + [1.0]); b_ub.append(0.0)
            links.append(((p, jp), (q, jq)))
        bounds = [(float(box[i][0]), float(box[i][1])) for i in range(6)] + [(None, None)]
        r = linprog([0.0] * 6 + [-1.0], A_ub=A_ub, b_ub=b_ub, bounds=bounds, method='highs')
        if not r.success: return None, None, None
        t = r.x[-1]; x = r.x[:6]
        tight = []
        for k, ((p, jp), (q, jq)) in enumerate(links):
            slack = (8 * jp + 1) * x[q - 2] - (8 * jq - 1) * x[p - 2]
            if slack <= t + 1e-9: tight.append(((p, jp), (q, jq)))
        return t, x, tight
    cycle_hits = collections.Counter()
    tmin_all = None; tmax_all = None
    for D, n in sub:
        box = [(F(n[i], 64), F(n[i] + 1, 64)) for i in range(6)]
        seen = {}
        for bits in itertools.product([0, 1], repeat=6):
            rhos = [box[i][bits[i]] for i in range(6)]
            ch, cov, gap = greedy_chain(rhos)
            k = (tuple(ch), cov); seen[k] = seen.get(k, 0) + 1
        for (ch, cov) in seen:
            t, x, tight = lp_margin(box, ch, cov)
            if t is None: continue
            tmin_all = t if tmin_all is None else min(tmin_all, t)
            tmax_all = t if tmax_all is None else max(tmax_all, t)
            if t <= 1e-9 and tight: cycle_hits[tuple(sorted(tight))] += 1
    P('    LP margin t* over subsample leaves/chains: min %.3e max %.3e' % (tmin_all, tmax_all))
    P('    margin-zero (t* <= 1e-9) tight-link sets (product-1 cycle candidates): %d distinct' % len(cycle_hits))
    try:
        import sympy as sp
        def row_of(link):
            (p, jp), (q, jq) = link
            row = [0] * 6
            row[q - 2] += -(8 * jp + 1); row[p - 2] += (8 * jq - 1)
            return row
        for key, c in cycle_hits.most_common(8):
            rws = [row_of(l) for l in key]
            ns = sp.Matrix(rws).T.nullspace() if rws else []
            P('      links %s | leaf-corners hits %d | exact nullspace: %s' % (key, c, [list(v) for v in ns]))
    except Exception as e:
        P('      (sympy unavailable:', e, ')')

# ---- [5] derived + legacy planes: exact straddle/touch census over ALL leaves
P('')
P('[5] plane census at this height -- EXACT straddle/touch over all %d leaves (interval arithmetic on the box; integers):' % N)
LEGACY = [('P1: 7rho5-9rho4', (0, 0, -9, 7, 0, 0)), ('P2: rho7-7rho6', (0, 0, 0, 0, -7, 1)),
          ('w1: 23rho7-137rho5', (0, 0, 0, -137, 0, 23)), ('w2: 25rho7-135rho6', (0, 0, 0, 0, -135, 25)),
          ('h1: rho7-7rho5', (0, 0, 0, -7, 0, 1)), ('h2: 3rho6-5rho4', (0, 0, -5, 0, 3, 0)),
          ('h3: 25rho7-89rho5', (0, 0, 0, -89, 0, 25))]
# derived planes from the corner first-gap census (top pairs) and centre census
derived = []
for gap, c in cgap.most_common(20):
    (pd, qd) = gap
    if qd != (7, None) and pd[1] is not None:
        (p, jp), (q, jq) = pd, qd
        h = [0] * 6; h[p - 2] = 8 * jq - 1; h[q - 2] = -(8 * jp + 1)
        derived.append(('%d*rho%d-%d*rho%d' % (8 * jq - 1, p, 8 * jp + 1, q), tuple(h)))
seen_h = set()
PLANES = []
for nm, h in LEGACY + derived:
    if h in seen_h: continue
    seen_h.add(h); PLANES.append((nm, h))
def straddle_census(planes):
    out = []
    for nm, h in planes:
        st = 0; tc = 0
        for D, n in leaves:
            # h(rho) over box: min/max by sign of coefficients (exact integers)
            lo_v = sum(h[i] * (n[i] if h[i] >= 0 else n[i] + 1) for i in range(6))
            hi_v = sum(h[i] * (n[i] + 1 if h[i] >= 0 else n[i]) for i in range(6))
            if lo_v < 0 < hi_v: st += 1
            elif lo_v == 0 or hi_v == 0: tc += 1
        out.append((nm, st, tc))
    return out
res = straddle_census(PLANES)
strtot = 0
for nm, st, tc in res:
    P('    %-22s straddled by %5d leaves | touched (min=0 or max=0) by %5d' % (nm, st, tc))
    strtot += st
P('    legacy planes straddling:', sum(st for nm, st, tc in res if nm in [a for a, _ in LEGACY]))

# ---- [6] exact cascade outcome at centres on a stratified sample (W_0 landing?)
P('')
P('[6] exact cascade outcome at leaf centres (outcome_classes_v2, Fractions), stratified sample (every 19th leaf):')
HERE_SAVE = os.getcwd()
os.chdir('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/')
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
os.chdir(HERE_SAVE)
def carves(rs):
    iv = []
    for r in rs:
        for j in range(1, int(7 * r / 8) + 3):
            a, b = F(8 * j - 1) / r, F(8 * j + 1) / r
            if b > 1 and a < 7: iv.append((a, b))
    if not any(a < 1 < b for a, b in iv): return False
    cur = max(b for a, b in iv if a < 1)
    while cur <= 7:
        nxt = [b for a, b in iv if a < cur and b > cur]
        if not nxt: return False
        cur = max(nxt)
    return True
samp = sorted(leaves, key=lambda t: (t[1][5], t[1]))[::19]
win = collections.Counter(); nc = 0; mx = F(0); nmv = collections.Counter()
for D, n in samp:
    x = sorted(CENT(n))
    o = outcome([F(1)] + x); win[int((o['R'] - 1) // 8)] += 1; mx = max(mx, o['R'])
    nmv[o['nmoves']] += 1
    if carves(x): nc += 1
P('    sample', len(samp), 'centres | cascade landing window counts (W_k):', sorted(win.items()),
  '| largest landing R (exact):', mx)
P('    cascade move counts:', sorted(nmv.items()), '| exact carves among centres:', nc)
P('    W_0 = landing window 0 (R in [1,9) after normalising by the smallest reading): centres landing W_0:',
  win.get(0, 0), 'of', len(samp))
o0 = outcome([F(1)] + sorted(CENT(leaves[0][1])))
P('    first leaf centre outcome example: R =', o0['R'], '| opener', o0['opener'], '| closer', o0['closer'],
  '| lap vector', o0['lap'], '| moves', o0['nmoves'])

P('')
P('done census in %.1f s' % (time.time() - t0))
O.close()
