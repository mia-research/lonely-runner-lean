# conjT_cover_check_v1.py -- Conjecture T via the covering side: exact case analysis.  v2
# Exact arithmetic (Fractions) for every verdict; float literals only steer the synthetic probe.
# Parts:
#  P1 comb clauses (exact): strips vs (1,7]; end windows W_k; the task-sketch corrections
#     (rho6>7 CAN cover R=7; strips vs gaps off-pin); the strip-top end gap; front-closure bands.
#  P2 the FRONT-CLOSURE LEMMA (pin-free) + the off-pin zone-2 option tables (exact thresholds).
#  P3 population calibration [T n/N] on the 96 recorded carves + 9 near-carves,
#     INCLUDING the negative control of the K6-nesting instrument on the 96 real carves.
#  P4 K6-component / rho7-nesting probes on every near-carve system (exact): own window,
#     (25,50), and (25,130) -- the last composes with E852 (rho6<=17, rho7>=50) to all rho7>=25.
#  P5 case-A synthetic probe with front-band negative controls (floats steer; exact verdicts).
from fractions import Fraction as F
import pickle, glob, re, sys, time

DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'
sys.path.insert(0, DIR)
from taillemma_lib_v1 import zones_of, greedy_chain

out = open(DIR + 'conjT_cover_check_v1.out', 'w')
def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True); out.write(s + '\n'); out.flush()

P('# conjT_cover_check_v1 (v2) -- exact (Fractions); started', time.strftime('%Y-%m-%d %H:%M:%S'))

PIN = F(49, 7)   # = 7

def regime(rho):
    """returns (kind, m) with kind in {'strip','gap'} or (None, None)."""
    for m in range(1, 80):
        if F(8 * m - 1) < rho < F(8 * m + 1): return ('strip', m)
        if F(8 * m + 1) < rho < F(8 * m + 7): return ('gap', m)
    return (None, None)

def coverers_of_R(R, rho, jmax=500):
    X = R * rho; res = []; j = 1
    while F(8 * j - 1) < X:
        if F(8 * j - 1) < X < F(8 * j + 1): res.append(j)
        j += 1
        if j > jmax: break
    return res

# ================= P1: comb clauses =================
P('# === P1. comb clauses (exact) ===')
meets = [j for j in range(1, 40) if F(8 * j - 1) < F(7) and F(8 * j + 1) > F(1)]
P('(a) strips C_j meeting (1,7]:', meets, '-> EMPTY' if not meets else 'FAIL')

P('(b) end windows W_k (a reading covers R=7 at lap k iff it lies in W_k):')
for k in range(1, 17):
    lo, hi = F(8 * k - 1, 7), F(8 * k + 1, 7)
    klo, mlo = regime(lo); khi, mhi = regime(hi)
    if klo and klo == khi: cell = 'inside %s %d' % (klo, mlo)
    elif klo and khi and (klo, mlo) != (khi, mhi): cell = 'spans %s%d boundary to %s%d' % (klo, mlo, khi, mhi)
    else: cell = 'edge case'
    tag = 'in (7,17]' if hi > F(7) and lo < F(17) else ('<=7 side' if hi <= F(7) else 'above 17')
    P('    W_%-2d = (%.5f, %.5f)  %-28s %s' % (k, float(lo), float(hi), cell, tag))

w7lo, w7hi = F(55, 7), F(57, 7)
P('(c1) SKETCH CORRECTION 1: rho6 > 7 CAN cover R=7 (and R=1): (55/7, 57/7) = (%.5f, %.5f):' % (float(w7lo), float(w7hi)))
P('     subset (7,9):', F(7) < w7lo and w7hi < F(9),
  '| covers R=1 at lap 1 (rho in C_1):', F(7) < w7lo,
  '| covers R=7 at lap 7 (7rho in (55,57)):', F(7) * w7lo > F(55) and F(7) * w7hi < F(57))

ok = True
for j in range(1, 30):
    for k in range(1, 250):
        hit = (F(8 * k - 1) < F(56 * j + 7) and F(8 * k + 1) > F(56 * j - 7))
        if hit != (k == 7 * j): ok = False
P('(c2) a reading in strip C_j covers R=7 only possibly at lap 7j:', ok)

ok = True
for m in range(1, 40):
    lo, hi = F(8 * m) + F(1, 7), F(8 * m + 1)
    Xlo, Xhi = F(7) * lo, F(7) * hi   # (56m+1, 56m+7)
    for k in range(1, 300):
        if F(8 * k - 1) < Xhi and F(8 * k + 1) > Xlo: ok = False
P('(c3) SKETCH CORRECTION 2 (sharp form): rho in (8m+1/7, 8m+1) covers R=7 at NO lap (any m):', ok)

P('(d) front-closure thresholds g_k(m) = (8k-1)(8m-1)/(8m+1) (band-k lower edge at rho7 = 8m-1):')
for m in range(4, 13):
    row = ['%s' % (F(8 * k - 1) * F(8 * m - 1, 8 * m + 1)) for k in range(1, 7)]
    P('     m=%-2d %s' % (m, '  '.join('%-9s' % r for r in row)))

# ================= P2: the FRONT-CLOSURE LEMMA (pin-free) + zone-2 tables =================
P('# === P2. front-closure lemma (pin-free) and off-pin zone-2 options ===')
P('LEMMA (front closure, pin-free). In any carve the anchor zone Z(a0,k0) containing R=1 has exit')
P('  x0 = (8k0+1)/rho_{a0}; x0 is covered by NO zone of a0 (zones of one reading are disjoint with')
P('  gap exactly 6/rho, and x0 is the anchor exit), so SOME other reading strictly covers x0:')
P('  exists rho != a0, lap k: (8k-1) rho_{a0}/(8k0+1) < rho < (8k+1) rho_{a0}/(8k0+1).')
P('  Hence rho6 > 7 rho_{a0}/(8k0+1) ALWAYS.')
P('  - self-anchored (a0 = rho7 in C_m, k0 = m): rho6 > 7 rho7/(8m+1)   [the front pin, pin-free].')
P('  - strip-1-anchored (a0 = rho_s in C_1, k0 = 1): some reading lies in')
P('    union_j ((8j-1) rho_s/9, (8j+1) rho_s/9); smalls can only serve j=1 (band (7rho_s/9, rho_s))')
P('    or j>=2 with rho > (15/9) rho_s > 11.67; otherwise rho7 serves via its sliver band.')
P('Case-A (no small in any strip) strip-free band parts: k=1: (7 rho7/(8m+1), 7];')
P('  k >= 2: ((8k-1) rho7/(8m+1), 8k-1] (lower sliver inside gap G_{k-1}).')
P('Off-pin zone-2 options, middle branch (Theorem S: rho6 in (7,17], rho7 in [25,50)):')
P('  case A (self-anchored): rho6 in (9,15] u {17} (strips (7,9),(15,17) excluded):')
P('    zone 2 = lap-1 of a small in (7 rho7/(8m+1), 7]  OR  lap-k (k>=2) with a small in')
P('    ((8k-1) rho7/(8m+1), 8k-1], in particular lap-2 needs rho6 > g_2(m) = 15(8m-1)/(8m+1):')
for m in range(4, 7):
    g2 = F(15) * F(8 * m - 1, 8 * m + 1); g3 = F(23) * F(8 * m - 1, 8 * m + 1)
    P('    m=%d: g_2 = %s = %.5f (so lap-2 front needs rho6 > g_2, <= 15); g_3 = %.5f %s' %
      (m, g2, float(g2), float(g3), '(lap-3 live only above 17: V3)' if g3 > F(17) else ''))
P('  B2 (strip-1 small a0 = rho_s): zone 2 = lap-1 of a reading in (7 rho_s/9, rho_s), or')
P('    lap-j (j>=2) of a reading > (8j-1) rho_s/9, or rho7 via the sliver band. The pinned')
P('    front-pin floor f(m) < 7 < rho6 is AUTOMATIC off-pin (no transport from the front side).')
P('  COROLLARY (case-A front kill): rho7 in C_m, no small in any strip, no small in')
P('    (7 rho7/(8m+1), 7] and rho6 < 15 rho7/(8m+1)  =>  NO CARVE (the anchor seam x0 is uncovered).')

# ================= P3: population calibration =================
P('# === P3. population calibration [T n/N] ===')
vecs = {2: [], 3: []}
for k in (2, 3):
    for f in sorted(glob.glob(DIR + 'frontier_band_carve_v1_k%d_s*.pkl' % k)):
        vecs[k] += pickle.load(open(f, 'rb'))
for f in sorted(glob.glob(DIR + 'frontier_box_carve_v1_23_25_s*.pkl')):
    vecs[3] += pickle.load(open(f, 'rb'))
near = []
try:
    near.append(pickle.load(open(DIR + 'frontier_polish_v1_first.pkl', 'rb')))
except Exception as e:
    P('polish load failed:', e)
for f in sorted(glob.glob(DIR + 'frontier_box_carve_v1_hi2_s*.out')):
    m_ = re.search(r'readings \(float\): \[(.*)\]', open(f).readline())
    if m_: near.append([float(v) for v in m_.group(1).split(',')])
N = len(vecs[2]) + len(vecs[3])
P('carves: strip2 %d strip3 %d total %d | near-carves: %d' % (len(vecs[2]), len(vecs[3]), N, len(near)))

def k6_components(rho_small):
    ivs = []
    for r in rho_small:
        for a, b, j in zones_of(r):
            a2, b2 = max(a, F(1)), min(b, F(7))
            if a2 < b2: ivs.append((a2, b2))
    ivs.sort()
    merged = []
    for a, b in ivs:
        if merged and a <= merged[-1][1]: merged[-1][1] = max(merged[-1][1], b)
        else: merged.append([a, b])
    comps, cur = [], F(1)
    for a, b in merged:
        if a > cur: comps.append((cur, a))
        cur = max(cur, b)
    if cur < F(7): comps.append((cur, F(7)))
    return comps

def feasible_set(a, b, rlo, rhi, jmax=800):
    ivs = []
    j = 1
    while True:
        lo, hi = F(8 * j - 1, a), F(8 * j + 1, b)
        if lo >= rhi: break
        if hi > rlo and hi > lo: ivs.append((max(lo, rlo), min(hi, rhi)))
        j += 1
        if j > jmax: break
    ivs.sort()
    merged = []
    for lo, hi in ivs:
        if lo >= hi: continue
        if merged and lo <= merged[-1][1]: merged[-1][1] = max(merged[-1][1], hi)
        else: merged.append([lo, hi])
    return merged

def intersect(f1, f2):
    res = []
    for lo1, hi1 in f1:
        for lo2, hi2 in f2:
            lo, hi = max(lo1, lo2), min(hi1, hi2)
            if lo < hi: res.append((lo, hi))
    res.sort()
    merged = []
    for lo, hi in res:
        if merged and lo <= merged[-1][1]: merged[-1][1] = max(merged[-1][1], hi)
        else: merged.append([lo, hi])
    return merged

def probe(rho_small, win):
    comps = k6_components(rho_small)
    fs = [feasible_set(a, b, win[0], win[1]) for (a, b) in comps]
    cur = fs[0] if fs else []
    for f2 in fs[1:]: cur = intersect(cur, f2)
    return comps, intersect(cur, [win])

n_pin = n_self = n_anchor = n_start = n_front = n_cov = n_gap7 = n_touch = 0
n_neg = 0
for kk in (2, 3):
    for v in vecs[kk]:
        rho = sorted(F(x) for x in v)
        r6, r7 = rho[4], rho[5]
        rg, m = regime(r7)
        n_pin += r6 <= PIN
        n_self += (rg == 'strip')
        anch = []
        for i, r in enumerate(rho):
            for j in coverers_of_R(F(1), r): anch.append((i + 2, j))
        n_anchor += (anch == [(7, m)])
        ch, cov = greedy_chain(rho)
        n_cov += bool(cov)
        n_start += bool(ch) and (ch[0][0] + 2, ch[0][1]) == (7, m)
        n_front += r6 > F(7) * r7 / F(8 * m + 1)
        n_gap7 += F(8 * m) + F(1, 7) < r7 < F(8 * m + 1)
        if bool(ch) and cov and len(ch) >= 2:
            z = {}
            for i, r in enumerate(rho):
                for a, b, j in zones_of(r): z[(i, j)] = (a, b)
            cur = z[(ch[0][0], ch[0][1])][1]
            for node in ch[1:]:
                a, b = z[(node[0], node[1])]
                if a == cur: n_touch += 1
                cur = b
        # NEGATIVE CONTROL of the nesting instrument: the carve's own rho7 must be feasible
        comps, fs = probe(rho[:5], (F(8 * m - 1), F(8 * m + 1)))
        n_neg += any(lo < r7 < hi for lo, hi in fs)
P('PIN rho6 <= 49/7                        : [T %d/%d]' % (n_pin, N))
P('regime strip (self-anchor available)    : [T %d/%d]' % (n_self, N))
P('ANCHOR coverer(R=1) = {(rho7,m)}        : [T %d/%d]' % (n_anchor, N))
P('greedy covers                           : [T %d/%d]' % (n_cov, N))
P('greedy chain starts at the anchor       : [T %d/%d]' % (n_start, N))
P('FRONT-CLOSURE rho6 > 7 rho7/(8m+1)      : [T %d/%d]' % (n_front, N))
P('rho7 in the strip-top end gap (c3)      : [T %d/%d]' % (n_gap7, N))
P('touch links (entry == exit) in chains   : %d' % n_touch)
P('NEG CONTROL nesting instrument: own rho7 feasible on own K6 : [T %d/%d]' % (n_neg, N))

# near-carve classification
P('# --- near-carves: regime x pin classification ---')
nrows = []
for idx, v in enumerate(near):
    rho = sorted(F(x) for x in v)
    r6, r7 = rho[4], rho[5]
    rg, m = regime(r7)
    anch = []
    for i, r in enumerate(rho):
        for j in coverers_of_R(F(1), r): anch.append((i + 2, j))
    ch, cov = greedy_chain(rho)
    rows = ('B2-strip' if (rg == 'strip' and F(7) < r6) else
            'B1-gap' if (rg == 'gap' and F(7) < r6) else
            'A-pinned-strip' if (rg == 'strip') else
            'A-pinned-gap' if (rg == 'gap') else '?')
    nrows.append((idx, rows, rg, m, float(r6), float(r7)))
    P('  near %d: %-14s %s m=%d rho6=%.4f rho7=%.4f anchor=%s covers=%s chain=%s' %
      (idx, rows, rg, m, float(r6), float(r7), anch, cov,
       [(i + 2, j) for i, j in (ch or [])][:9]))
cnt = {}
for x in nrows: cnt[x[1]] = cnt.get(x[1], 0) + 1
P('near classification count:', cnt)

# ================= P4: K6 / nesting probes on every near system =================
P('# === P4. K6 components + whole-window rho7 nesting on the near systems (exact) ===')
RLO = F(25)
for idx, v in enumerate(near):
    rho = sorted(F(x) for x in v)
    r6, r7 = rho[4], rho[5]
    rg, m = regime(r7)
    comps = k6_components(rho[:5])
    widths = [b - a for a, b in comps]
    lem2 = all(w < F(2) / r7 for w in widths) if comps else True
    win_own = (F(8 * m - 1), F(8 * m + 1)) if rg == 'strip' else ((F(8 * m + 1), F(8 * m + 7)) if rg == 'gap' else (RLO, F(50)))
    _, fs_own = probe(rho[:5], win_own)
    _, fs_50 = probe(rho[:5], (RLO, F(50)))
    _, fs_130 = probe(rho[:5], (RLO, F(130)))
    bad = [i for i, w in enumerate(widths) if not (w < F(2) / r7)]
    P('  near %d (%s, rho7=%.4f): K6 comps %d, max width %.5f, Lemma2(<2/rho7) %s %s' %
      (idx, nrows[idx][1], float(r7), len(comps), float(max(widths)) if widths else 0.0,
       lem2, ('FAIL at comps %s' % bad) if bad else ''))
    P('     feasible rho7 in own window %s: %s' %
      ('(%s,%s)' % (str(win_own[0])[:6], str(win_own[1])[:6]),
       [(str(lo)[:9], str(hi)[:9]) for lo, hi in fs_own] or 'EMPTY => whole-window kill'))
    P('     feasible rho7 in (25,50): %s' % ([(str(lo)[:9], str(hi)[:9]) for lo, hi in fs_50] or 'EMPTY (column kill on (25,50))'))
    P('     feasible rho7 in (25,130): %s   [+ E852 at rho7>=50 (rho6<=17): => dead for ALL rho7>=25]'
      % ([(str(lo)[:9], str(hi)[:9]) for lo, hi in fs_130] or 'EMPTY (column kill on (25,130))'))

# ================= P5: case-A synthetic probe (floats steer; exact verdicts) =================
P('# === P5. case-A probe: self-anchored unpinned candidates, rho7 in C_4 (exact verdicts) ===')
P('front via lap-1 small in (7rho7/33, 7] or lap-2 small in (15rho7/33, 15]; negative controls included.')
cand = []
for r7 in (31.4, 32.0, 32.5):
    lo1 = 7 * r7 / 33.0
    lo2 = 15 * r7 / 33.0
    for r5 in (6.8, 6.85, 6.9, 6.95):                  # spans the k=1 band edge lo1
        if r5 >= 7.0: continue
        for r6 in (7.5, 9.5, 11.0, 13.0, 14.5):
            if r6 <= r5: continue
            cand.append(('lap1?', [3.128139101571158, 3.722637992191327, 4.204281419315649, r5, r6, r7]))
    for r6 in (14.4, 14.7, 14.8, 14.9):                # spans the k=2 band edge lo2
        cand.append(('lap2?', [3.128139101571158, 3.722637992191327, 4.204281419315649, 5.238833615307547, r6, r7]))
        cand.append(('lap2?', [2.8690614936963414, 3.8828054084136983, 4.909405940454304, 6.360092296102934, r6, r7]))
n_cov5 = 0; maxreach = 0.0; reach_row = None
n_lem = n_lem_kill = 0; n_band_seam = n_noband_seam = 0
for tag, c in cand:
    rho = sorted(F(x) for x in c)
    if any(F(7) < x < F(9) or F(15) < x < F(17) for x in rho[:5]):
        continue   # enforce case A: no small in a strip
    r7 = rho[5]; x0 = F(33) / r7
    inband = any(coverers_of_R(x0, r) for r in rho[:5])
    ch, cov = greedy_chain(rho)
    reach = None
    if ch:
        z = {}
        for i, r in enumerate(rho):
            for a, b, j in zones_of(r): z[(i, j)] = (a, b)
        cur = z[(ch[0][0], ch[0][1])][1]
        for node in ch[1:]: cur = z[(node[0], node[1])][1]
        reach = float(cur)
        if reach > maxreach: maxreach, reach_row = reach, ([float(x) for x in rho], tag, inband)
        if cov: n_cov5 += 1
        n_band_seam += (1 if (inband and cur > x0) else 0)
    if not inband:
        n_lem += 1
        # the seam x0 is uncovered: the chain must stop with frontier <= x0 (or not start)
        killed = (not cov) and (ch is None or reach <= float(x0))
        n_lem_kill += killed
    else:
        n_noband_seam += 0
P('case-A candidates tested (strip-free): %d ; covered: %d ; best frontier reach: %.5f' % (len([1 for tag,c in cand if not any(F(7) < F(x) < F(9) or F(15) < F(x) < F(17) for x in sorted(F(x) for x in c)[:5])]), n_cov5, maxreach))
P('best-reach row:', reach_row)
P('front-closure constructive check: NO-band candidates %d, killed at the anchor seam [T %d/%d]'
  % (n_lem, n_lem_kill, n_lem))
P('(band candidates passing the seam: %d)' % n_band_seam)

out.close()
print('DONE')
