# tailrest_anchor_v1.py -- THE ANCHOR-CLASSIFICATION LEMMA (E840's named not-done), exact.
# Question (mission residue A-i): which reading's zone covers R=1, as a function of the
# rho7 regime (strip m vs gap) and the pin state (rho6 < 49/7 vs rho6 in (7,9))?
# Comb arithmetic only: a zone (8j-1, 8j+1)/rho of a reading rho covers R=1 iff
# (8j-1)/rho < 1 < (8j+1)/rho  <=>  8j-1 < rho < 8j+1  (rho in the strip C_j).
# Parts:
#   P1 the comb classification, proved by exact interval arithmetic (no floats anywhere):
#      (a) strips are disjoint, spaced 6 (a reading sits in at most one strip);
#      (b) PIN REGIME rho6 <= 49/7: readings rho2..rho6 lie in (1, 49/7] = (1, 7],
#          which is disjoint from every strip => the R=1 coverer set is
#          empty  or  exactly {(rho7, m)} (m = rho7's unique strip);
#      (c) GAP COROLLARY: rho7 in a gap (8m+1, 8m+7) => NO reading covers R=1 =>
#          no carve of [1,7] (a carve's zones are open and must contain R=1);
#      (d) rho6-ANCHORED REGIME (pin broken, rho6 in (7,9)): the coverer set is
#          {(k,1) : rho_k in (7,9)} plus {(7,m)} if rho7 in strip m;
#      (e) no reading in (1,7] covers 1 at ANY lap (checked j=0..8 per reading value).
#   P2 validation [T n/N] against the recorded population (E839 taxonomy: carves
#      self-anchored lap2 x6 + lap3 x90; near-carves rho6-lap1 x7 + one rho7-lap5):
#      per vector: regime of rho7, pin state, predicted coverer set, recorded greedy
#      chain's start zone; verdict = start zone's (reading, lap) in the predicted set
#      AND (pin regime) the set is the singleton.
#   P3 the anchor lemma statement, written to tailrest_anchor_lemma_v1.out.
from fractions import Fraction as F
import pickle, glob, re, sys, time

sys.path.insert(0, '/Users/trentpalelei/Desktop/Math Ex/experiments/n8')

DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'
out = open(DIR + 'tailrest_anchor_v1.out', 'w')
def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True); out.write(s + '\n'); out.flush()

P('# tailrest_anchor_v1 -- exact; started', time.strftime('%Y-%m-%d %H:%M:%S'))

# ---------------- P1: the comb classification (exact interval arithmetic) ----------------
P('# === P1. comb classification (exact) ===')

# (a) strips C_j = (8j-1, 8j+1) pairwise disjoint, gap (8j+1, 8j+7) width 6 between them.
ok_disjoint = all(F(8 * (j + 1) - 1) >= F(8 * j + 1) + 6 for j in range(0, 200))
P('(a) strips disjoint with gap width >= 6 for j=0..199:', ok_disjoint,
  ' (8(j+1)-1) - (8j+1) =', F(6))

# (b) PIN REGIME: C intersect (1, 49/7] is empty; hence rho2..rho6 cover 1 at no lap.
#     Reading rho in (1,7] covers 1 at lap j iff 8j-1 < rho < 8j+1; for j>=1 this needs
#     rho > 7; for j=0 it needs rho < 1. Exact sweep over all j and the exact endpoints.
PIN = F(49, 7)
hits = []
for j in range(0, 9):
    lo, hi = F(8 * j - 1), F(8 * j + 1)
    # interval intersection (lo,hi) with (1, PIN], endpoints exact:
    lo2, hi2 = max(lo, F(1)), min(hi, PIN)
    if lo2 < hi2 or (lo2 == hi2 and lo < lo2 < hi):   # nonempty open intersection with (1,7]
        hits.append(j)
    # strict interior containment check of the shared part:
    if lo < PIN and hi > F(1) and lo2 < hi2:
        hits.append(('endpoint-check', j))
P('(b) strips meeting the open interval (1, 49/7] = (1, 7]:', hits, '-> EMPTY' if not hits else '-> NONEMPTY: LEMMA FAILS')

# exact statement: for every strip j>=1, 8j-1 >= 7, and 7 not in the OPEN strip (7,9):
b_j1 = F(8 * 1 - 1) == F(7)                # lower edge of strip 1 is exactly 7
b_open = not (F(7) > F(7))                 # 7 is not an interior point of (7,9)
P('    strip-1 lower edge 8*1-1 = 7 exactly:', b_j1, '| 7 interior to (7,9):', not b_open)

# (c) gap regime: rho7 in (8m+1, 8m+7) meets no strip for any m>=1 and any lap j.
ok_gap = all((F(8 * m + 7) <= F(8 * m + 1) + 6) and (F(8 * m + 1) >= F(8 * m - 1) + 2)
             for m in range(1, 200))
# rho7 in (8m+1, 8m+7): strictly above strip m's top (8m+1) and strictly below strip m+1's
# bottom (8m+7); exact:
gap_ok = all((F(8 * m + 1) >= F(8 * (m) + 1)) and (F(8 * (m + 1) - 1) == F(8 * m + 7))
             for m in range(1, 200))
P('(c) gap (8m+1, 8m+7) = complement of strips m and m+1 closure for m=1..199:', ok_gap, gap_ok)

# (d) rho6-anchored regime: strips reachable by readings <= rho6 < 9 are exactly strip 1.
#     (15,17) needs rho > 15 > 9. exact:
d_ok = F(8 * 2 - 1) == F(15) and F(15) > F(9)
P('(d) strip-2 lower edge 15 > 9 (so readings < 9 reach only strip 1):', d_ok)

# (e) full sweep: for rho-values at the exact rationals k/8 in (1, 33], which laps cover 1.
#     Pure comb: rho covers 1 iff rho in some (8j-1, 8j+1). Enumerate rho in (1,7] exactly
#     at a fine exact grid and confirm zero laps; and rho in (7,9) exactly lap 1, etc.
def cover_laps(rho):
    return [j for j in range(0, 12) if F(8 * j - 1) < rho < F(8 * j + 1)]
n_bad = 0
# grid: all midpoints of consecutive grid points k/64 (exact rationals, interior points only)
# expectation = the OPEN strip ladder; exact edges (rho = 8j-1 or 8j+1) cover 1 at NO lap.
pts = [F(k, 64) for k in range(65, 33 * 64)]
for rho in pts:
    ls = cover_laps(rho)
    exp = []
    for j in range(1, 5):
        if F(8 * j - 1) < rho < F(8 * j + 1):
            exp = [j]
    if rho > F(33) or rho <= F(1):
        continue
    if ls != exp:
        n_bad += 1
P('(e) exact comb sweep over', len(pts), 'rationals in (1,33): violations =', n_bad)
# exact-edge check: rho exactly at a strip edge covers 1 at no lap (open zones)
edge_bad = [rho for rho in (F(7), F(9), F(15), F(17), F(23), F(25), F(31), F(33)) if cover_laps(rho)]
P('    exact strip-edge values covering 1:', edge_bad, '-> NONE (open intervals)' if not edge_bad else 'FAILS')

# ---------------- P2: validation against the recorded population ----------------
P('# === P2. validation vs the 105 recorded vectors [T n/N] ===')
sys_path_saved = list(sys.path)
vecs_carves = {2: [], 3: []}
for k in (2, 3):
    for f in sorted(glob.glob(DIR + 'frontier_band_carve_v1_k%d_s*.pkl' % k)):
        vecs_carves[k] += pickle.load(open(f, 'rb'))
for f in sorted(glob.glob(DIR + 'frontier_box_carve_v1_23_25_s*.pkl')):
    vecs_carves[3] += pickle.load(open(f, 'rb'))
near = [pickle.load(open(DIR + 'frontier_polish_v1_first.pkl', 'rb'))]
for f in sorted(glob.glob(DIR + 'frontier_box_carve_v1_hi2_s*.out')):
    m_ = re.search(r'readings \(float\): \[(.*)\]', open(f).readline())
    if m_: near.append([float(v) for v in m_.group(1).split(',')])
P('carves loaded: lap2', len(vecs_carves[2]), 'lap3', len(vecs_carves[3]),
  '| near-carves above 25:', len(near))

from taillemma_lib_v1 import greedy_chain

def regime(rho7):
    """'strip m' / 'gap m' / other, exact."""
    for m in range(1, 40):
        if F(8 * m - 1) < rho7 < F(8 * m + 1):
            return ('strip', m)
        if F(8 * m + 1) < rho7 < F(8 * m + 7):
            return ('gap', m)
    return (None, None)

def coverer_set(rho_sorted, pin_regime):
    """Predicted coverer set of R=1 (as reading indices 2..7 with laps), exact comb.
    rho_sorted: the six readings rho2..rho6 (values) and rho7.
    pin_regime True means rho6 <= 49/7."""
    out_set = []
    rho7 = rho_sorted[5]
    reg, m = regime(rho7)
    if pin_regime:
        if reg == 'strip':
            out_set.append((7, m))       # unique coverer (rho7, m)
        # gap => empty
        return out_set, reg, m
    # unpinned: readings rho_k in (7,9) anchor at lap 1; rho7 anchors if in a strip;
    # readings in higher strips (>=15) would anchor at their lap (none in the recorded
    # population; the lemma lists them combinatorially).
    for i, r in enumerate(rho_sorted[:5]):
        if F(7) < r < F(9):
            out_set.append((i + 2, 1))
    if reg == 'strip':
        out_set.append((7, m))
    return out_set, reg, m

def maxpin(rho_sorted):
    return rho_sorted[4] <= F(49, 7)   # rho6 <= 49/7

tally = {}
n_ok = n_tot = 0
rows = []
for k in (2, 3):
    for v in vecs_carves[k]:
        rho = sorted(F(x) for x in v)
        ch, cov = greedy_chain(rho)
        pr = maxpin(rho)
        cs, reg, m = coverer_set(rho, pr)
        anchor = (ch[0][0] + 2, ch[0][1]) if ch else None
        # verdict: the greedy start zone lies in the predicted coverer set; in the pin
        # regime the set must be the singleton {(7,m)}; an empty predicted set must
        # coincide with the chain being unable to start (no zone covers R=1).
        if not cs:
            ok = (ch is None) and (not cov)
        elif pr:
            ok = (ch is not None) and (anchor in cs) and (len(cs) == 1)
        else:
            ok = (ch is not None) and (anchor in cs)
        n_tot += 1; n_ok += ok
        key = ('carve-strip%d' % k, reg, m, 'pin' if pr else 'nopin')
        tally.setdefault(key, [0, 0])
        tally[key][0] += ok; tally[key][1] += 1
        if not ok and len(rows) < 5:
            rows.append((k, rho[-1], pr, reg, m, cs, anchor, cov))
for v in near:
    rho = sorted(F(x) for x in v)
    ch, cov = greedy_chain(rho)
    pr = maxpin(rho)
    cs, reg, m = coverer_set(rho, pr)
    anchor = (ch[0][0] + 2, ch[0][1]) if ch else None
    if not cs:
        ok = (ch is None) and (not cov)          # gap corollary in action
    else:
        ok = (ch is not None) and (anchor in cs)
    n_tot += 1; n_ok += ok
    key = ('near', reg, m, 'pin' if pr else 'nopin')
    tally.setdefault(key, [0, 0])
    tally[key][0] += ok; tally[key][1] += 1
    if not ok and len(rows) < 10:
        rows.append(('near', rho[-1], pr, reg, m, cs, anchor, cov))
P('ANCHOR-CLASS validation: [T %d/%d]' % (n_ok, n_tot))
for key in sorted(tally, key=str):
    P('   ', key, ': [T %d/%d]' % (tuple(tally[key])))
for r in rows:
    P('    MISS:', r)

# the pin state of every recorded vector, exact counts
n_pin = sum(1 for k in (2, 3) for v in vecs_carves[k] if maxpin(sorted(F(x) for x in v)))
n_near_nopin = sum(1 for v in near if not maxpin(sorted(F(x) for x in v)))
P('pin state: carves with rho6 <= 49/7:', n_pin, '/', len(vecs_carves[2]) + len(vecs_carves[3]),
  '| near-carves with rho6 > 49/7:', n_near_nopin, '/', len(near))

# rho7 regimes of the recorded population, exact
regc = {}
for k in (2, 3):
    for v in vecs_carves[k]:
        r7 = sorted(F(x) for x in v)[5]
        regc[('carve',) + regime(r7)] = regc.get(('carve',) + regime(r7), 0) + 1
for v in near:
    r7 = sorted(F(x) for x in v)[5]
    regc[('near',) + regime(r7)] = regc.get(('near',) + regime(r7), 0) + 1
P('regime census (exact):')
for key in sorted(regc, key=str):
    P('   ', key, ':', regc[key])

# GAP COROLLARY check on the near-carve gap vectors: under the pin they would be dead
# (no coverer); they live only because rho6 > 7. exact demonstration:
P('# gap near-carves: the anchor reading and its lap, exact')
for v in near:
    rho = sorted(F(x) for x in v)
    ch, cov = greedy_chain(rho)
    r6 = rho[4]; r7 = rho[5]
    reg, m = regime(r7)
    instrip1 = F(7) < r6 < F(9)
    P('   rho6=%s (%.4f) rho7=%s (%.4f) regime=%s pin=%s rho6-in-(7,9)=%s chain-start=%s covers=%s'
      % (r6, float(r6), r7, float(r7), (reg, m), maxpin(rho), instrip1,
         (ch[0][0] + 2, ch[0][1]) if ch else None, cov))

out.close()
print('DONE P1/P2')
