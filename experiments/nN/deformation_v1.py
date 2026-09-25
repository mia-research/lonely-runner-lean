"""Lonely cells followed along the deformation from the ideal.

S sorted s_1 < ... < s_7; its best-fitting progression puts s_k at k*Delta, Delta = sum k s_k / sum k^2.
Along d_k(lambda) = (1 - lambda) k Delta + lambda s_k (exact rational steps), the lonely cells in
(0, 1] are computed exactly; a cell descends from the previous step's cells it overlaps, and one
with none is born.  At lambda = 0 the cells are the global instants a/(8 Delta) + m/Delta, each a
point.  Every birth is a two-runner pinch: an opening runner at +1/8 and a closing runner at -1/8,
the event's geometry for one pair.

Reports: for the 28 sets no q <= 8 certifies, the two with delta = 2/15, and 30 random residual
sets of [1,40], whether any cell at lambda = 1 descends from an event, and the (opening, closing)
ranks of born cells; then, for six sets at 300 and 600 steps, when the last event-descended cell
dies and how many cells are born along the path.
"""
import itertools, random, time, sys
from fractions import Fraction as Fr
from collections import Counter
from math import floor, ceil
def cells_real(D, T=Fr(1)):
    """lonely cells in (0, T] for positive rational speeds D (list); each (L, openidx, lap, R, closeidx, lap)"""
    zones = []
    for idx, d in enumerate(D):
        for m in range(0, int(d * T) + 2):
            lo, hi = (m - Fr(1, 8)) / d, (m + Fr(1, 8)) / d
            if hi > 0 and lo < T: zones.append((lo, hi, idx, m))
    zones.sort()
    out = []; cur_hi = None; cur = None
    for lo, hi, idx, m in zones:
        if cur_hi is not None and lo >= cur_hi and cur_hi < T:
            out.append((cur_hi, cur[0], cur[1], min(lo, T), idx, m))
        if cur_hi is None or hi > cur_hi: cur_hi, cur = hi, (idx, m)
    if cur_hi is not None and cur_hi < T: out.append((cur_hi, cur[0], cur[1], T, None, None))
    return out
def track(S, steps=300):
    s = sorted(S); ks = range(1, 8)
    Delta = Fr(sum(k * x for k, x in zip(ks, s)), sum(k * k for k in ks))
    prev = []
    for step in range(steps + 1):
        lam = Fr(step, steps)
        D = [(1 - lam) * k * Delta + lam * x for k, x in zip(ks, s)]
        C = cells_real(D)
        cur = []
        for L, oi, om, R, ci, cm in C:
            anc = set()
            for pL, pR, panc in prev:
                if L <= pR and pL <= R: anc |= panc
            if step == 0:
                a = round(float(L * Delta * 8)) % 8          # event class a/(8 Delta) + m/Delta
                anc = {("event", a)}
            elif not anc:
                anc = {("born", float(lam), oi + 1, (ci + 1) if ci is not None else None)}
            cur.append((L, R, frozenset(anc)))
        prev = cur
    return Delta, prev
sys.setrecursionlimit(10000)
_rs = __file__.replace('deformation_v1.py', 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])
t0 = time.time()
R40 = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
caseB = [S for S in R40 if not any(rule(S, q, free_exact) for q in range(2, 9))]
tight = [(1, 3, 4, 5, 7, 11, 24), (1, 4, 5, 6, 7, 11, 16)]
random.seed(7); samp = random.sample(R40, 30)
print(f"setup {time.time()-t0:.0f}s")
for label, sets in (("Case B (28)", caseB), ("delta = 2/15 (2)", tight), ("random residual (30)", samp)):
    t1 = time.time(); summ = Counter(); births = Counter(); evcls = Counter()
    for S in sets:
        Delta, final = track(S)
        ev = [c for c in final if any(a[0] == "event" for a in c[2])]
        born = [c for c in final if all(a[0] == "born" for a in c[2])]
        summ['sets with a cell descended from an event'] += bool(ev)
        summ['sets with a born cell'] += bool(born)
        summ['sets whose every cell is born'] += (not ev)
        for c in ev:
            for a in c[2]:
                if a[0] == "event": evcls[a[1]] += 1
        for c in born:
            for a in c[2]: births[(a[2], a[3])] += 1
    print(f"{label}: {dict(summ)}  ({time.time()-t1:.0f}s)")
    print(f"   event classes a (mod 8) reaching lambda = 1: {dict(evcls)}")
    print(f"   born cells by (opening rank, closing rank) at birth: {births.most_common(8)}")

def track_detail(S, steps):
    s = sorted(S); ks = range(1, 8)
    Delta = Fr(sum(k * x for k, x in zip(ks, s)), sum(k * k for k in ks))
    prev = []; last_event = 0.0; nbirth = 0; first_ev = None
    for step in range(steps + 1):
        lam = Fr(step, steps)
        D = [(1 - lam) * k * Delta + lam * x for k, x in zip(ks, s)]
        cur = []
        for L, oi, om, R, ci, cm in cells_real(D):
            anc = set()
            for pL, pR, panc in prev:
                if L <= pR and pL <= R: anc |= panc
            if step == 0: anc = {"event"}
            elif not anc: anc = {"born"}; nbirth += 1
            cur.append((L, R, frozenset(anc)))
        if step == 0: first_ev = len(cur)
        if any("event" in c[2] for c in cur): last_event = float(lam)
        prev = cur
    return first_ev, last_event, nbirth, len(prev), sum("event" in c[2] for c in prev)
sets = [(1, 3, 4, 5, 7, 11, 24), (1, 4, 5, 6, 7, 11, 16), (3, 5, 6, 7, 8, 26, 27), (2, 12, 15, 21, 32, 34, 38), (5, 8, 18, 28, 34, 38, 39), (1, 5, 6, 7, 8, 17, 19)]
for S in sets:
    for steps in (300, 600):
        t0 = time.time()
        ev0, last, nb, nf, nfe = track_detail(S, steps)
        print(f"{S} steps {steps}: events at lambda 0: {ev0}; last event-descended cell alive at lambda {last:.3f}; births along the path {nb}; cells at lambda 1: {nf} (event-descended {nfe})  ({time.time()-t0:.1f}s)")
