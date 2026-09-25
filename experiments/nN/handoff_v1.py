"""Are deaths of lonely cells compensated by births nearby, before or after?

Along the deformation from the ideal (deformation_v1), 400 exact steps, 25 random residual sets of
[1,40]: for each cell death, is there a birth within one step and within a quarter lap of the
fastest runner?  Null: the same births moved to random steps.
"""
import itertools, random, time
from fractions import Fraction as Fr
from collections import Counter
exec(open(__file__.replace('handoff_v1.py', 'deformation_v1.py')).read().split('sys.setrecursionlimit')[0])
_rs = __file__.replace('handoff_v1.py', 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])
def events_along(S, steps=400):
    s = sorted(S); ks = range(1, 8)
    Delta = Fr(sum(k * x for k, x in zip(ks, s)), sum(k * k for k in ks))
    prev = None; births = []; deaths = []
    for st in range(steps + 1):
        lam = Fr(st, steps)
        D = [(1 - lam) * k * Delta + lam * x for k, x in zip(ks, s)]
        cur = [(L, R) for L, oi, om, R, ci, cm in cells_real(D)]
        if prev is not None:
            for L, R in cur:
                if not any(L <= pR and pL <= R for pL, pR in prev): births.append((st, float(L)))
            for pL, pR in prev:
                if not any(L <= pR and pL <= R for L, R in cur): deaths.append((st, float(pL)))
        prev = cur
    return births, deaths, float(max(s))
def handoff_rate(births, deaths, win_t, win_st=1):
    hit = 0
    for st, t in deaths:
        if any(abs(bs - st) <= win_st and abs(bt - t) <= win_t for bs, bt in births): hit += 1
    return hit, len(deaths)
random.seed(10)
R = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
sets = random.sample(R, 25)
t0 = time.time(); H = N = HR = 0
for S in sets:
    b, d, dmax = events_along(S)
    w = 1 / (4 * dmax)                         # 'nearby': within a quarter lap of the fastest runner
    h, n = handoff_rate(b, d, w); H += h; N += n
    br = [(random.randrange(1, 401), t) for _, t in b]      # same births, random steps (null)
    hr, _ = handoff_rate(br, d, w); HR += hr
print(f"25 residual sets, 400 steps: deaths {N}; deaths with a birth within one step and a quarter lap: {H} ({H/N:.2f});  null (births at random steps): {HR} ({HR/N:.2f})  ({time.time()-t0:.0f}s)")
