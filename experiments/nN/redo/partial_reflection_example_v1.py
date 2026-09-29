"""Pick one real death event (Case B deformation path) where the partial reflection is the cascade's replacement, with
the smallest denominators, and print every quantity needed to state it as a Lean instance of
partial_reflected_right_inequalities."""
import itertools, math
from fractions import Fraction as F
import partial_reflection_v1 as PR
import deform_pinch_v1 as D
from quantity_tests_v1 import E8

best = None
for S in [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1]][::400]:
    S = tuple(sorted(S)); x = [F(7 * d, S[-1]) for d in S]
    r = D.follow(S)
    for e in r['events']:
        if e.get('kind') != 'death' or not e.get('simple') or e['tau'] in (None, 0):
            continue
        tau, t0, k = e['tau'], e['t0'], e['ka']
        ds = D.readings_at(x, tau)
        pos = [d * t0 - math.floor(d * t0) for d in ds]
        a = pos.index(E8); b = pos.index(F(7, 8))
        Qab = PR.lcm_rat(1 / ds[a], 1 / ds[b])
        j = math.floor(t0 / Qab) + 1
        Q = j * Qab; t2 = Q - t0
        lab = []
        ok = True
        for i, d in enumerate(ds):
            if i in (a, b):
                lab.append(int(Q * d) - k[i] - 1)
            else:
                f = d * t2 - math.floor(d * t2)
                if not (E8 < f < F(7, 8)):
                    ok = False; break
                lab.append(math.floor(d * t2))
        if not ok or tuple(lab) != e['kb']:
            continue
        size = max(max(d.denominator for d in ds), tau.denominator)
        if best is None or size < best[0]:
            best = (size, S, tau, t0, a, b, Q, j, [x[i] - (i + 1) for i in range(7)], ds, k, lab)
size, S, tau, t0, a, b, Q, j, v, ds, k, lab = best
print("S", S, "tau", tau, "t0", t0, "pair", a, b, "Q", Q, "j", j)
print("d", [str(d) for d in ds]); print("v", [str(w) for w in v]); print("q", k); print("lab", lab)
lam = Q / t0 - 1
print("lam", lam, "P_i for R:", int(Q * ds[a]), int(Q * ds[b]))
