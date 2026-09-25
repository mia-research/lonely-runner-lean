"""REDO (supersedes ap_local_v1 and tight_local_v1, which deformed one runner's disparities with that
runner at speed 0): do isolated runners keep their isolation when the ARRANGEMENT deforms?

Take arrangements of 8 distinct speeds in [1,24] that contain an isolated runner (isolated_runners_v1).
Deform every speed v_i -> v_i (1 + r_i), |r_i| <= rho, rational.  For EVERY runner, read its isolation
event with the exact cascade map (move cap 20,000); for the isolated runner, also record whether the
event lies near its old instants a/8 (within 1/64) and which class.
"""
import random
from collections import Counter
from itertools import combinations
from math import gcd
from functools import reduce
from arrangement_lib import readings, nd, F, floor
from isolated_runners_v1 import lonely_components
def cascade_cap(ds, cap=20000):
    t = F(1, 8) / min(ds); n = 0
    while n < cap:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t, n
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way); n += 1
    return None, n
if __name__ == '__main__':
    rnd = random.Random(50); found = []
    while len(found) < 150:
        V = tuple(sorted(rnd.sample(range(1, 25), 8)))
        if reduce(gcd, [v - V[0] for v in V[1:]]) != 1: continue
        iso = [k for k in range(8) if (lambda c: c and all(a == b for a, b in c))(lonely_components(readings(V, k)))]
        if iso: found.append((V, iso))
    for rho in (F(1, 50), F(1, 100), F(1, 400)):
        iso_ok = iso_tot = oth_ok = oth_tot = 0; near = Counter(); fails = []
        for V, iso in found:
            for rep in range(8):
                W = [v * (1 + F(rnd.randrange(-10**4, 10**4 + 1), 10**4) * rho) for v in V]
                for k in range(8):
                    t, n = cascade_cap(readings(W, k))
                    if k in iso:
                        iso_tot += 1
                        if t is not None:
                            iso_ok += 1
                            cls = next((a for a in (1, 3, 5, 7) for m in range(0, 3) if abs(t - (m + F(a, 8))) < F(1, 64)), None)
                            near[cls if cls else 'elsewhere'] += 1
                        elif len(fails) < 3: fails.append((V, k, [float(w) for w in W]))
                    else:
                        oth_tot += 1; oth_ok += t is not None
        print(f"|r| <= {rho}: isolated runners reach an isolation event {iso_ok}/{iso_tot} (class of the event: {dict(near)});  all other runners {oth_ok}/{oth_tot};  failures {fails[:2]}")
