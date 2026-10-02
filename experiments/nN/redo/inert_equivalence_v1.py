# Equivalence #4: a reading that is clear at every visited state R_0..R_n (and the landing) is INERT: replacing it by ANY value that is
# also clear at those states leaves the whole sequence of states unchanged.  Test on random arrangements, exact.
import sys, random, math
from fractions import Fraction as F
sys.argv = [sys.argv[0]]
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
rnd = random.Random(323)
def q(x): return F(round(x * 1000), 1000)
def states(rhos):
    steps, Rend = path(rhos); return [mv["R"] for mv in steps] + [Rend] if steps else [Rend]
def clear_all(r, sts): return all(not blocks(R, r) for R in sts)
def gen():
    k = rnd.choice((0, 1, 2))
    if k == 0: xs = [q(math.exp(rnd.uniform(0, math.log(rnd.choice((9, 30, 100)))))) for _ in range(7)]
    elif k == 1:
        xs = [F(j) for j in range(1, 8)]
        for m in rnd.sample(range(7), rnd.choice((1, 2, 3))): xs[m] = max(F(11, 10), xs[m] + q(rnd.uniform(-1.5, 3.5)))
    else: xs = [F(rnd.randint(1, 40)) for _ in range(7)]
    xs = sorted(xs); m = xs[0]; xs = [x / m for x in xs]
    return xs if len(set(xs)) == 7 else gen()
tot = ok = inert_tot = 0; bad = []
for _ in range(1500):
    rh = gen(); sts = states(rh)
    inert = [i for i in range(7) if clear_all(rh[i], sts) and rh[i] != min(rh)]
    for i in inert:
        inert_tot += 1
        for _ in range(8):
            for _try in range(40):
                v = q(rnd.uniform(1.0, float(max(rh)) * 1.5))
                if v not in rh and clear_all(v, sts): break
            else: continue
            new = list(rh); new[i] = v
            if min(new) != min(rh): continue
            tot += 1
            if states(new) == sts: ok += 1
            else: bad.append((rh, i, v))
print("inert readings examined:", inert_tot, "; replacements tested:", tot, "; sequence of states unchanged:", ok, "; changed:", len(bad))
for b in bad[:5]: print("  CHANGED", [float(x) for x in b[0]], b[1], float(b[2]))
