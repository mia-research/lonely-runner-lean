"""Step 3: deviations.  Base arrangements: complete grids (AP, laps <= 1, laps <= 3) and one-doubled-slot grids (E40's
family m <= 3, and laps <= 1); speeds 100 + residue + 8*laps.  Every speed deviated by e_i uniform in [-rho, rho]
(gap units; exact rationals, denominator 97*rho's).  At the grid instant a deviation e moves a runner e eighths
(Prop 2.2), so |e| < 1 keeps every runner inside its own slot's band.  Every runner, exact cascade.  Per runner vs the
same runner in the undeviated base: relocation factor t*/t_base; flank is a circle neighbour at the grid instant
(residue offset +-1) or not; class kept (delayed past 1/8 or not, same as base)."""
import random
from fractions import Fraction as F
from math import floor
from collections import Counter
from doubled_slot_grid_v1 import event, nd

def flank_of(v, k, t):
    fl = [i for i in range(8) if i != k and (abs(v[i] - v[k]) * t) % 1 == F(1, 8)]
    return fl

def bases(kind, rnd):
    if kind.startswith('grid'):
        Q = {'grid AP': 0, 'grid laps<=1': 1, 'grid laps<=3': 3}[kind]
        res = list(range(8))
    else:
        Q = {'doubled E40': 0, 'doubled laps<=1': 1}[kind]
        s, r = rnd.sample(range(8), 2); res = [x for x in range(8) if x != r] + [s]
    while True:
        laps = [rnd.randint(0, Q) for _ in range(8)]
        if kind == 'doubled E40':
            laps = [0] * 8; laps[7] = rnd.randint(1, 3)
        u = [res[i] + 8 * laps[i] for i in range(8)]
        if len(set(u)) == 8: return res, [100 + x for x in u]

if __name__ == '__main__':
    rnd = random.Random(45)
    for kind in ('grid AP', 'grid laps<=1', 'grid laps<=3', 'doubled E40', 'doubled laps<=1'):
        print(f"\n== {kind}")
        for rho in (F(1, 64), F(1, 16), F(1, 8), F(1, 4), F(1, 2), F(1)):
            fac = []; nb = Counter(); cls = Counter()
            for trial in range(250):
                res, v0 = bases(kind, rnd)
                den = 97
                v = [v0[i] + rho * F(rnd.randint(-den, den), den) for i in range(8)]
                if len(set(v)) < 8: continue
                for k in range(8):
                    t0 = event(v0, k); t = event(v, k)
                    fac.append(t / t0)
                    cls['kept' if (t0 > F(1, 8)) == (t > F(1, 8)) else 'changed'] += 1
                    fl = flank_of(v, k, t)
                    offs = {(res[i] - res[k]) % 8 for i in fl}
                    nb['circle neighbour' if offs & {1, 7} else 'other'] += 1
            fac.sort(); n = len(fac)
            print(f"  rho {str(rho):>5}: {n} runners; t*/t_base min {float(fac[0]):.3f}, 5% {float(fac[n//20]):.3f}, "
                  f"median {float(fac[n//2]):.3f}, 95% {float(fac[19*n//20]):.3f}, max {float(fac[-1]):.3f};  "
                  f"class kept {cls['kept']}/{n};  flank a circle neighbour {nb['circle neighbour']}/{n}")
