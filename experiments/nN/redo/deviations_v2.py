"""deviations_v1 re-measured on the AP's own spine.  For each runner of a deviated arrangement: its event's nearest spine
instant p/8 (p odd; the grid gap is 1), the relative offset |8t* - p|/p, that offset divided by rho (is the relocation
proportional to the deviation?), and whether the flank is a circle neighbour for class p (residue offset +-p, the
neighbour rule, Cor 4.15).  Classes p mod 8 in {1,3,5,7} are the four class instants of phi(8) = 4."""
import random
from fractions import Fraction as F
from math import floor
from collections import Counter
from doubled_slot_grid_v1 import event
from deviations_v1 import bases, flank_of
rnd = random.Random(46)
for kind in ('grid AP', 'grid laps<=1', 'grid laps<=3', 'doubled E40', 'doubled laps<=1'):
    print(f"\n== {kind}")
    for rho in (F(1, 64), F(1, 16), F(1, 8), F(1, 4), F(1, 2), F(1)):
        cls = Counter(); rel = []; nbr = Counter(); n = 0
        for trial in range(250):
            res, v0 = bases(kind, rnd)
            v = [v0[i] + rho * F(rnd.randint(-97, 97), 97) for i in range(8)]
            if len(set(v)) < 8: continue
            for k in range(8):
                t = event(v, k); x = 8 * t
                p = 2 * floor(x / 2) + 1                    # nearest odd integer
                if abs(x - (p + 2)) < abs(x - p): p += 2
                if p > 1 and abs(x - (p - 2)) < abs(x - p): p -= 2
                n += 1; cls[p % 8 if p < 8 else f'{p % 8} (lap {p // 8})'] += 1
                rel.append(abs(x - p) / p / rho)
                fl = flank_of(v, k, t)
                offs = {(res[i] - res[k]) % 8 for i in fl}
                nbr['class neighbour' if offs & {p % 8, (8 - p) % 8} else 'other'] += 1
        rel.sort()
        print(f"  rho {str(rho):>5}: {n} runners; nearest spine class: " +
              ", ".join(f"{c}: {m}" for c, m in sorted(cls.items(), key=lambda z: -z[1])[:6]) +
              f";  |8t*-p|/(p*rho): median {float(rel[n//2]):.2f}, 95% {float(rel[19*n//20]):.2f}, max {float(rel[-1]):.2f}"
              f";  flank a class neighbour {nbr['class neighbour']}/{n}")
