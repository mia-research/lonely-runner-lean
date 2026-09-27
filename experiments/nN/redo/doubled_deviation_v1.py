"""(b) The doubled slot under deviation.  Bases: E40's family (AP, runner of slot r moved to s + 8m, m <= 4) and
one-doubled grids with laps <= 1.  Every speed deviated uniformly in [-rho, rho].  Per runner, by role:
  'beside'  = outside the pair, its residue next to the doubled slot (two runners one slot away at the grid instant);
  'other'   = outside the pair otherwise;  'home' / 'far' = the pair (home = the member with the smaller laps).
Measured: t*/t_base (t_base the undeviated event of the same runner): |factor - 1|/rho median, 95%, max, and jumps
(factor outside [2/3, 3/2]).  Exact."""
import random
from fractions import Fraction as F
from collections import defaultdict
from doubled_slot_grid_v1 import event
rnd = random.Random(49)
def base(kind):
    s, r = rnd.sample(range(8), 2); res = [x for x in range(8) if x != r] + [s]
    while True:
        if kind == 'E40': laps = [0] * 7 + [rnd.randint(1, 4)]
        else: laps = [rnd.randint(0, 1) for _ in range(8)]
        u = [res[i] + 8 * laps[i] for i in range(8)]
        if len(set(u)) == 8: return s, res, laps, [100 + x for x in u]
for kind in ('E40', 'laps<=1'):
    print(f"\n== {kind}")
    for rho in (F(1, 256), F(1, 64), F(1, 16)):
        st = defaultdict(list)
        for trial in range(300):
            s, res, laps, v0 = base(kind)
            v = [v0[i] + rho * F(rnd.randint(-97, 97), 97) for i in range(8)]
            if len(set(v)) < 8: continue
            pair = [i for i in range(8) if res[i] == s]
            home = min(pair, key=lambda i: laps[i])
            for k in range(8):
                role = ('home' if k == home else 'far') if k in pair else ('beside' if (res[k] - s) % 8 in (1, 7) else 'other')
                st[role].append(event(v, k) / event(v0, k))
        for role in ('other', 'beside', 'home', 'far'):
            f = st[role]; d = sorted(abs(x - 1) / rho for x in f); n = len(d)
            jumps = sum(1 for x in f if x > F(3, 2) or x < F(2, 3))
            print(f"  rho {str(rho):>5} {role:6s}: {n:5d} runners; |factor-1|/rho median {float(d[n//2]):.2f}, "
                  f"95% {float(d[19*n//20]):.2f}, max {float(d[-1]):.1f}; jumps {jumps}")
