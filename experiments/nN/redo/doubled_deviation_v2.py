"""doubled_deviation_v1 with E44's reference for the runners OUTSIDE the pair: the lonely instant nearest a class
instant p/8 (first lonely instant at or after p/8 - 1/64, p = 1,3,5,7), its relative offset /rho, split beside the
doubled slot vs other.  Also: is every such runner lonely within 8*rho (relative) of some class instant?"""
import random
from fractions import Fraction as F
from collections import defaultdict
from nested_cascade_v1 import cascade_from
rnd = random.Random(50)
def base(kind):
    s, r = rnd.sample(range(8), 2); res = [x for x in range(8) if x != r] + [s]
    while True:
        laps = [0] * 7 + [rnd.randint(1, 4)] if kind == 'E40' else [rnd.randint(0, 1) for _ in range(8)]
        u = [res[i] + 8 * laps[i] for i in range(8)]
        if len(set(u)) == 8: return s, res, [100 + x for x in u]
for kind in ('E40', 'laps<=1'):
    print(f"\n== {kind}")
    for rho in (F(1, 256), F(1, 64), F(1, 16)):
        st = defaultdict(list)
        for trial in range(300):
            s, res, v0 = base(kind)
            v = [v0[i] + rho * F(rnd.randint(-97, 97), 97) for i in range(8)]
            if len(set(v)) < 8: continue
            for k in range(8):
                if res[k] == s: continue
                role = 'beside' if (res[k] - s) % 8 in (1, 7) else 'other'
                ds = [abs(v[i] - v[k]) for i in range(8) if i != k]
                off = min(abs(cascade_from(ds, F(p, 8) - F(1, 64)) - F(p, 8)) / F(p, 8) for p in (1, 3, 5, 7))
                st[role].append(off / rho)
        for role in ('other', 'beside'):
            d = sorted(st[role]); n = len(d)
            print(f"  rho {str(rho):>5} {role:6s}: {n} runners; nearest class-instant offset/rho median {float(d[n//2]):.2f}, "
                  f"95% {float(d[19*n//20]):.2f}, max {float(d[-1]):.2f}; within 8*rho: {sum(1 for x in d if x <= 8)}/{n}")
