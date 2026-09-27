"""Class C of doubled_slot_grid_v2 (a pair member delayed past the grid instant, and the partner's opening
1/8 + 1/(64m) blocked), grouped for a law.  Orientation normalised so the partner is AHEAD: when it is behind, every
difference is negated (the mirror; loneliness unchanged).  Per case: empty-slot offset c = (r - s) mod 8 in that
orientation; the blockers of the partner's opening as (offset, side, stretch D/(8m)); the pair separation m; the event
as (flank = blocker / partner / offset x side, lap N)."""
import random, sys
from fractions import Fraction as F
from math import floor
from collections import Counter, defaultdict
from doubled_slot_grid_v1 import event, nd
Q = int(sys.argv[1]) if len(sys.argv) > 1 else 1
rnd = random.Random(43); groups = defaultdict(Counter); ncase = 0
for trial in range(6000):
    s, r = rnd.sample(range(8), 2); res = [x for x in range(8) if x != r] + [s]
    while True:
        laps = [rnd.randint(0, Q) for _ in range(8)]; u = [res[i] + 8 * laps[i] for i in range(8)]
        if len(set(u)) == 8: break
    v = [100 + x for x in u]; pair = [i for i in range(8) if res[i] == s]
    for k in pair:
        t = event(v, k); p = [i for i in pair if i != k][0]; m = abs(v[p] - v[k]) // 8
        if t <= F(1, 8): continue
        tm = F(1, 8) + F(1, 64 * m)
        bl = [i for i in range(8) if i != k and nd((v[i] - v[k]) * tm) < F(1, 8)]
        if not bl: continue
        ncase += 1
        sg = 1 if v[p] > v[k] else -1                       # mirror so the partner is ahead
        D = {i: sg * (v[i] - v[k]) for i in range(8) if i != k}
        c = (sg * (r - s)) % 8
        sig = tuple(sorted((D[i] % 8, 'ahead' if D[i] > 0 else 'behind', 'small' if abs(D[i]) < 8 * m else 'big') for i in bl))
        fl = [i for i in range(8) if i != k and (abs(v[i] - v[k]) * t) % 1 == F(1, 8)]
        i0 = min(fl, key=lambda i: abs(D[i])); N = floor(abs(D[i0]) * t)
        who = 'blocker' if i0 in bl else ('partner' if i0 == p else f'off {D[i0] % 8} {"ahead" if D[i0] > 0 else "behind"}')
        groups[(c, sig)][(who, N, 'R=' + str(8 * t) if Q == 1 and m == 1 else '')] += 1
print(f"Q = {Q}: {ncase} class-C cases; groups (empty-slot offset c, blocker signature) -> (flank, lap[, R when m = 1]):")
for key in sorted(groups, key=lambda k: -sum(groups[k].values()))[:24]:
    g = groups[key]
    print(f"  c={key[0]} blockers {list(key[1])}: {sum(g.values())} cases -> " +
          ", ".join(f"{w} N={n}{(' ' + R) if R else ''} x{cnt}" for (w, n, R), cnt in g.most_common(5)))
