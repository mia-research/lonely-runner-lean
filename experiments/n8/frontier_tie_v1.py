# E829: the first polished near-carve above 25 (frontier_polish_v1_first.pkl): its exact closed clear set on [1,7] (Fractions of the float readings), and 9,000 random perturbations tested for an exact carve (strict overlap of the open zones).  Seeded.
import pickle, random
from fractions import Fraction as F
def clear_components(rs):
    iv = []
    for r in rs:
        r = F(r); j = 1
        while F(8 * j - 1) / r < 7:
            iv.append((F(8 * j - 1) / r, F(8 * j + 1) / r)); j += 1
    iv.sort(); out = []; cur = F(1)
    if any(a < 1 < b for a, b in iv): cur = max(b for a, b in iv if a < 1)
    else: out.append((F(1), F(1)))
    for a, b in iv:
        if b <= cur: continue
        if a >= cur and a <= 7: out.append((cur, a))
        if b > cur: cur = b
    if cur < 7: out.append((cur, F(7)))
    return [(x, y) for x, y in out if y >= x]
x = pickle.load(open('frontier_polish_v1_first.pkl', 'rb'))
print('readings', x)
comps = clear_components(x)
print('exact closed clear set of [1,7]: components', len(comps))
for a, b in comps: print('  at R =', float(a), 'length below 1e-15:', (b - a) < F(1, 10**15), 'exact length', b - a)
random.seed(5); hit = 0; tot = 0
for scale in [1e-9, 1e-8, 1e-7, 1e-6, 1e-5, 1e-4]:
    for _ in range(1500):
        y = sorted(max(1.0001, v * (1 + scale * random.uniform(-1, 1))) for v in x)
        tot += 1
        if not clear_components(y): hit += 1
print('random perturbations tested', tot, 'exact carves among them', hit)
