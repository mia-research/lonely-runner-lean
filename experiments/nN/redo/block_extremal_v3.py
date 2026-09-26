"""WP3 item 1: do resonances at t = 1/3, 1/4, 2/5 ... give longer blocked stretches than the t = 1/2 extremum (Q = 13/4)?
Starts built so that several readings are multiples of q (they sit on the subject at t = p/q) and the others sit at
fixed fractions; then the exact perturbation climb of block_extremal_v1.  Exact."""
import random
from fractions import Fraction as F
from multiprocessing import Pool
from block_extremal_v1 import Q, climb, comps
rnd = random.Random(33)
def res_start(q, a=180):
    # three readings multiples of q near a, 2a, 3a; three others near the progression with nonzero residues mod q
    base = [a, 2 * a, 3 * a, int(1.5 * a), int(2.5 * a), int(4.6 * a)]
    out = []
    for i, x in enumerate(base):
        if i < 3: out.append(q * round(x / q))
        else:
            y = x + rnd.randint(-5, 5)
            while y % q == 0: y += 1
            out.append(y)
    return sorted(set(out))
if __name__ == '__main__':
    starts = []
    for q in (2, 3, 4, 5, 6):
        for _ in range(4): starts.append(res_start(q))
    starts = [s for s in starts if len(s) == 6]
    with Pool() as p:
        res = list(p.imap_unordered(climb, starts))
    res.sort(key=lambda r: -r[2])
    for start, cur, qq, q0 in res[:8]:
        cs = comps(cur); L, a0, b0 = max(((b - a, a, b) for a, b in cs if a > 0))
        mid = (a0 + b0) / 2
        print(f"  Q = {qq} ({float(qq):.4f})  block {cur}  longest stretch centred at t = {mid} ({float(mid):.4f})")
    print(f"max Q over {len(res)} resonance-seeded climbs: {float(res[0][2]):.4f}  (t = 1/2 extremum: 13/4 = 3.25)")
