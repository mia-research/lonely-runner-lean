"""
The tightest configurations: runners whose clear set is a SINGLE instant.

margin_count_v1 found the minimum number of clear components is 1 at every n tested.
This enumerates every such runner and asks what they look like:

  - where is the single instant?  (is it always u = 1/n, the opening of the nearest
    runner's own zone, as the first examples suggested?)
  - which runner is it?  (the extremal examples were all the top speed)
  - what do the speed sets look like?

Any attack on part 7 has to survive these: a configuration whose entire clear set is one
point leaves nothing to spare. Locating them is not a proof of anything.

Exact; open zones; never merged.
"""
import sys, itertools
from collections import Counter
from fractions import Fraction as F
from math import gcd
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from margin_count_v1 import clear_components, phi, readings

def all_clear_points(v, i, n):
    lo, hi = F(1, n), F(n - 1, n)
    Z = []
    for s in readings(v, i, n):
        k = 0
        while True:
            a = F(n * k - 1, n) / s
            if a > hi:
                break
            b = F(n * k + 1, n) / s
            if b > lo:
                Z.append((a, b))
            k += 1
    Z.sort()
    cands = sorted({lo} | {b for _, b in Z if lo <= b <= hi})
    out, ptr, maxb = [], 0, None
    for u in cands:
        while ptr < len(Z) and Z[ptr][0] < u:
            b = Z[ptr][1]
            if maxb is None or b > maxb:
                maxb = b
            ptr += 1
        if maxb is None or not (maxb > u):
            out.append(u)
    return out

def hunt(n, V):
    singles = []
    for v in itertools.combinations(range(1, V + 1), n):
        g = 0
        for x in v:
            g = gcd(g, x)
        if g != 1:
            continue
        for i in range(n):
            c, _ = clear_components(list(v), i, n)
            if c == 1:
                u = all_clear_points(list(v), i, n)[0]
                singles.append((v, i, u))
    return singles

if __name__ == "__main__":
    spec = [(5, 20), (6, 17), (7, 15), (8, 14), (9, 13)]
    if len(sys.argv) > 1:
        spec = [(int(a.split(':')[0]), int(a.split(':')[1])) for a in sys.argv[1:]]
    for n, V in spec:
        S = hunt(n, V)
        at_start = sum(1 for _, _, u in S if u == F(1, n))
        pos = Counter(str(u) for _, _, u in S)
        which = Counter("top" if i == n - 1 else ("bottom" if i == 0 else "middle")
                        for _, i, _ in S)
        print(f"n={n} (phi={phi(n)}), speeds <= {V}:  {len(S)} runners with a "
              f"SINGLE clear instant")
        print(f"    at u = 1/n : {at_start} of {len(S)}")
        if len(pos) > 1:
            print(f"    other positions: "
                  + ", ".join(f"{k}x{c}" for k, c in pos.most_common(5) if k != str(F(1,n))))
        print(f"    which runner: {dict(which)}")
        ex = [(v, i) for v, i, _ in S][:4]
        print(f"    examples: {ex}")
        print(flush=True)
