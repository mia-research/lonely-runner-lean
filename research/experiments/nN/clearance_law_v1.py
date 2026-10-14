"""The clearance law: how large must n be for k blockers (card k+1) to never fail?

f(k) = least n such that no card-(k+1) set has its largest flank fail.
A subject at order n has exactly n-2 blockers, so the diagonal holds iff  n >= f(n-2).
"""
import math
from itertools import combinations

def works(c, n):
    e = c[-1]; M = n*e; lo, hi = e, (n-1)*e
    return any(all(lo <= (d*(n*j+1)) % M <= hi for d in c) for j in range(e))

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

RANGE = {4: 30, 5: 24, 6: 18, 7: 15, 8: 13}
print(f"{'card':>5} {'blockers':>9}  failures by order n")
thresh = {}
for card in (4,5,6,7,8):
    hi = RANGE[card]
    sets = [c for c in combinations(range(1,hi+1), card) if prim(c)]
    line = []
    f = None
    for n in range(max(3,card), 26):
        bad = sum(1 for c in sets if not works(c, n))
        line.append(f"n={n}:{bad}")
        if bad == 0 and f is None: f = n
        if bad > 0: f = None          # require ALL larger n clean; reset on a failure
    # recompute f as least n with no failures from there on
    fails = {n: sum(1 for c in sets if not works(c, n)) for n in range(max(3,card), 26)}
    f = None
    for n in sorted(fails):
        if all(fails[m] == 0 for m in sorted(fails) if m >= n):
            f = n; break
    thresh[card-1] = f
    shown = " ".join(x for x in line if not x.endswith(":0"))[:90]
    print(f"{card:>5} {card-1:>9}  f({card-1}) = {f}    nonzero: {shown if shown else '(none)'}   [{len(sets)} sets, range [1,{hi}]]")

print()
print("=== the diagonal: a subject at order n has n-2 blockers ===")
print(f"{'n':>4} {'blockers n-2':>13} {'f(n-2)':>8} {'n >= f(n-2)?':>14}")
for n in range(5, 10):
    k = n - 2
    f = thresh.get(k)
    ok = (f is not None and n >= f)
    print(f"{n:>4} {k:>13} {str(f):>8} {('YES -- rank 1 holds' if ok else 'no -- rank 1 fails'):>14}")
