"""Interior-witness route: bound the UNION of the bad sets below 1, natively.

Bad(b) = { q mod m : q mod b NOT in [ceil((b-1)/8), floor((7b-1)/8)] }.
Each has density ~1/4; six of them give 6/4 > 1 if disjoint.  But when b | b', multiples of b'
are multiples of b, so the sets overlap heavily.  Measure the union exactly on CHAIN profiles
(b_1 | b_2 | ... | b_5 | m), where the divisor structure is cleanest.
"""
from itertools import combinations
from fractions import Fraction as F

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def badset(m, b):
    lo, hi = I(b)
    return {q for q in range(m) if not (lo <= q % b <= hi)}

def chains(m):
    """5-element chains of proper divisors of m, each dividing the next."""
    ds = sorted(d for d in range(2, m) if m % d == 0)
    out = []
    def go(pref):
        if len(pref) == 5: out.append(tuple(pref)); return
        last = pref[-1] if pref else 1
        for d in ds:
            if d > last and d % last == 0: go(pref + [d])
    go([])
    return out

rows = []
for m in range(24, 700):
    cs = chains(m)
    if not cs: continue
    for ch in cs:
        U = set()
        for b in list(ch) + [m]: U |= badset(m, b)
        rows.append((m, ch, F(len(U), m)))
if not rows:
    print("no chain profiles found"); raise SystemExit
mx = max(rows, key=lambda r: r[2])
print(f"CHAIN profiles (b_1 | ... | b_5 | m), m < 700 : {len(rows):,}")
print(f"  max union density : {mx[2]} = {float(mx[2]):.6f}   at m={mx[0]} chain={mx[1]}")
print(f"  is the union ever all of Z/m ?  {any(r[2] == 1 for r in rows)}")
import statistics
f = [float(r[2]) for r in rows]
print(f"  union density: min {min(f):.4f}  median {statistics.median(f):.4f}  max {max(f):.4f}")
print(f"  naive sum of densities would be ~6 x 1/4 = 1.5")
# is there a closed form?  compare with 1 - prod(1 - 1/4) style
print()
for m, ch, u in sorted(rows, key=lambda r: -r[2])[:6]:
    print(f"    m={m:<5} chain={ch}   union={u}={float(u):.4f}   free={1-u}")
