"""Case II rule (5 | e): take a = k*e + 1.

Algebra: d*a = d*k*e + d, and mod 5e that is  e*(d*k mod 5) + d  (since 5 | e, d < e).
With 0 < d < e this lies in [e, 4e]  iff  d*k mod 5 in {1,2,3}.
The flank itself: 5 | e so e*k = 0 mod 5, giving value e -- clear, at the boundary.

Since r -> r*k is a bijection on {1,2,3,4} mod 5, the k FAILS only if some non-flank d has
d = 4*k^{-1} (mod 5).  So k works iff the non-flank residues MISS the value 4*k^{-1}.

At n=5, card 4, there are at most THREE non-flank disparities, so they cannot cover all four
nonzero residues {1,2,3,4} -- hence some k always works, PROVIDED no d is divisible by 5
(a d with 5|d gives d*k = 0, which is never in {1,2,3}).
"""
import math
from itertools import combinations

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

def clear_all(c, a, e):
    M = 5*e
    return all(e <= (d*a) % M <= 4*e for d in c)

hi = 60
caseII = [c for c in combinations(range(1, hi+1), 4)
          if prim(c) and c[-1] % 5 == 0 and c[-1] > 4*c[0] and c[-1] > 15]
noinner = [c for c in caseII if all(d % 5 != 0 for d in c[:-1])]
inner   = [c for c in caseII if any(d % 5 == 0 for d in c[:-1])]
print(f"Case II sets in [1,{hi}]: {len(caseII)}   no inner multiple: {len(noinner)}   with inner: {len(inner)}")
print()

def k_works(c, k):
    e = c[-1]
    return all((d*k) % 5 in (1,2,3) for d in c[:-1])

ok = bad = 0; ex = []
for c in noinner:
    e = c[-1]
    ks = [k for k in (1,2,3,4) if k_works(c, k)]
    if not ks:
        bad += 1
        if len(ex) < 3: ex.append((c, "no k"))
        continue
    # verify the prediction directly
    if all(clear_all(c, k*e+1, e) for k in ks): ok += 1
    else:
        bad += 1
        if len(ex) < 3: ex.append((c, f"k={ks} predicted but failed"))
print(f"no-inner-multiple Case II: rule finds a working k and it verifies: {ok} / {len(noinner)}")
print(f"   failures: {bad}  {ex}")
print()
ok2 = 0
for c in inner:
    e = c[-1]
    if any(k_works(c, k) and clear_all(c, k*e+1, e) for k in (1,2,3,4)): ok2 += 1
print(f"WITH inner multiple: rule works for {ok2} / {len(inner)}   (expected 0: 5|d gives d*k=0)")
print()
print("=== the residue-cover condition, stated ===")
from collections import Counter
cnt = Counter()
for c in noinner:
    cnt[tuple(sorted({d % 5 for d in c[:-1]}))] += 1
print("   distinct non-flank residue sets mod 5 (never all of {1,2,3,4}, since only 3 disparities):")
for k, v in sorted(cnt.items(), key=lambda p: -p[1])[:8]:
    print(f"      {k}: {v}")
