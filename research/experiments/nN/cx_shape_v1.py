"""What do the largest-flank counterexamples LOOK like?

Integer form: flank e, opening j is lonely  <=>  for all d in ds,  d*(n*j+1) mod (n*e)  lies in
[e, (n-1)*e].  So the largest flank works iff some j in [0,e) satisfies that for every d.
Pure integers; validated against the Fraction implementation on the recorded n=8 witness.
"""
import math
from itertools import combinations

def largest_works(c, n):
    e = c[-1]; M = n*e; lo, hi = e, (n-1)*e
    for j in range(e):
        a = n*j + 1
        if all(lo <= (d*a) % M <= hi for d in c): return True
    return False

# validate against the record
print("=== validation ===")
print(f"  n=8 (2,3,5,7,8,13,16) largest flank works? {largest_works((2,3,5,7,8,13,16), 8)}  (record: NO)")
print(f"  n=6 (1,3,4,5,6)       largest flank works? {largest_works((1,3,4,5,6), 6)}  (record from our sweep: NO)")
print(f"  n=5 (1,13,15,28)      largest flank works? {largest_works((1,13,15,28), 5)}")
print()

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g, x)
    return g == 1

print("=== shape of the counterexamples, per order ===")
for n, hi in [(6, 30), (7, 24), (8, 20)]:
    k = n - 1
    fails = [c for c in combinations(range(1, hi+1), k) if prim(c) and not largest_works(c, n)]
    tot = sum(1 for c in combinations(range(1, hi+1), k) if prim(c))
    print(f"\n  n={n}, [1,{hi}]:  {len(fails)} failures out of {tot} primitive sets")
    if not fails: continue
    ratios = sorted(c[0]/c[-1] for c in fails)
    allr   = [c[0]/c[-1] for c in combinations(range(1,hi+1), k) if prim(c)]
    print(f"     d_min/d_max among FAILURES: max {max(ratios):.4f}   median {ratios[len(ratios)//2]:.4f}")
    print(f"     d_min/d_max among ALL sets: max {max(allr):.4f}   median {sorted(allr)[len(allr)//2]:.4f}")
    # how many of the k-1 smaller disparities are below d_max/(n-1)?
    below = [sum(1 for d in c[:-1] if d*(n-1) < c[-1]) for c in fails]
    allbelow = [sum(1 for d in c[:-1] if d*(n-1) < c[-1]) for c in combinations(range(1,hi+1), k) if prim(c)]
    print(f"     # disparities with d < d_max/(n-1):  failures min {min(below)}  |  all sets min {min(allbelow)}")
    print(f"     sample failures: {fails[:6]}")
