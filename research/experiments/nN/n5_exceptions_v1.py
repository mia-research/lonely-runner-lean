"""Understanding the exceptions: why do the low-opening residue sets have few openings?

Observation from the <=2 list: the extremes are (5,15,20,e) = 5*(1,3,4) plus a flank -- EVERY
non-flank disparity a multiple of 5.  When that happens the 5 cancels in all of them and the
system becomes
      m_i * a  mod e  in [e/5, 4e/5]     for every i,
which is the SAME band shape at modulus e instead of 5e.  The problem is SELF-SIMILAR: a
smaller instance of itself.  That is why those sets are hardest -- they are the residue
composed with itself.
"""
import math
from itertools import combinations
from collections import Counter

def n_open(c, cap=99):
    e = c[-1]; M = 5*e
    return sum(1 for j in range(e) if all(e <= (d*(5*j+1)) % M <= 4*e for d in c))

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

def in_residue(c):
    e = c[-1]
    return any(d % 5 == 0 for d in c[:-1]) and e > 4*c[0] and e > 15

hi = 80
sets = [c for c in combinations(range(1, hi+1), 4) if prim(c) and in_residue(c)]
low = [c for c in sets if n_open(c) <= 2]
print(f"residue [1,{hi}]: {len(sets)}   low (<=2 openings): {len(low)}\n")

print("=== how many non-flank 5-multiples, in the residue vs in the low set? ===")
allc = Counter(sum(1 for d in c[:-1] if d % 5 == 0) for c in sets)
lowc = Counter(sum(1 for d in c[:-1] if d % 5 == 0) for c in low)
print(f"{'#5-mults':>9} {'all residue':>13} {'share':>8} {'low set':>9} {'share':>8} {'enrichment':>11}")
for k in sorted(allc):
    a = allc[k]; l = lowc.get(k, 0)
    print(f"{k:>9} {a:>13} {100*a/len(sets):>7.2f}% {l:>9} {100*l/len(low):>7.2f}%"
          f" {((l/len(low))/(a/len(sets))) if a else 0:>10.2f}x")
print()
print("=== the fully-self-similar family: ALL non-flank disparities multiples of 5 ===")
ss = [c for c in sets if all(d % 5 == 0 for d in c[:-1])]
ss_low = [c for c in ss if n_open(c) <= 2]
print(f"   {len(ss)} such sets;  {len(ss_low)} of them are low  ({100*len(ss_low)/len(ss):.1f}%)")
print(f"   vs base rate {100*len(low)/len(sets):.3f}%   ->  enrichment {(len(ss_low)/len(ss))/(len(low)/len(sets)):.0f}x")
print()
print("=== the reduction, verified: does (5m1,5m2,5m3,e) behave like (m1,m2,m3) at modulus e? ===")
print(f"{'set':>22} {'e':>4} {'inner (m_i)':>14} {'#open':>6} {'#r with all m_i r mod e in band':>33}")
for c in ss[:10]:
    e = c[-1]; ms = tuple(d//5 for d in c[:-1])
    cnt = sum(1 for r in range(e) if all(5*((mi*r) % e) >= e and 5*((mi*r) % e) <= 4*e for mi in ms))
    print(f"{str(c):>22} {e:>4} {str(ms):>14} {n_open(c):>6} {cnt:>33}")
