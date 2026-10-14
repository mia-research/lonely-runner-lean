"""The actual scale recursion, taken at a RESONANT flank e = n*f.
Claim (algebra):  for d = n*m',  d clear at (e=n f, a)  <=>  m' clear at (f, a).
So A = n*A' imposes exactly the original problem's conditions for A' at flank f, same a.
The only genuinely new conditions are B's, at modulus n^2 f."""
from math import gcd
from itertools import combinations
N=8
def clear(d,e,a,n=N): return e<=(d*a)%(n*e)<=(n-1)*e

print("=== 1. the self-similarity, exactly ===")
bad=0; tot=0
for f in range(1,26):
    e=N*f
    for m in range(1,40):
        d=N*m
        for j in range(0,60):
            a=N*j+1; tot+=1
            if clear(d,e,a)!=clear(m,f,a): bad+=1
print(f"    checked {tot} triples (f<26, m'<40, j<60):  mismatches = {bad}")
print("    => at a resonant flank e=n f, the resonant disparities pose EXACTLY the")
print("       original problem for A/n at flank f, with the SAME opening numerator a.")

print()
print("=== 2. what the descent costs: the A-part fixes a mod n*f, B needs a mod n^2 f ===")
bad=0;tot=0
for f in range(1,20):
    e=N*f
    for m in range(1,25):
        d=N*m
        for a0 in range(1,N*f,1):
            if a0%N!=1: continue
            vals={clear(d,e,a0+t*N*f) for t in range(N)}
            tot+=1
            if len(vals)!=1: bad+=1
print(f"    resonant condition constant on a mod n*f ?  counterexamples = {bad} of {tot}")
print("    => each solution of the sub-problem is a residue class mod n*f with n lifts mod n^2 f;")
print("       B must be cleared by one of those n lifts.  That is the whole of the descent's cost.")
