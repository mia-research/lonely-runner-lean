#!/usr/bin/env python3
"""
Vector 1 (toy scale): Fourier transform over F_n^x = (Z[omega]/pi_n)^x of the set of
SMALL-PRIME-SUPPORT integers, testing whether smooth integers have larger amplitude at
particular multiplicative modes (the user's 'small prime support modes survive' idea).
Toy n (prime =1 mod 3) so the F_n discrete log is feasible; secp n is out of reach.
Reports amplitudes vs a matched-random-set null. No verdict -- numbers only.
"""
import cmath, math, random
import sympy
n=15013  # prime, =1 mod 3
assert sympy.isprime(n) and n%3==1
g=sympy.primitive_root(n)
# discrete log table
ind={}
cur=1
for e in range(n-1):
    ind[cur]=e; cur=cur*g%n
def chi(a,d): return cmath.exp(2j*math.pi*a*ind[d%n]/(n-1))
# small-prime-support integers in [1,n-1]: all prime factors <= B
B=13
smalls=[d for d in range(2,n) if max(sympy.factorint(d)) <= B]
print(f"n={n}, F_n^x order {n-1}, generator {g}; small-support (primes<= {B}) integers: {len(smalls)}")
# spectrum: amplitude |sum chi_a(d)| over the smooth set, for low modes a
def spectrum(S,amax=40):
    return [abs(sum(chi(a,d) for d in S))/len(S) for a in range(amax)]
sp=spectrum(smalls)
# null: random subsets of same size, many draws -> mean+max per mode
rng=random.Random(1)
allints=list(range(2,n))
NULL=200
nullsp=[[] for _ in range(len(sp))]
for _ in range(NULL):
    R=rng.sample(allints,len(smalls))
    s=spectrum(R,len(sp))
    for a in range(len(sp)): nullsp[a].append(s[a])
import statistics
print(f"\n{'mode a':>7}{'smooth |A|':>12}{'null mean':>11}{'null max':>10}{'z':>7}")
flagged=[]
for a in range(1,len(sp)):
    mu=statistics.mean(nullsp[a]); sd=statistics.pstdev(nullsp[a]) or 1e-9
    z=(sp[a]-mu)/sd
    if z>3: flagged.append((a,z))
    if a<=12 or z>3:
        print(f"{a:>7}{sp[a]:>12.4f}{mu:>11.4f}{max(nullsp[a]):>10.4f}{z:>7.1f}{'  <-' if z>3 else ''}")
# the cubic mode: a = (n-1)/3 (order-3 char = chi_-3 analog) -- CM-relevant
acub=(n-1)//3; asex=(n-1)//6
for nm,a in [('cubic (n-1)/3',acub),('sextic (n-1)/6',asex),('quadratic (n-1)/2',(n-1)//2)]:
    mu=statistics.mean(nullsp[a] if a<len(nullsp) else [0]) if a<len(nullsp) else None
    val=abs(sum(chi(a,d) for d in smalls))/len(smalls)
    # null for this specific mode
    ns=[abs(sum(chi(a,d) for d in rng.sample(allints,len(smalls))))/len(smalls) for _ in range(NULL)]
    z=(val-statistics.mean(ns))/(statistics.pstdev(ns) or 1e-9)
    print(f"  {nm:20} mode a={a}: smooth|A|={val:.4f} null={statistics.mean(ns):.4f} z={z:.1f}{'  <-' if z>3 else ''}")
print(f"\nflagged modes (z>3): {flagged if flagged else 'none in low band'}")
