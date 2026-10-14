"""The second blocked class -- corrected scope.
residue of p(nk+1) mod nq = n*u + p, u = pk mod q.  blocked iff n*u+p < q or n*u+p > (n-1)q.
For q <= n the low branch forces u=0 and the high branch forces u=q-1, giving
    blocked set = {0} u ({-p^{-1}} iff p+q > n).
(For q > n the branches admit several u and the two-class form is NOT claimed.)"""
from math import gcd
def blocked(p,q,n): 
    return frozenset(k%q for k in range(2*q) if (lambda r: min(r,n*q-r)<q)((p*(n*k+1))%(n*q)))
def inv(p,q): return next(x for x in range(1,q) if (p*x)%q==1)

bad=[]; tot=0
for n in range(3,25):
    for q in range(2,n+1):
        for p in range(1,q):
            if gcd(p,q)!=1: continue
            tot+=1
            want={0} | ({(-inv(p,q))%q} if p+q>n else set())
            if blocked(p,q,n)!=want: bad.append((n,p,q))
print(f"[A] q <= n:  blocked = {{0}} u ({{-p^-1}} iff p+q>n)  -- {tot} cases, "
      f"{'HOLDS' if not bad else f'FAILS {len(bad)}'}")

bad2=[]; tot2=0
for n in range(3,25):
    for q in range(2,4*n):
        for p in range(1,q):
            if gcd(p,q)!=1: continue
            tot2+=1
            if (q-1) in blocked(p,q,n) and not (p==1 and q>=n): bad2.append((n,p,q,sorted(blocked(p,q,n))))
print(f"[B] k ≡ -1 (mod q) blocked  =>  p = 1 AND q >= n  -- {tot2} cases, "
      f"{'HOLDS' if not bad2 else f'FAILS {len(bad2)}'}")
for b in bad2[:6]: print("   counterexample:",b)
print(f"[C] converse: p=1, q>=n  =>  k ≡ -1 blocked : "
      f"{all((q-1) in blocked(1,q,n) for n in range(3,25) for q in range(n,4*n))}")

print()
bad3=[]; tot3=0
for n in range(3,25):
    for q in range(2,n+1):
        for p in range(1,q):
            if gcd(p,q)!=1: continue
            tot3+=1
            if ((q-1) in blocked(p,q,n)) != (p==1 and q==n): bad3.append((n,p,q))
print(f"[B'] q <= n:  k ≡ -1 (mod q) blocked  <=>  p = 1 AND q = n  -- {tot3} cases, "
      f"{'HOLDS' if not bad3 else f'FAILS {len(bad3)}'}")
print("     i.e. within q <= n, the mover 1/n is the ONLY one that blocks the last class.")
