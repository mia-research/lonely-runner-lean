"""The second blocked class.
residue of p(nk+1) mod nq is n*(pk mod q) + p.  Write u = pk mod q, 0 <= u < q.
  blocked-low :  n*u + p < q        <=>  u = 0        (since 0 < p < q)
  blocked-high:  n*u + p > (n-1)q   <=>  u = q-1 AND p + q > n
So a mover p/q blocks k ≡ 0 (mod q) ALWAYS, and a SECOND class k ≡ -p^{-1} (mod q)
exactly when p + q > n.  Covering the class k ≡ -1 (mod q) needs p^{-1} = 1, i.e. p = 1,
and then p + q > n forces q > n - 1, i.e. q >= n."""
from math import gcd
def blocks(p,A,q,n):
    M=n*q; r=(p*A)%M; return min(r,M-r)<q
def inv(p,q): return next(x for x in range(1,q) if (p*x)%q==1)
bad=[]
for n in range(3,17):
    for q in range(2,4*n):
        for p in range(1,q):
            if gcd(p,q)!=1: continue
            got=frozenset(k%q for k in range(2*q) if blocks(p,n*k+1,q,n))
            want={0} | ({(-inv(p,q))%q} if p+q>n else set())
            if got!=want: bad.append((n,p,q,sorted(got),sorted(want)))
print(f"'blocked set = {{0}} u {{-p^-1}} iff p+q>n' : {'HOLDS' if not bad else 'FAILS'}"
      f"  over n=3..16, q<4n  ({len(bad)} mismatches)")
for b in bad[:5]: print("   ",b)
print()
for n in (5,7,8,9,11,12):
    who=[(p,q) for q in range(2,3*n) for p in range(1,q) if gcd(p,q)==1
         and (k:=(-inv(p,q))%q)==(q-1) and p+q>n]
    qs=sorted({q for _,q in who})
    print(f"n={n:2d}: movers blocking k ≡ -1 (mod q) are {who[:4]}{'...' if len(who)>4 else ''}"
          f"  -> always p=1, and min q = {min(qs)} = n ({min(qs)==n})")
