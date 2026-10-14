"""At the LARGEST flank (|d| <= e), which movers block the opening k = L-1, L = lcm of denominators?
Derivation: at k = -1 (mod q), residue = (q*c - 7p) mod 8q with rho = d/e = a/q, a = qc+p.
  rho mod 8 in (0,1)  (c=0): blocked iff 7p < q      i.e. rho  <  1/7
  rho mod 8 in (7,8)  (c=7): blocked iff 7p' < q     i.e. |rho| <  1/7
So for |rho| <= 1 the law collapses to:  blocked  <=>  7*|d| < e.   Test it."""
from math import gcd, lcm
import random
def inWay(d,A,e):
    M=8*e; r=(d*A)%M; return min(r,M-r)<e
bad=[]; tot=0; nblock=0
random.seed(11)
for trial in range(300000):
    e=random.randint(1,400)
    ds=[random.randint(-e,e) for _ in range(random.randint(1,7))]
    ds=[d for d in ds if d!=0]
    if not ds: continue
    qs=[e//gcd(abs(d),e) for d in ds]
    L=lcm(*qs); k=L-1; A=8*k+1
    for d in ds:
        tot+=1
        got=inWay(d,A,e); want=(7*abs(d)<e)
        if got: nblock+=1
        if got!=want: bad.append((e,d,k,got,want))
print(f"largest flank, k = lcm-1:  'in the way  <=>  7|d| < e'  over {tot} movers: "
      f"{'HOLDS' if not bad else f'FAILS {len(bad)}'}   ({nblock} actually in the way)")
for b in bad[:6]: print("   ",b)
