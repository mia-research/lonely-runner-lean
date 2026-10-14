"""Corrected greedy: at each level keep the LONGEST surviving piece, not the first full window.
A full window run needs l >= b + w(b) - 1 ~ 7b/4, which the invariant does not supply; a
truncated run is fine as long as it still covers the next (smaller) modulus."""
from math import gcd
import random, itertools
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def w(b): return U(b)-L(b)+1
def longest_piece(lo,hi,b):
    """longest [a,c] subset of [lo,hi] with every q in it having q%b in [L(b),U(b)]"""
    best=None
    j0=(lo-L(b))//b - 1
    for j in range(j0, j0+ (hi-lo)//b + 3):
        a=max(lo, j*b+L(b)); c=min(hi, j*b+U(b))
        if a<=c and (best is None or c-a > best[1]-best[0]): best=(a,c)
    return best
def greedy(tower):
    lo,hi = L(tower[0]), U(tower[0])
    for b in tower[1:]:
        p=longest_piece(lo,hi,b)
        if p is None: return None
        lo,hi = p
    return lo
def ok(t,q): return all(L(b) <= q % b <= U(b) for b in t)
random.seed(23)
fail=0; n=0; worst=[]
for _ in range(200000):
    k=random.randint(2,6); t=[1]
    for _ in range(k): t.append(t[-1]*random.choice([2,2,3,3,4,5,6,7,8]))
    tower=sorted(set(t[1:]), reverse=True)
    if len(tower)<2: continue
    n+=1
    q=greedy(tower)
    if q is None or not ok(tower,q):
        fail+=1
        if len(worst)<6: worst.append(tower)
print(f"random towers: {n-fail}/{n} {'ALL SUCCEED' if fail==0 else f'{fail} FAIL'}")
for x in worst: print(f"   fail: {x}")
fail2=0; n2=0; w2=[]
for m in (48,72,96,120,144,240,360,480,720,840,1440,2520,5040):
    divs=[d for d in range(2,m+1) if m%d==0]
    for k in (2,3,4,5):
        for c in itertools.combinations(divs,k):
            t=sorted(c, reverse=True)
            if any(t[i] % t[i+1] for i in range(len(t)-1)): continue
            n2+=1
            q=greedy(t)
            if q is None or not ok(t,q):
                fail2+=1
                if len(w2)<6: w2.append(t)
print(f"exhaustive divisor towers: {n2-fail2}/{n2} {'ALL SUCCEED' if fail2==0 else f'{fail2} FAIL'}")
for x in w2: print(f"   fail: {x}")
print("\ninvariant check: is the surviving length always >= the next modulus?")
def trace(tower):
    lo,hi=L(tower[0]),U(tower[0]); out=[(tower[0],hi-lo+1)]
    for b in tower[1:]:
        p=longest_piece(lo,hi,b)
        if p is None: return out+[(b,0)]
        lo,hi=p; out.append((b,hi-lo+1))
    return out
for t in ([16,8,4,2],[64,32,16,8,4],[2520,840,210,42,14]):
    print(f"   {t}: (modulus, surviving length) = {trace(t)}")
