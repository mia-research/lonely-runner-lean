"""
v2 of the BHK-mechanism check. Fixes: (1) special-case normalization
{(wi/q)*t}; (2) use ACTUAL segment extent (x-extent H, y-extent V) of line∩P with
p2=q-p FIXED, certify "H>=1/q (horiz pigeonhole) OR V>=2/q (vert) OR special";
(3) report fract(jX - Y) (which line the C-points sit on).
"""
from math import gcd
from fractions import Fraction as F
def frac(x): return x - (x.numerator // x.denominator)
def Cpts(p, q, r):
    return [(frac(F(r*(2*l+1), 2*q)), frac(F(p*(2*l+1), 2*q))) for l in range(q)]
def in_G(i, j, p, q, r):
    return any((m*r) % q == i % q and (m*p) % q == j % q for m in range(q))
def is_pair(ii, jj, p, q, r):
    if not in_G(ii, jj, p, q, r): return False
    for k in range(-abs(ii), abs(ii)+1):
        for l in range(-abs(jj), abs(jj)+1):
            if (k,l)==(0,0) or (abs(k)==abs(ii) and abs(l)==abs(jj)): continue
            if in_G(k,l,p,q,r): return False
    return True
def extents(p, q, r, s, slope):
    """actual x-extent H and y-extent V of (line y=frac(slope*x-c)) ∩ P, p2=q-p."""
    p2 = q - p
    e1=F(r*(s-q),3*q*s); e0=F(p*(s-q),3*q*s); e2=F(p2*(s-q),3*q*s); inv3s=F(1,3*s)
    X0, Y0 = Cpts(p,q,r)[0]; c = frac(slope*X0 - Y0)
    H = V = F(0)
    for n in range(-4,5):
        Lo=[F(1,6)-e1, F(0)]; Hi=[F(5,6), F(1)]
        rhs=F(1,6)-e0+c+n; (Lo if slope>0 else Hi).append(F(rhs,slope))
        rhs=F(1,3)+e2+c+n; (Hi if slope>0 else Lo).append(F(rhs,slope))
        A5=-F(1,r)+F(slope,p); B5=F(5,6*r)+(-c-n-F(1,6))/p-inv3s
        if A5>0: Lo.append(-B5/A5)
        elif A5<0: Hi.append(-B5/A5)
        elif B5<0: continue
        A6=-F(1,r)-F(slope,p2); B6=F(5,6*r)+(F(1,3)+c+n)/p2-inv3s
        if A6>0: Lo.append(-B6/A6)
        elif A6<0: Hi.append(-B6/A6)
        elif B6<0: continue
        lo=max(Lo); hi=min(Hi)
        if hi>lo:
            H=max(H, hi-lo); V=max(V, abs(slope)*(hi-lo))
    return H, V

for (ii, jj, rig_ok) in [(1,2, lambda p,q,r: 2*r-p==2*q),
                          (1,-2, lambda p,q,r: 2*r+p==3*q)]:
    slope = jj
    tot=horiz=vert=spec=none=0
    cvals=set()
    for q in range(18, 81):
        for p in range(1, q):
            if 3*p>=q or gcd(p,q)!=1: continue
            num = 2*q+p if jj==2 else 3*q-p
            if num % 2 != 0: continue
            r = num//2
            if not (q < r) or 2*r >= 3*q: continue
            if not is_pair(ii,jj,p,q,r): continue
            X0,Y0=Cpts(p,q,r)[0]; cvals.add(frac(jj*X0 - Y0))
            for s in range(r+1, 3*q+1):
                tot += 1
                H, V = extents(p,q,r,s,slope)
                i = s - r
                if jj==2 and p==2 and i==1: spec += 1
                elif H >= F(1,q): horiz += 1
                elif V >= F(2,q): vert += 1
                else: none += 1
    print(f"=== ({ii},{jj}) ===")
    print(f"  completions={tot}; H>=1/q:{horiz}  V>=2/q:{vert}  special:{spec}  NONE:{none}")
    print(f"  fract({jj}X - Y) values across survivors: {sorted(float(x) for x in cvals)}")

# fixed special-case check: positions {(wi/q)*t}
print("\n=== p=2,i=1 special (FIXED normalization {(wi/q)*(j+1/2)}) ===")
def circdist(x):
    f=frac(x); return min(f, 1-f)
bad=checked=0
for q in range(9, 81):
    if q % 2 == 0: continue
    w=[2,q-2,q,q+1,q+2]
    for j in range(q):
        if F(1,6) <= F(2*j+1,q) <= F(1,3):
            t=F(2*j+1,2); checked+=1
            if not all(circdist(F(wi,q)*t) >= F(1,6) for wi in w): bad+=1
            break
print(f"  checked {checked} odd q in [9,80]; t=j+1/2 NOT a 012345-gap in {bad}")
