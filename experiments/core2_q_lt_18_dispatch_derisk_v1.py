"""De-risk the core2_q_lt_18 finite dispatch (6-runner part-2 core).
Space: p in {1,2}, q in [7,17], gcd(p,q)=1, 6p<q, q<r<2q.
Classification is IDENTICAL to core_q_lt_18 (same h_nogood rectangle): a triple is
- diagonal if r=p+q       (-> part6_w)
- R-killable if some l puts C(l) in R=[1/6,1/2]x[1/6,1/3]   (-> exc_Rkill, abstract, reusable)
- P-killable if some l puts C(l) in pentagon P for all valid s  (-> exc_Pkill2)
- else "needs v4-exclusion" (-> exc_v4kill2, TODO) or genuinely hard.
"""
from math import gcd
from fractions import Fraction as F

def fract(num, den): return F(num % den, den)
def in_R(X, Y): return F(1,6) <= X <= F(1,2) and F(1,6) <= Y <= F(1,3)

def in_P(X, Y, p, q, r, s):
    ca=F(r*(s-q),3*q*s); cb=F(p*(s-q),3*q*s); cc=F((q-p)*(s-q),3*q*s)
    if not (F(1,6)-ca <= X): return False
    if not (F(1,6)-cb <= Y): return False
    if not (Y <= F(1,3)+cc): return False
    if not (X <= F(5,6)): return False
    if not (F(1,3*s) <= (F(5,6)-X)/r + (Y-F(1,6))/p): return False
    if not (F(1,3*s) <= (F(5,6)-X)/r + (F(1,3)-Y)/(q-p)): return False
    return True

def valid_s(q,r,cap=300):
    out=[]; s=r+1
    while s<=cap and len(out)<40:
        if gcd(s,q)==1: out.append(s)
        s+=1
    return out

def R_witness(p,q,r):
    for l in range(0,2*q):
        X=fract(r*(2*l+1),2*q); Y=fract(p*(2*l+1),2*q)
        if in_R(X,Y): return l
    return None

def P_witness(p,q,r):
    ss=valid_s(q,r)
    if not ss: return None
    for l in range(0,2*q):
        X=fract(r*(2*l+1),2*q); Y=fract(p*(2*l+1),2*q)
        if all(in_P(X,Y,p,q,r,s) for s in ss): return l
    return None

counts={'diag':0,'R':0,'P':0,'other':0}
other=[]; diags=[]
for q in range(7,18):
    for p in (1,2):
        if 6*p>=q: continue
        if gcd(p,q)!=1: continue
        for r in range(q+1, 2*q):
            if r==p+q:
                counts['diag']+=1; diags.append((p,q,r)); continue
            if R_witness(p,q,r) is not None:
                counts['R']+=1
            elif P_witness(p,q,r) is not None:
                counts['P']+=1
            else:
                counts['other']+=1; other.append((p,q,r))

print("core2_q_lt_18 finite dispatch (p in {1,2}, q in [7,17], 6p<q, gcd=1, q<r<2q):")
print("  counts:", counts)
print("  diagonals (-> part6_w):", diags)
print("  'other' (need v4-exclusion exc_v4kill2 or hard):")
for t in other: print("   ", t)
