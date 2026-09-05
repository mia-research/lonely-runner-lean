from math import gcd
from fractions import Fraction as F

# Reduced speeds: w0=p, w1=q-p, w2=q, w3=r, w4=s (drop common g; conditions scale-invariant).
# C-point at index l: X = fract(r*(2l+1)/(2q)), Y = fract(p*(2l+1)/(2q)).
def fract(num, den):
    return F(num % den, den)

def in_R(X, Y):
    return F(1,6) <= X <= F(1,2) and F(1,6) <= Y <= F(1,3)

# Exact Lean pentagon pent_no_good (h39..h42b), with w0=p,w1=q-p,w2=q,w3=r,w4=s:
#  corr_a = r*(s-q)/(3*q*s)   [= w3(w4-w2)/(3 w2 w4)]
#  corr_b = p*(s-q)/(3*q*s)
#  corr_c = (q-p)*(s-q)/(3*q*s)
#  h39: 1/6 - corr_a <= X
#  h40: 1/6 - corr_b <= Y
#  h41: Y <= 1/3 + corr_c
#  hxle: X <= 5/6
#  h42a: 1/(3s) <= (5/6 - X)/r + (Y - 1/6)/p
#  h42b: 1/(3s) <= (5/6 - X)/r + (1/3 - Y)/(q-p)
def in_P(X, Y, p, q, r, s):
    corr_a = F(r*(s-q), 3*q*s)
    corr_b = F(p*(s-q), 3*q*s)
    corr_c = F((q-p)*(s-q), 3*q*s)
    if not (F(1,6) - corr_a <= X): return False
    if not (F(1,6) - corr_b <= Y): return False
    if not (Y <= F(1,3) + corr_c): return False
    if not (X <= F(5,6)): return False
    if not (F(1,3*s) <= (F(5,6)-X)/r + (Y-F(1,6))/p): return False
    if not (F(1,3*s) <= (F(5,6)-X)/r + (F(1,3)-Y)/(q-p)): return False
    return True

# For a triple, "killable by P" = exists l such that C(l) in P(s) for ALL valid s>r.
# Pentagon is most restrictive at smallest s. We test against a set of representative s
# (smallest few valid s, and a large s) — require some single l works for ALL of them.
def valid_s_list(q, r, cap=400):
    out=[]
    s=r+1
    while s<=cap and len(out)<60:
        if gcd(s,q)==1:
            out.append(s)
        s+=1
    return out

rows=[]
for q in range(5,18):
    for p in range(1,q):
        if 3*p>=q: continue
        if gcd(p,q)!=1: continue
        for r in range(q+1,2*q):
            if gcd(r,q)!=1: continue
            diagonal=(r==p+q)
            den=2*q
            pts=[(l, fract(r*(2*l+1),den), fract(p*(2*l+1),den)) for l in range(2*q)]
            hitsR = any(in_R(X,Y) for (_,X,Y) in pts)
            slist = valid_s_list(q,r)
            # an l kills via P if it lands in P(s) for every valid s in slist
            killP_l = None
            for (l,X,Y) in pts:
                if all(in_P(X,Y,p,q,r,s) for s in slist):
                    killP_l=l; break
            if hitsR: st="R"
            elif diagonal: st="DIAG"
            elif killP_l is not None: st="P"
            else: st="HARD"
            rows.append((q,p,r,diagonal,hitsR,st))

from collections import Counter
c=Counter(r[5] for r in rows)
print("total:",len(rows),"counts:",dict(c))
print("\nHARD (not R, not DIAG, not killable by exact P for all s):")
for q,p,r,diag,hitsR,st in rows:
    if st=="HARD":
        print(f"  q={q} p={p} r={r}  v1=p/q={p}/{q} (<=1/6: {6*p<=q})")
