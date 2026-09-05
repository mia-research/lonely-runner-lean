"""
v5: is (1,±2) the tractable "large-q window + small-q explicit" pattern, or the
research-grade fine-grid Diophantine covering?

Findings to confirm/measure:
 (A) e = gcd(2r∓p, q) = q exactly (relation q | 2r∓p). -> grid is FULL 1/q line.
 (B) true X-spacing of the point set {fract(r*odd/2q)} (= gcd over actual points).
 (C) line∩P max X-run vs true spacing; among run<spacing FAILURES: max q, and does
     a witness still exist (so finite explicit covers them)?
 (D) Could a COARSER usable grid come from a sub-window argument? Report n points
     of the line that fall in P (the witness count, exact, smallest-slack s=r+1).
"""
from math import gcd
from fractions import Fraction as F

def frac(x): return x - (x.numerator // x.denominator)
def S(l, p, q, r):
    u = 2*l+1
    return frac(F(r*u, 2*q)), frac(F(p*u, 2*q))
XLO, XHI, YLO, YHI = F(1,6), F(1,2), F(1,6), F(1,3)
def inR(X, Y): return XLO <= X <= XHI and YLO <= Y <= YHI
def cap_R_empty(p, q, r): return all(not inR(*S(l, p, q, r)) for l in range(q))
def in_G(i, j, p, q, r):
    return any((m*r) % q == i % q and (m*p) % q == j % q for m in range(q))
def is_pair(ii, jj, p, q, r):
    if not in_G(ii, jj, p, q, r): return False
    for k in range(-abs(ii), abs(ii)+1):
        for l in range(-abs(jj), abs(jj)+1):
            if (k,l)==(0,0) or (abs(k)==abs(ii) and abs(l)==abs(jj)): continue
            if in_G(k,l,p,q,r): return False
    return True
def in_P(X, Y, p, p2, q, r, s):
    e1=F(r*(s-q),3*q*s); e0=F(p*(s-q),3*q*s); e2=F(p2*(s-q),3*q*s)
    return (X>=F(1,6)-e1 and Y>=F(1,6)-e0 and Y<=F(1,3)+e2 and X<=F(5,6)
            and F(1,3*s)<=(F(5,6)-X)/r+(Y-F(1,6))/p
            and F(1,3*s)<=(F(5,6)-X)/r+(F(1,3)-Y)/p2)
def survivors(ii, jj, qmax):
    out=[]
    for q in range(18,qmax+1):
        for p in range(1,q):
            if 3*p>=q or gcd(p,q)!=1: continue
            for r in range(q+1,(3*q)//2+1):
                if 2*r>=3*q: continue
                if is_pair(ii,jj,p,q,r) and cap_R_empty(p,q,r): out.append((p,q,r))
    return out
def line_run(p, p2, q, r, s, c, slope):
    e1=F(r*(s-q),3*q*s); e0=F(p*(s-q),3*q*s); e2=F(p2*(s-q),3*q*s); inv3s=F(1,3*s)
    best=F(0)
    for n in range(-4,5):
        Lo=[F(1,6)-e1, F(1,6)]; Hi=[F(5,6), F(5,6)]
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
        if hi>lo: best=max(best, hi-lo)
    return best

for (ii,jj) in [(1,2),(1,-2)]:
    survs=survivors(ii,jj,60)
    slope=jj
    # (A) confirm q | (2r∓p)
    relbad=sum(1 for (p,q,r) in survs if (2*r-p if jj==2 else 2*r+p)%q!=0)
    # (B) true X spacing per survivor
    spacings=[]
    for (p,q,r) in survs:
        xs=sorted(set(S(l,p,q,r)[0] for l in range(q)))
        gaps=[xs[i+1]-xs[i] for i in range(len(xs)-1)]+[xs[0]+1-xs[-1]]
        spacings.append((min(gaps), F(1,q), len(xs)))
    spc_eq_invq=sum(1 for (mn,iq,_) in spacings if mn==iq)
    print(f"\n=== ({ii},{jj}): {len(survs)} survivors ===")
    print(f"  (A) relation q|(2r∓p) violations: {relbad}")
    print(f"  (B) min X-gap == 1/q in {spc_eq_invq}/{len(survs)} survivors; "
          f"#distinct-X range {min(s[2] for s in spacings)}..{max(s[2] for s in spacings)}")
    # (C) failures (run < true spacing) — max q + still-exists?
    fail_q=[]; fail_noexist=0; cmp=0
    for (p,q,r) in survs:
        xs=sorted(set(S(l,p,q,r)[0] for l in range(q)))
        gaps=[xs[i+1]-xs[i] for i in range(len(xs)-1)]+[xs[0]+1-xs[-1]]
        spacing=min(gaps)
        X0,Y0=S(0,p,q,r); c=frac(slope*X0-Y0)
        for p2 in range(p+1,q):
            for s in range(r+1,3*q+1):
                cmp+=1
                run=line_run(p,p2,q,r,s,c,slope)
                if run<spacing:
                    fail_q.append(q)
                    exists=any(in_P(*S(l,p,q,r),p,p2,q,r,s) for l in range(q))
                    if not exists: fail_noexist+=1
    if fail_q:
        from collections import Counter
        print(f"  (C) run<spacing: {len(fail_q)}/{cmp} fails; max q = {max(fail_q)}; "
              f"q-hist={dict(sorted(Counter(fail_q).items()))}")
        print(f"      of those, witness still EXISTS in all but {fail_noexist}")
    else:
        print(f"  (C) run>=spacing for ALL {cmp} completions (window argument always works!)")
