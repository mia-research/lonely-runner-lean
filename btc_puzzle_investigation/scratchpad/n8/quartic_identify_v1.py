"""
Identify the quartic. G(x) = y(P+S)y(S-P) = kappa * prod_i(x-e_i)/(x-u)^3,
so chi2(G(c)) = chi2(kappa)*chi2(q_R(c)) with q_R(c) = (c-u)*prod_i(c-e_i)
                                        = prod_{2Q=R} (c - x(Q)).
Standard: x(2Q) = (x^4 - 2Ax^2 - 8Bx + A^2)/(4(x^3+Ax+B)), so
   q_R(x) = x^4 - 4 x_R x^3 - 2A x^2 - (8B + 4A x_R) x + (A^2 - 4B x_R).
Measured here:  h1(R),  Sigma2 = sum_c chi2(G(c)),  T := sum_c chi2(q_R(c)),  chi2(kappa),
and the hand relation   Sigma1 + Sigma2 = h1(R) - 1   (with Sigma1 = 0 already verified).
Exact integers only.
"""
import sys
sys.path.insert(0,'scratchpad/n8')
from pencil_vanishing_v1 import leg, pts, add, neg, m2, s2, n2, pw2, add2

def run(p,A,B,nshow=4):
    E=pts(p,A,B); n=len(E)+1
    if n%2==0: return
    r=next(u for u in range(2,p) if leg(u,p)==-1)
    sq={}
    for y0 in range(p):
        for y1 in range(p): sq.setdefault(m2((y0,y1),(y0,y1),p,r),[]).append((y0,y1))
    def half(R):
        k=(n+1)//2; T=None; b=R
        while k:
            if k&1: T=add(T,b,p,A)
            b=add(b,b,p,A); k>>=1
        return T
    t = p+1-n
    print(f"--- p={p} A={A} B={B} n={n} t={t}  (E trace t) ---")
    for R in E[:nshow]:
        Q0=half(R); u=Q0[0]; Q02=((Q0[0],0),(Q0[1],0))
        # h1(R)
        h1=0
        for M in E:
            Mm=add(R,neg(M,p),p,A)
            if Mm is None: continue
            h1+=leg(M[1],p)*leg(Mm[1],p)
        # Sigma2 and kappa
        S2sum=0; kappa=None
        xR=R[0]
        qR=lambda c: (pow(c,4,p) - 4*xR*pow(c,3,p) - 2*A*c*c - (8*B+4*A*xR)*c + (A*A-4*B*xR)) % p
        Tsum=sum(leg(qR(c),p) for c in range(p))
        for c in range(p):
            rhs=(c*c%p*c + A*c + B)%p
            ys=sq.get((rhs%p,0))
            P2=((c,0),ys[0])
            Pl=add2(Q02,P2,p,A,r); Pm=add2(Q02,(P2[0],n2(P2[1],p)),p,A,r)
            if Pl is None or Pm is None: continue
            pr=m2(Pl[1],Pm[1],p,r); assert pr[1]==0
            S2sum+=leg(pr[0],p)
            if kappa is None and qR(c)%p!=0:
                # G(c) = kappa * qR(c)/(c-u)^4   (multiplied num & den by (c-u))
                num=pr[0]*pow(c-u,4,p)%p
                kappa=num*pow(qR(c),-1,p)%p
        print(f"  R={R}  h1={h1:4d}  Sigma2={S2sum:4d}  h1-1={h1-1:4d}  match={S2sum==h1-1}"
              f" | T=sum chi2(qR)={Tsum:4d}  chi2(kappa)={leg(kappa,p):+d}"
              f"  chi2(k)*T={leg(kappa,p)*Tsum:4d}  -1-t={-1-t:4d}")

for (p,A,B) in [(19,0,3),(17,1,5),(23,1,4),(29,2,1)]: run(p,A,B)
