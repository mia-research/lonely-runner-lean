import sys
def PR(*a): print(*a); sys.stdout.flush()
R.<t> = QQ[]
PR("p   | pmod4 | b1(trace) | b2 | b2/p | b2%p==0? | p-rank(A_new) | verdict")
for p in (19,23,31,43, 13,29,37,53):
    B=7
    E=EllipticCurve(GF(p),[0,B]); ap=p+1-E.order()
    K=FunctionField(GF(p),'x'); x=K.gen()
    Rt=PolynomialRing(K,'S'); Sv=Rt.gen()
    L=K.extension(Sv**4-(x**3+B),'w')
    PC=R(L.L_polynomial()); PE=R(1-ap*t+p*t**2)
    Pn,rem=PC.quo_rem(PE)
    if rem!=0: PR("p=%d rem!=0"%p); continue
    c=Pn.list()+[0]*(5-len(Pn.list()))
    b1=-c[1]; b2=c[2]; b3=-c[3]
    # p-rank of A_new = number of unit roots of P_new mod p (Newton). ss <=> b1=b3=0 and b2=0 mod p.
    ss = (b1==0 and b3==0 and (b2%p==0))
    PR("%-3d | %d     | %-9s | %-4s | %-5s | %-8s | %-13s | %s"
       %(p,p%4,b1,b2,(QQ(b2)/p if b2%p==0 else "-"),b2%p==0,
         "0 (ss)" if ss else "≥1", "SUPERSINGULAR" if ss else "ordinary/other"))
