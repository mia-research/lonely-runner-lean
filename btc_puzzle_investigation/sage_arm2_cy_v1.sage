# C_y: w^4 = x^3 + B, genus 3.  New part = L_{C_y}/L_E, degree 4 = A_new.
# #C_y(F_q) via quartic char: #{w:w^4=r} = sum_{chi^4=1} chi(r).  Get L-poly from k=1,2,3 counts.
B=7
QT.<T>=QQ[]
def count_Cy(q_field):
    # affine count of w^4 = x^3+B over the field, + points at infinity
    Fq=q_field
    # precompute #4th-roots of each value
    from collections import Counter
    cnt4=Counter()
    for w in Fq: cnt4[w**4]+=1
    aff=sum(cnt4[(x**3+B)] for x in Fq)
    # projective closure of w^4=x^3+B (weighted): points at infinity of a smooth model of a genus-3
    # superelliptic w^4=cubic: 1 point at infinity (since gcd(4,3)=1). Use smooth-count via functional eqn instead:
    return aff
def cy_newpart(p):
    Fp=GF(p); E=EllipticCurve(Fp,[0,B]); aE=p+1-E.order(); LE=1-aE*T+p*T^2
    # smooth projective genus-3 curve point counts N_k = #C(F_p^k)
    # Use the smooth model via Sage curve over each F_p^k
    Ns=[]
    for k in (1,2,3):
        Fk=GF(p**k,'g')
        P2=ProjectiveSpace(Fk,2,'X,Y,Z'); X,Y,Z=P2.gens()
        C=Curve(Y^4-X^3*Z-B*Z^4,P2)
        Ns.append(C.count_points(1)[0] if False else len(C.rational_points()))
    g=3
    # L-poly: numerator P(T) deg 2g=6, N_k = p^k+1 - sum alpha_i^k.  power sums s_k = p^k+1-N_k.
    s=[ (p**k+1-Ns[k-1]) for k in (1,2,3)]
    # Newton -> e_1..e_3 ; use functional eqn for e_4,e_5,e_6: e_{6-i}=p^{3-i} e_i
    e=[1]
    for k in range(1,4):
        acc=0
        for i in range(1,k+1): acc+=(-1)**(i-1)*e[k-i]*s[i-1]
        e.append(acc/k)
    e4=p*e[2]; e5=p**2*e[1]; e6=p**3*e[0]
    ecoef=[e[0],-e[1],e[2],-e[3],e4,-e5,e6]
    P=sum(ecoef[i]*T**i for i in range(7))   # note sign convention: build P(T)=prod(1-alpha T)
    # Actually P(T)=1 - s1 T + ... ; use e with alternating already. Rebuild cleanly:
    P=QT(1)
    coeffs=[1, -e[1], e[2], -e[3], e4, -e5, e6]
    P=sum(coeffs[i]*T^i for i in range(7))
    return aE,LE,P,Ns
for p in [13,43,61,67]:
    if p%3!=1 or B%p==0: continue
    aE,LE,P,Ns=cy_newpart(p)
    q,r=P.quo_rem(LE)
    print("p=%d a_E=%d  N_k=%s"%(p,aE,Ns))
    print("   L_Cy=%s"%P.list())
    print("   new_y = L_Cy/L_E = %s (rem %s)"%(q.list(),r.list()))
    if r==0:
        print("   new_y factor:",[(f.list(),m) for f,m in q.factor()],"  even in T? ", q.list()[1]==0 and q.list()[3]==0)
