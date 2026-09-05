B=7
QT.<T>=QQ[]
def count_aff(Fq):
    from collections import Counter
    c4=Counter()
    for w in Fq: c4[w**4]+=1
    return sum(c4[x**3+B] for x in Fq)
def cy_newpart(p):
    Fp=GF(p); E=EllipticCurve(Fp,[0,B]); aE=p+1-E.order(); LE=1-aE*T+p*T^2
    Ns=[count_aff(GF(p**k,'g'))+1 for k in (1,2,3)]   # +1 smooth point at infinity
    s=[(p**k+1-Ns[k-1]) for k in (1,2,3)]             # power sums sum(alpha^k)
    e=[1]
    for k in range(1,4):
        acc=0
        for i in range(1,k+1): acc+=(-1)**(i-1)*e[k-i]*s[i-1]
        e.append(acc/k)
    coeffs=[1,-e[1],e[2],-e[3],p*e[2],-p**2*e[1],p**3]   # functional eqn for deg 6
    P=sum(coeffs[i]*T^i for i in range(7))
    return aE,LE,P,Ns
for p in [13,43,61,67,79,103,127]:
    if p%3!=1 or B%p==0: continue
    aE,LE,P,Ns=cy_newpart(p)
    q,r=P.quo_rem(LE)
    ql=q.list()
    even = len(ql)==5 and ql[1]==0 and ql[3]==0
    print("p=%-3d a_E=%-4d N_k=%s  new_y=L_Cy/L_E=%s rem=%s  EVEN(t^4+mp t^2+p^2)?%s"
          %(p,aE,Ns,ql,r.list(),even))
    if even:
        m=ql[2]/p
        print("        -> new_y = T^4 + (%s)*p*T^2 + p^2   (m=%s)  [A_new char poly, matches m-law object]"%(m,m))
