B=7
QT.<T>=QQ[]
def count_aff(Fq):
    from collections import Counter
    c4=Counter()
    for w in Fq: c4[w**4]+=1
    return sum(c4[x**3+B] for x in Fq)
for p in [991,1051,1249,1303,2089,2143]:   # N1 addendum primes
    if p%3!=1: continue
    Fp=GF(p); aE=p+1-EllipticCurve(Fp,[0,B]).order(); LE=1-aE*T+p*T^2
    Ns=[count_aff(GF(p**k,'g'))+1 for k in (1,2,3)]
    s=[(p**k+1-Ns[k-1]) for k in (1,2,3)]
    e=[1]
    for k in range(1,4):
        acc=0
        for i in range(1,k+1): acc+=(-1)**(i-1)*e[k-i]*s[i-1]
        e.append(acc/k)
    ny=(QT([1,-e[1],e[2],-e[3],p*e[2],-p**2*e[1],p**3])//LE).list()
    even = ny[1]==0 and ny[3]==0
    m = ny[2]/p if even else None
    print("p=%-5d  A_new char poly coeffs=%s  EVEN?%s  m=%s"%(p,ny,even,m))
