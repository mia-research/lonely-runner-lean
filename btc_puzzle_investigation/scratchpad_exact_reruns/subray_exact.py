# EXACT-DATA (mpmath 25dps) rerun of the sub-Rayleigh deficit: M1=mean(|U|/sqrt(mean|U|^2)), char vs random.
import mpmath as mp, random
mp.mp.dps=25
def egcd(a,b):
    if b==0:return(a,1,0)
    g,x,y=egcd(b,a%b);return(g,y,x-(a//b)*y)
def inv(a,m):return egcd(a%m,m)[1]%m
def ec_add(P,Q,a,p):
    if P is None:return Q
    if Q is None:return P
    (x1,y1),(x2,y2)=P,Q
    if x1==x2 and (y1+y2)%p==0:return None
    l=((3*x1*x1+a)*inv(2*y1,p) if P==Q else (y2-y1)*inv((x2-x1)%p,p))%p
    x3=(l*l-x1-x2)%p;return(x3,(l*(x1-x3)-y1)%p)
def isprime(m):
    i=2
    while i*i<=m:
        if m%i==0:return False
        i+=1
    return m>=2
for p,A,B in [(43,0,7),(67,0,7)]:
    pts=[(x,y) for x in range(p) for y in range(p) if (y*y-x*x*x-A*x-B)%p==0]
    n=len(pts)+1
    if not isprime(n): continue
    G=pts[0];P=[None]*n;Q=None
    for d in range(1,n):Q=ec_add(Q,G,A,p);P[d]=Q
    wp=2*mp.pi/p; wn=2*mp.pi/n
    BC=[(b,c) for b in range(p) for c in range(p) if not(b==0 and c==0)]
    # precompute exp phases per (b,c,d)
    E=[[mp.e**(1j*wp*((b*P[d][0]+c*P[d][1])%p)) for d in range(1,n)] for (b,c) in BC]
    def M1_of(gvals):
        # mean|U|^2 exact rational: (p^2(n-1) - |U(0,0)|^2)/(p^2-1); |U(0,0)|=|sum g|
        U0=sum(gvals); m0sq=abs(U0)**2
        m2=(mp.mpf(p)**2*(n-1)-m0sq)/(p*p-1)
        s=mp.mpf(0)
        for row in E:
            U=sum(gvals[i]*row[i] for i in range(n-1))
            s+=abs(U)
        return (s/len(BC))/mp.sqrt(m2)
    # character g_d = e_n(-a0 d), a0=1
    gc=[mp.e**(-1j*wn*1*d) for d in range(1,n)]
    M1c=M1_of(gc)
    rng=random.Random(3); nulls=[]
    for _ in range(40):
        gr=[mp.e**(1j*mp.mpf(rng.random())*2*mp.pi) for _ in range(1,n)]
        nulls.append(M1_of(gr))
    nm=sum(nulls)/len(nulls)
    import math
    nsd=math.sqrt(sum((float(x)-float(nm))**2 for x in nulls)/len(nulls))
    deficit=1-float(M1c)/float(nm)
    z=(float(M1c)-float(nm))/nsd if nsd>0 else 0
    rayleigh=float(mp.sqrt(mp.pi/4))
    print(f"p={p} n={n}: M1_char={mp.nstr(M1c,10)}  null mean={mp.nstr(nm,10)} sd={nsd:.5f}  Rayleigh={rayleigh:.6f}")
    print(f"        deficit = 1 - M1c/null = {deficit*100:+.4f}%   z(char vs null) = {z:+.2f}   {'DEFICIT (char below null)' if z<-1 else 'no deficit'}")
