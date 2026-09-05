# ---- Doc 12: y-only deficit scaling. Reproduce a few rows + INTERROGATE the control. ----
import numpy as np, cmath, math
from sympy import legendre_symbol, isprime, nextprime

def curve_order_and_gen(p,A,B):
    def add(P,Q):
        if P is None:return Q
        if Q is None:return P
        x1,y1=P;x2,y2=Q
        if x1==x2 and (y1+y2)%p==0:return None
        if P==Q:m=(3*x1*x1+A)*pow(2*y1,-1,p)%p
        else:m=(y2-y1)*pow((x2-x1)%p,-1,p)%p
        x3=(m*m-x1-x2)%p;y3=(m*(x1-x3)-y1)%p;return(x3,y3)
    pts=[None]+[(x,y) for x in range(p) for y in range(p) if (y*y-(x**3+A*x+B))%p==0]
    N=len(pts)
    return N,add,pts

def orbit(p,A,B,add,G,n):
    orb=[];R=None
    for d in range(1,n):
        R=add(R,G);orb.append(R)
    return orb

def yonly_deficit(p,A,B,nshuf=50,seed=0):
    N,add,pts=curve_order_and_gen(p,A,B)
    n=N
    if not isprime(n): return None
    # generator
    G=None
    for Q in pts:
        if Q is None:continue
        R=Q;k=1
        while R is not None:R=add(R,Q);k+=1
        if k==n:G=Q;break
    orb=orbit(p,A,B,add,G,n)
    ys=[P[1] for P in orb]  # y_d for d=1..n-1
    # U(1,0,c)=sum_d e_p(c y_d) e_n(-d), for c=1..p-1
    dvec=np.arange(1,n)
    en=np.exp(-2j*math.pi*dvec/n)
    ymat=np.array(ys)
    realmag=[]
    for c in range(1,p):
        U=np.sum(np.exp(2j*math.pi*c*ymat/p)*en)
        realmag.append(abs(U))
    realmag=np.array(realmag)
    rng=np.random.default_rng(seed)
    shufmags=[]
    for _ in range(nshuf):
        yp=rng.permutation(ymat)
        for c in range(1,p):
            U=np.sum(np.exp(2j*math.pi*c*yp/p)*en)
            shufmags.append(abs(U))
    shufmags=np.array(shufmags)
    rmean=realmag.mean(); smean=shufmags.mean()
    deficit=100*(rmean-smean)/smean
    # low tail r<0.5 where r=|U|/sqrt(n-1)
    rlow=100*np.mean(realmag/math.sqrt(n-1)<0.5)
    slow=100*np.mean(shufmags/math.sqrt(n-1)<0.5)
    return n,rmean,smean,deficit,rlow,slow

# reproduce their non-CM rows (they pick 'first prime-order non-CM curve, A!=0')
def first_nonCM(p):
    for A in range(1,p):
        for B in range(0,p):
            if (4*A**3+27*B**2)%p==0: continue
            N,_,_=curve_order_and_gen(p,A,B)
            if isprime(N):
                return A,B,N
    return None
print("p  | A,B     | n   | realMean | shufMean | deficit% | realLow% | shufLow%")
for p in [43,67,103,163]:
    A,B,N=first_nonCM(p)
    n,rm,sm,dfc,rl,sl=yonly_deficit(p,A,B)
    print(f"{p:3d}| {A},{B:<4d}| {n:3d} | {rm:8.4f} | {sm:8.4f} | {dfc:+7.2f} | {rl:6.2f} | {sl:6.2f}")
