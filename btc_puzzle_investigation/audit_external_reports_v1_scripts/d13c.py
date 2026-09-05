import numpy as np, math
from sympy import isprime
def curve(p,A,B):
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
    if not isprime(N):return None
    G=next(Q for Q in pts if Q is not None)  # placeholder
    for Q in pts:
        if Q is None:continue
        R=Q;k=1
        while R is not None:R=add(R,Q);k+=1
        if k==N:G=Q;break
    orb=[];R=None
    for d in range(1,N):R=add(R,G);orb.append(R)
    return N,np.array([P[0] for P in orb]),np.array([P[1] for P in orb])
def Utensor(p,xs,ys,n):
    d=np.arange(1,n)
    bb,cc=np.meshgrid(np.arange(p),np.arange(p),indexing='ij');bb=bb.ravel();cc=cc.ravel()
    phase=np.exp(2j*math.pi*(np.outer(bb,xs)+np.outer(cc,ys))/p)
    en=np.exp(-2j*math.pi*np.outer(np.arange(n),d)/n)
    return en@phase.T,bb,cc
def m4_test(p,A,B,seed=0,reps=30):
    r=curve(p,A,B)
    if r is None:return None
    n,xs,ys=r
    U,bb,cc=Utensor(p,xs,ys,n)
    nz=(bb!=0)|(cc!=0)
    M4_real=np.mean(np.sum(np.abs(U[:,nz])**4,axis=0))
    rng=np.random.default_rng(seed);cont=[]
    for _ in range(reps):
        perm=rng.permutation(n-1)
        Us,_,_=Utensor(p,xs[perm],ys[perm],n)
        cont.append(np.mean(np.sum(np.abs(Us[:,nz])**4,axis=0)))
    cont=np.array(cont)
    return n,100*(M4_real-cont.mean())/cont.mean(),(M4_real-cont.mean())/cont.std()
print("p    type   n    M4excess%   T")
for p,A,B,typ in [(43,0,7,'CM'),(43,1,3,'nonCM'),(67,0,7,'CM'),(139,0,7,'CM'),(163,0,7,'CM'),(163,1,4,'nonCM')]:
    res=m4_test(p,A,B)
    if res is None: print(f"{p:4d} {typ:6s} (order not prime — skip)");continue
    n,ex,t=res
    print(f"{p:4d} {typ:6s} {n:4d}  {ex:+8.3f}   {t:+.2f}")
