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
    G=None
    for Q in pts:
        if Q is None:continue
        R=Q;k=1
        while R is not None:R=add(R,Q);k+=1
        if k==N:G=Q;break
    orb=[];R=None
    for d in range(1,N):R=add(R,G);orb.append(R)
    return N,np.array([P[0] for P in orb]),np.array([P[1] for P in orb])
def Ufull(p,xs,ys,n):
    d=np.arange(1,n)
    bb,cc=np.meshgrid(np.arange(p),np.arange(p),indexing='ij');bb=bb.ravel();cc=cc.ravel()
    phase=np.exp(2j*math.pi*(np.outer(bb,xs)+np.outer(cc,ys))/p)
    en=np.exp(-2j*math.pi*np.outer(np.arange(n),d)/n)
    return en@phase.T,bb,cc
def m4(p,A,B,reps=200,seed=0):
    n,xs,ys=curve(p,A,B)
    U,bb,cc=Ufull(p,xs,ys,n);nz=(bb!=0)|(cc!=0)
    real=np.mean(np.sum(np.abs(U[:,nz])**4,axis=0))
    rng=np.random.default_rng(seed);cont=[]
    for _ in range(reps):
        perm=rng.permutation(n-1)
        Us,_,_=Ufull(p,xs[perm],ys[perm],n)
        cont.append(np.mean(np.sum(np.abs(Us[:,nz])**4,axis=0)))
    cont=np.array(cont)
    return n,100*(real-cont.mean())/cont.mean(),(real-cont.mean())/cont.std()
print("Doc 17 amicable pair M4 (200-rep control):")
for p,A,B,nm in [(67,0,7,'CM E1'),(79,0,7,'CM E2'),(67,1,8,'nonCM E1'),(79,2,28,'nonCM E2')]:
    n,ex,t=m4(p,A,B)
    sig = "SIGNIF" if abs(t)>2 else "not significant"
    print(f"  {nm:9s} p={p} n={n}: excess {ex:+.4f}%  T={t:+.2f}  [{sig}]")
print("\nDoc claims: E2 CM '+0.3693%, T=+1.63' = definitive proof of CM-accelerated crossover.")
print("Reality: |T|<2 for the CM-positive cell; and doc 14's full sweep shows crossover is UNIVERSAL (CM~=nonCM).")
