import numpy as np, math
from sympy import isprime, legendre_symbol
def curve(p,A,B,want=None):
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
    return N,np.array([P[0] for P in orb]),np.array([P[1] for P in orb]),add,pts

def Ufull(p,xs,ys,n):
    d=np.arange(1,n)
    bb,cc=np.meshgrid(np.arange(p),np.arange(p),indexing='ij');bb=bb.ravel();cc=cc.ravel()
    phase=np.exp(2j*math.pi*(np.outer(bb,xs)+np.outer(cc,ys))/p)
    en=np.exp(-2j*math.pi*np.outer(np.arange(n),d)/n)
    return en@phase.T,bb,cc

print("=== Doc 18: LINEAR shear x->x+s y : total M4 EXACT invariance ===")
p,A,B=79,2,28
n,xs,ys,_,_=curve(p,A,B)
base=None
for s in [0,1,10,37,78]:
    xp=(xs+s*ys)%p
    U,bb,cc=Ufull(p,xp,ys,n)
    nz=(bb!=0)|(cc!=0)
    tot=np.sum(np.abs(U[:,nz])**4)
    if base is None: base=tot
    print(f"  s={s:3d}: total M4 = {tot:.6f}   reldiff vs s=0 = {abs(tot-base)/base:.2e}")

print("\n=== Doc 19: NONLINEAR shear x->x+s y^2 : L2 preserved, M4 broken ===")
p,A,B=43,0,7
n,xs,ys,_,_=curve(p,A,B)
U0,bb,cc=Ufull(p,xs,ys,n); nz=(bb!=0)|(cc!=0)
tot0=np.sum(np.abs(U0[:,nz])**4)
L2_0=np.sum(np.abs(U0)**2,axis=0)
for s in [0,1,2,5]:
    xp=(xs+s*ys**2)%p
    U,bb,cc=Ufull(p,xp,ys,n)
    tot=np.sum(np.abs(U[:,nz])**4)
    L2=np.sum(np.abs(U)**2,axis=0)
    print(f"  s={s}: total-M4 delta = {100*(tot-tot0)/tot0:+.2f}%   maxL2 dev from n(n-1) = {np.max(np.abs(L2[nz]-n*(n-1))):.2e}")

print("\n=== Doc 15 Exp2: beta-orbits satisfy Semaev S3=0 (CM) ; random/nonCM don't ===")
def S3(x1,x2,x3,A,B,p):
    return ((x1-x2)**2*x3**2 - 2*((x1+x2)*(x1*x2+A)+2*B)*x3 + ((x1*x2-A)**2-4*B*(x1+x2)))%p
# E1: y^2=x^3+7 over F_67, beta=29 (cube root of 1 mod 67)
p=67;A=0;B=7;beta=29
print("  beta^3 mod 67 =",pow(beta,3,p))
n,xs,ys,add,pts=curve(p,A,B)
# beta-orbits on x-coords: {x, beta x, beta^2 x}
xset=set(int(x) for x in xs); seen=set(); good=0;tot=0
for x in list(xset):
    if x in seen:continue
    o=[x,(beta*x)%p,(beta*beta*x)%p]
    if len(set(o))<3: continue
    for t in o: seen.add(t)
    tot+=1
    if S3(o[0],o[1],o[2],A,B,p)==0: good+=1
print(f"  CM E1: {good}/{tot} beta-orbits satisfy S3=0  (forced by 1+lambda+lambda^2=0)")
# nonCM E1': y^2=x^3+x+8 over F_67
A2,B2=1,8
n2,xs2,ys2,_,_=curve(p,A2,B2)
xset2=set(int(x) for x in xs2); seen=set(); good=0;tot=0
for x in list(xset2):
    if x in seen:continue
    o=[x,(beta*x)%p,(beta*beta*x)%p]
    if len(set(o))<3: continue
    for t in o:seen.add(t)
    tot+=1
    if S3(o[0],o[1],o[2],A2,B2,p)==0: good+=1
print(f"  nonCM E1': {good}/{tot} beta-orbits satisfy S3=0")

print("\n=== Doc 20: 2 sqrt(p) cap. max|V(a)|/sqrt(p), V(a)=sum chi2(y_d) e_n(a d) ===")
cur20=[(13,3,7),(17,2,2),(29,4,9),(37,3,15),(41,3,7),(53,3,21),(61,2,5),(73,3,13),(89,1,9),(97,2,15),(101,2,31),(109,3,17),(113,2,42)]
for p,A,B in cur20:
    r=curve(p,A,B)
    n,xs,ys=r[0],r[1],r[2]
    def chi2(v):
        v=int(v)%p; return 0 if v==0 else int(legendre_symbol(v,p))
    ch=np.array([chi2(y) for y in ys])
    d=np.arange(1,n)
    best=0;ba=0
    for a in range(1,n):
        V=np.sum(ch*np.exp(2j*math.pi*a*d/n))
        if abs(V)>best:best=abs(V);ba=a
    print(f"  p={p:3d} n={n:3d}: max|V|={best:.4f}  ratio={best/math.sqrt(p):.4f}  {'<2 OK' if best/math.sqrt(p)<2 else 'EXCEEDS 2'}")
