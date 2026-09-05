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
    if not isprime(N): return None
    G=None
    for Q in pts:
        if Q is None:continue
        R=Q;k=1
        while R is not None:R=add(R,Q);k+=1
        if k==N:G=Q;break
    orb=[];R=None
    for d in range(1,N):R=add(R,G);orb.append(R)
    return N,[P[1] for P in orb]

p,A,B=163,1,4
N,ys=curve(p,A,B)
n=N; ys=np.array(ys); dvec=np.arange(1,n); en=np.exp(-2j*math.pi*dvec/n)
# (1) Is U_real actually REAL? (odd symmetry y_{n-d}=-y_d)
print("check odd symmetry y_{n-d} == -y_d mod p:",
      all((ys[k]+ys[n-2-k])%p==0 for k in range(n-1)))   # index d=k+1, n-d -> index n-d-1=n-2-k
Uimag=[]
for c in range(1,p):
    U=np.sum(np.exp(2j*math.pi*c*ys/p)*en); Uimag.append(abs(U.imag))
print("max |Im U_real| over c:", max(Uimag), "-> U_real is REAL (1 dof), not complex")

def meanmag(seqs):
    m=[]
    for yp in seqs:
        for c in range(1,p):
            m.append(abs(np.sum(np.exp(2j*math.pi*c*yp/p)*en)))
    return np.array(m)
real_m=meanmag([ys])
rng=np.random.default_rng(0)
# (A) their control: arbitrary permutation of y's -> COMPLEX U (2 dof)
permC=[rng.permutation(ys) for _ in range(50)]
# (B) realness-preserving control: keep the +/- pairing, randomize which pair & signs
# pairs: index k (d=k+1) partners n-2-k. Build pair reps, shuffle their abs values, keep antisymmetry.
half=(n-1)//2
# y for d=1..half are 'free'; y for d=n-1..half+1 are their negatives (already). Shuffle the half-block, keep negation.
permR=[]
for _ in range(50):
    perm=rng.permutation(half)
    yp=np.empty(n-1,dtype=int)
    for k in range(half):
        yp[k]=ys[perm[k]]
        yp[n-2-k]=(-ys[perm[k]])%p
    permR.append(yp)
mC=meanmag(permC); mR=meanmag(permR)
print(f"\nreal mean|U|            = {real_m.mean():.4f}")
print(f"their control (complex) = {mC.mean():.4f}   deficit vs it = {100*(real_m.mean()-mC.mean())/mC.mean():+.2f}%")
print(f"realness-preserving ctrl= {mR.mean():.4f}   deficit vs it = {100*(real_m.mean()-mR.mean())/mR.mean():+.2f}%")
print("\nlow-tail (r<0.5): real=%.1f%%  theirCtrl=%.1f%%  realCtrl=%.1f%%"%(
    100*np.mean(real_m/math.sqrt(n-1)<0.5),100*np.mean(mC/math.sqrt(n-1)<0.5),100*np.mean(mR/math.sqrt(n-1)<0.5)))
