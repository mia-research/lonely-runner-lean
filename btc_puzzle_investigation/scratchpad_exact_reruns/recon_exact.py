# EXACT-DATA (mpmath 30dps) rerun of the reconstruction-fidelity "generic" null (M14).
# metric(target t) = corr/||F||_inf ; corr=(1/n)sum_bc|U_t(b,c)|, Fhat=conj(U_t)/|U_t|, F(P_d)=sum Fhat e_p(bx+cy).
import mpmath as mp, random
mp.mp.dps=30
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
p,A,B=43,0,7
pts=[(x,y) for x in range(p) for y in range(p) if (y*y-x*x*x-A*x-B)%p==0]
n=len(pts)+1
G=pts[0];P=[None]*n;Q=None
for d in range(1,n):Q=ec_add(Q,G,A,p);P[d]=Q
wp=2*mp.pi/p
# precompute e_p(b x_d + c y_d) for all (b,c,d)
BC=[(b,c) for b in range(p) for c in range(p) if not(b==0 and c==0)]
E={}
for (b,c) in BC:
    E[(b,c)]=[mp.e**(1j*wp*((b*P[d][0]+c*P[d][1])%p)) for d in range(1,n)]
def metric(tvals):   # tvals[d-1] = target at point d (d=1..n-1)
    corr=mp.mpf(0); Fhat={}
    for bc in BC:
        e=E[bc]
        U=sum(tvals[i]*e[i] for i in range(n-1))
        au=abs(U); corr+=au
        Fhat[bc]=(mp.conj(U)/au) if au>0 else mp.mpc(0)
    corr/=n
    Finf=mp.mpf(0)
    for i in range(n-1):
        Fd=sum(Fhat[bc]*E[bc][i] for bc in BC)
        if abs(Fd)>Finf: Finf=abs(Fd)
    return corr/Finf if Finf>0 else mp.mpf(0)
wn=2*mp.pi/n
# true character target t(d)=e_n(-a0 d), a0=1
true_t=[mp.e**(-1j*wn*1*d) for d in range(1,n)]
mt=metric(true_t)
# random targets: random unit-modulus phases
rng=random.Random(11); rand=[]
for _ in range(30):
    rt=[mp.e**(1j*mp.mpf(rng.random())*2*mp.pi) for _ in range(1,n)]
    rand.append(metric(rt))
rand_sorted=sorted(rand)
mean=sum(rand)/len(rand); 
import math
sd=(sum((float(r)-float(mean))**2 for r in rand)/len(rand))**0.5
above=sum(1 for r in rand if r>=mt)
print(f"p={p} n={n}: EXACT-data reconstruction fidelity corr/||F||_inf")
print(f"  TRUE character a0=1 : {mp.nstr(mt,8)}")
print(f"  RANDOM targets (30) : mean {mp.nstr(mean,6)}  sd {sd:.4f}  min {mp.nstr(rand_sorted[0],6)}  max {mp.nstr(rand_sorted[-1],6)}")
print(f"  z(true vs random) = {(float(mt)-float(mean))/sd:+.2f}   #random >= true: {above}/30")
print(f"  => {'GENERIC (true within random spread)' if above>=2 else 'TRUE CHARACTER STANDS OUT (candidate signal)'}")

print("\n=== MATCHED NULL: fidelity for ALL characters a' (not uniform-random) ===")
lam=next(t for t in range(2,n) if pow(t,3,n)==1 and t!=1)
orbit=set((s*pow(lam,j,n))%n for s in (1,n-1) for j in range(3))  # mu6-orbit of a0=1: {+-1,+-lam,+-lam^2}
res={}
for ap in range(1,n):
    t=[mp.e**(-1j*wn*ap*d) for d in range(1,n)]
    res[ap]=float(metric(t))
vals=sorted(res.values())
orb_vals=[res[a] for a in orbit if a in res]
oth_vals=[res[a] for a in res if a not in orbit]
print(f"  mu6-orbit of a0=1 = {sorted(orbit)}  -> fidelities {[f'{v:.4f}' for v in sorted(orb_vals)]}")
print(f"  ALL characters: min {vals[0]:.4f} mean {sum(vals)/len(vals):.4f} max {vals[-1]:.4f}")
print(f"  orbit mean {sum(orb_vals)/len(orb_vals):.4f}  vs  other-chars mean {sum(oth_vals)/len(oth_vals):.4f}")
above=sum(1 for a in res if a not in orbit and res[a]>=min(orb_vals))
print(f"  #non-orbit characters with fidelity >= min(orbit): {above}/{len(oth_vals)}")
print(f"  => {'GENERIC (orbit not distinguished from other characters)' if above>=2 else 'ORBIT STANDS OUT vs other characters (candidate signal, needs OOS)'}")
