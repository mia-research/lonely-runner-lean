#!/usr/bin/env python3
"""
Dilution v3 (2026-07-11): construction = "features = primes q<=Q" (user-confirmed).
G_Q is d x d, d = pi(Q) (matches reported dims 3,4,8,15 for Q=5,10,20,50);
samples = test primes ell; entries = correlations of a CM-Hecke-derived feature
f_q(ell) across the q-features.  Goal: find the feature map that reproduces the
reported ratios {Q5:0.806, Q10:0.704, Q20:0.583, Q50:0.458}, then run the
project-out-the-conductor test on the match.

Candidate feature maps f_q(ell)  (q prime <= Q, ell = sample prime):
  A legendre(ell,q)              pure residue of ell        (expect flat)
  B legendre(a_ell,q)            residue of Hecke eigenvalue
  C (a_ell mod q)                additive residue of a_ell
  D cos(2*pi*a_ell/q)            additive char of a_ell
  E 1_{q | a_ell}                divisibility CONSTRAINT (residue shadow)
  F cos_theta = a_ell/(2 sqrt ell) broadcast * legendre(ell,q)  (CM-weighted residue)
  G a_ell/(2 sqrt ell) itself for EVERY q (pure shared Sato-Tate)  -> rank-1 by design
Each tried BOTH centered and uncentered (a DC/mean common mode = the split/inert
chi_-3 asymmetry).  Report ratio; whichever matches the table gets the full
diagnostic (gap, chi_-3 alignment, project-out).
"""
import numpy as np, math

def sieve(L):
    bs=bytearray([1])*(L+1); bs[0:2]=b'\x00\x00'
    for i in range(2,int(L**.5)+1):
        if bs[i]: bs[i*i::i]=bytearray(len(bs[i*i::i]))
    return [i for i in range(L+1) if bs[i]]
PRIMES=sieve(400000)
UNITS=[(1,0),(-1,0),(0,1),(0,-1),(-1,-1),(1,1)]
IDX2POW={0:0,1:3,2:2,3:5,4:4,5:1}; POW2IDX={v:k for k,v in IDX2POW.items()}
def mulw(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]-a[1]*b[1])
def Trw(v): return 2*v[0]-v[1]
def conj(v): return (v[0]-v[1],-v[1])
def primary(v):
    for u in UNITS:
        w=mulw(u,v)
        if w[0]%3==2 and w[1]%3==0: return w
def cornacchia(l):
    for y in range(1,int((4*l/3)**.5)+2):
        d=4*l-3*y*y
        if d<0: break
        s=int(d**.5)
        if s*s==d and (s+y)%2==0: return ((s+y)//2,y)
def u_of(l,pip):
    pc=conj(pip); w=(-pc[0]*pow(pc[1],-1,l))%l
    tab={(u[0]+u[1]*w)%l:i for i,u in enumerate(UNITS)}
    s=pow(28%l,(l-1)//6,l)
    return POW2IDX[(IDX2POW[tab[s]]+3)%6]
def a_ell(l):
    if l in (2,3,7) or l%3==2: return 0
    p=primary(cornacchia(l)); return Trw(mulw(UNITS[u_of(l,p)],p))
def leg(a,q):
    a%=q
    if a==0: return 0
    return 1 if pow(a,(q-1)//2,q)==1 else -1
def chi3(l): return 0 if l%3==0 else (1 if l%3==1 else -1)

# sample primes and their Hecke data
SAMP=[l for l in PRIMES if l>7 and 42%l!=0][:2000]
aL=np.array([a_ell(l) for l in SAMP],dtype=float)
ct=np.array([aL[i]/(2*math.sqrt(SAMP[i])) for i in range(len(SAMP))])  # cos theta

def featmat(Xn,Q,kind):
    ells=SAMP[:Xn]; a=aL[:Xn]; c=ct[:Xn]; qs=[q for q in PRIMES if q<=Q]
    F=np.zeros((Xn,len(qs)))
    for j,q in enumerate(qs):
        for i,l in enumerate(ells):
            if kind=="A": F[i,j]=leg(l,q)
            elif kind=="B": F[i,j]=leg(int(a[i]),q)
            elif kind=="C": F[i,j]=(int(a[i])%q)
            elif kind=="D": F[i,j]=math.cos(2*math.pi*a[i]/q)
            elif kind=="E": F[i,j]=1.0 if (int(a[i])%q==0) else 0.0
            elif kind=="F": F[i,j]=c[i]*leg(l,q)
            elif kind=="G": F[i,j]=c[i]
    return F,qs

def ratio(F, center):
    if center: F=F-F.mean(0,keepdims=True)
    G=F.T@F/F.shape[0]
    ev=np.linalg.eigvalsh(G)[::-1]
    return ev[0]/ev.sum() if ev.sum()>0 else float('nan')

print("target: Q5=0.806 Q10=0.704 Q20=0.583 Q50=0.458\n")
print(f"{'kind':>4} {'cen':>4} |" + "".join(f"  Q={q:<6}" for q in (5,10,20,50)))
best=None
for kind in "ABCDEFG":
    for center in (True,False):
        row=[ratio(featmat(1000,Q,kind)[0],center) for Q in (5,10,20,50)]
        tag="cen" if center else "raw"
        print(f"{kind:>4} {tag:>4} |" + "".join(f"  {r:<8.3f}" for r in row))
        err=sum((row[i]-t)**2 for i,t in enumerate([0.806,0.704,0.583,0.458]) if not math.isnan(row[i]))
        if best is None or err<best[0]: best=(err,kind,center,row)

print(f"\nBEST match to table: kind={best[1]} center={best[2]}  (sse={best[0]:.4f})  {['%.3f'%x for x in best[3]]}")

# ---- full diagnostic on the best-matching construction ----
kind,center=best[1],best[2]
print(f"\n=== diagnostic on kind={kind} center={center} ===")
print(f"{'Q':>4} {'d':>3} | {'ratio':>7} {'floor':>6} {'lmax':>7} {'gap l1/l2':>9} "
      f"| {'align χ₋₃':>9} {'ratio_projout':>13} {'X-indep(500/2000)':>17}")
for Q in (5,10,20,50,100):
    F,qs=featmat(2000,Q,kind); Fc=F-F.mean(0,keepdims=True) if center else F
    G=Fc.T@Fc/Fc.shape[0]; ev,evec=np.linalg.eigh(G); ev=ev[::-1]; evec=evec[:,::-1]
    d=len(qs); top=evec[:,0]/(np.linalg.norm(evec[:,0])+1e-12)
    # chi_-3 loading in q-feature space: corr of each feature col with chi3(ell)
    c3=chi3v=np.array([chi3(l) for l in SAMP[:2000]],dtype=float)
    load=np.array([np.corrcoef(c3,Fc[:,j])[0,1] if Fc[:,j].std()>0 else 0.0 for j in range(d)])
    load=load/(np.linalg.norm(load)+1e-12)
    align=abs(np.dot(top,load))
    P=np.eye(d)-np.outer(load,load); Gp=P@G@P; evp=np.linalg.eigvalsh(Gp)[::-1]
    rp=evp[0]/max(evp.sum(),1e-12)
    r500=ratio(featmat(500,Q,kind)[0],center)
    print(f"{Q:>4} {d:>3} | {ev[0]/ev.sum():>7.3f} {1.0/d:>6.3f} {ev[0]:>7.3f} "
          f"{ev[0]/max(ev[1],1e-12):>9.2f} | {align:>9.3f} {rp:>13.3f} "
          f"{r500:>8.3f}/{ev[0]/ev.sum():<8.3f}")
