"""
n / k EXCLUSION (emptiness) TEST -- the right target, the right question.

Correction over the neighbor-window scripts: a tight +/-W window around a large
key FREEZES (n,k). n is the best-rational-approximation denominator of the
position u=(c-2^{N-1})/2^{N-1} (n<=256); shifting c by +/-1e4 out of ~2^129
leaves u -- hence n,k -- unchanged. To study n/k you must vary the TOP bits.

So here we sample scalars spread across a bit-band, so (n,k) actually ranges,
and ask TWO things of the PUBLIC key (X,Y):

  DIRECT  : does any public feature PREDICT n (or k)?  [best-feature MI + null]
  EXCLUDE : does any public feature make some (feature-value, n) combination
            EMPTY -- i.e. rule an n out -- beyond chance?  This is the weaker,
            easier-to-miss "shadow" signal (methodology sec.0.6): a one-sided
            "this (X,Y) is INCOMPATIBLE with these n", not "predicts n".
            Statistic = # of structurally-empty cells in the feature x n table,
            compared to a shuffle-of-n null. A real exclusion => MORE empty
            cells than the null (the leak forbids combinations).

Positive controls (mandatory, methodology sec.0.2):
  - direct control : a planted feature = n mod 3  -> MI must fire.
  - exclude control: a planted feature that is FORBIDDEN (never occurs) for a
    subset of n values -> emptiness must fire.
If a control does not fire, its null is discarded as underpowered.

Public only: features are functions of (X,Y). Scalar/top-bits never a feature.
"""
import numpy as np

P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
def dbl(X1,Y1,Z1):
    if Y1==0: return (0,0,0)
    S=(4*X1*Y1*Y1)%P; M=(3*X1*X1)%P; X3=(M*M-2*S)%P
    Y3=(M*(S-X3)-8*(Y1*Y1%P)**2)%P; Z3=(2*Y1*Z1)%P; return (X3,Y3,Z3)
def addj(X1,Y1,Z1,X2,Y2,Z2):
    if Z1==0: return (X2,Y2,Z2)
    if Z2==0: return (X1,Y1,Z1)
    Z1Z1=Z1*Z1%P; Z2Z2=Z2*Z2%P; U1=X1*Z2Z2%P; U2=X2*Z1Z1%P
    S1=Y1*Z2*Z2Z2%P; S2=Y2*Z1*Z1Z1%P
    if U1==U2: return dbl(X1,Y1,Z1) if S1==S2 else (0,0,0)
    H=(U2-U1)%P; I=((2*H)%P)**2%P; J=H*I%P; r=(2*(S2-S1))%P; V=U1*I%P
    X3=(r*r-J-2*V)%P; Y3=(r*(V-X3)-2*S1*J)%P; Z3=((Z1+Z2)**2-Z1Z1-Z2Z2)%P*H%P
    return (X3,Y3,Z3)
def mulxy(d):
    RX,RY,RZ=0,0,0; AX,AY,AZ=Gx,Gy,1
    while d:
        if d&1: RX,RY,RZ=addj(RX,RY,RZ,AX,AY,AZ)
        AX,AY,AZ=dbl(AX,AY,AZ); d>>=1
    z=pow(RZ,P-2,P); z2=z*z%P; return (RX*z2%P, RY*z2*z%P)

def best_nk(u, nmax=256):
    """best rational k/n ~ u with 1<=n<=nmax; returns (n,k)."""
    bestn,bestk,berr=1,0,abs(u)
    for n in range(1,nmax+1):
        k=round(u*n); e=abs(u-k/n)
        if e<berr-1e-18: berr,bestn,bestk=e,n,k
    return bestn,bestk

N=130; lo=2**(N-1); hi=2**N
S=20000
rng=np.random.default_rng(424242)
import random as _r; _r.seed(424242)
scal=[_r.randrange(lo,hi) for _ in range(S)]         # spread across the band

print(f"sampling {S} scalars across the {N}-bit band; computing (n,k) and (X,Y)...")
ns=np.empty(S,int); ks=np.empty(S,int)
Xs=np.empty(S,object); Ys=np.empty(S,object)
for i,c in enumerate(scal):
    u=(int(c)-lo)/lo
    n,k=best_nk(u); ns[i]=n; ks[i]=k
    Xs[i],Ys[i]=mulxy(int(c))
print("done. n range:",ns.min(),"-",ns.max(),"| distinct n:",len(set(ns.tolist())))

# --- small-alphabet PUBLIC features (kept small so contingency cells populate) ---
feat={}
for m in (2,3,5,7,11,13):
    feat[f"X%{m}"]=np.array([int(x)%m for x in Xs])
    feat[f"Y%{m}"]=np.array([int(y)%m for y in Ys])
    feat[f"XY%{m}"]=np.array([(int(x)*int(y))%m for x,y in zip(Xs,Ys)])
for p in (3,5,7,11):
    feat[f"Xleg{p}"]=np.array([pow(int(x)%p,(p-1)//2,p) for x in Xs])
    feat[f"Yleg{p}"]=np.array([pow(int(y)%p,(p-1)//2,p) for y in Ys])
for b in (0,1,2,3):
    feat[f"Xb{b}"]=np.array([(int(x)>>b)&1 for x in Xs])
fnames=list(feat.keys())

# target n restricted to its most common values so cells are populated
from collections import Counter
common_n=[n for n,_ in Counter(ns.tolist()).most_common(16)]
mask=np.isin(ns,common_n)
nb=ns[mask]
remap={n:i for i,n in enumerate(sorted(common_n))}
tgt_n=np.array([remap[n] for n in nb])           # 16-way target
B=len(common_n)
print(f"exclusion target = 16 most-common n {sorted(common_n)}  (n_samples={mask.sum()})")

def mi(fcol,t):
    """normalized mutual information, small alphabets."""
    fa=fcol; A=int(fa.max())+1; Bt=int(t.max())+1
    joint=np.zeros((A,Bt));
    for a,b in zip(fa,t): joint[a,b]+=1
    joint/=joint.sum(); pa=joint.sum(1,keepdims=True); pb=joint.sum(0,keepdims=True)
    with np.errstate(divide='ignore',invalid='ignore'):
        m=joint*np.log((joint+1e-30)/(pa*pb+1e-30))
    return float(m[joint>0].sum())

def empties(fcol,t):
    """# empty cells in feature x target table."""
    A=int(fcol.max())+1; Bt=int(t.max())+1
    tab=np.zeros((A,Bt),bool)
    for a,b in zip(fcol,t): tab[a,b]=True
    return int((~tab).sum())

def best_over(stat,cols,t):
    vals=[(stat(feat[c][mask] if len(feat[c])==S else feat[c],t),c) for c in cols]
    return max(vals)

def null_p(stat,cols,t,obs,better,iters=300):
    c=1
    for _ in range(iters):
        tp=rng.permutation(t)
        v,_=best_over(stat,cols,tp)
        if better(v,obs): c+=1
    return c/(iters+1)

print("\n=== DIRECT: does a public feature PREDICT n? (best MI + shuffle null) ===")
obs,arg=best_over(mi,fnames,tgt_n)
p=null_p(mi,fnames,tgt_n,obs,lambda v,o:v>=o,200)
print(f"  REAL   : best MI={obs:.5f} bits  perm-p={p:.3f}  ({arg})")
# direct control: planted feature = n mod 3
feat["CTRL_nmod3_full"]=(ns%3);
obsc,argc=best_over(mi,["CTRL_nmod3_full"],tgt_n)
pc=null_p(mi,["CTRL_nmod3_full"],tgt_n,obsc,lambda v,o:v>=o,200)
print(f"  CONTROL: best MI={obsc:.5f} bits  perm-p={pc:.3f}  (planted n%3)")

print("\n=== EXCLUDE: does a public feature make some n IMPOSSIBLE? ===")
print("    (more empty cells than the null => a one-sided exclusion leak)")
obs,arg=best_over(empties,fnames,tgt_n)
# for exclusion a leak means MORE empties than null -> better = v>=obs
p=null_p(empties,fnames,tgt_n,obs,lambda v,o:v>=o,200)
print(f"  REAL   : max empty-cells={obs}  perm-p={p:.3f}  ({arg})")
# exclude control: feature forbidden for half the n-classes
forb=np.where(np.isin(tgt_n,range(0,B,2)), 0, (rng.integers(1,6,tgt_n.shape)))
feat["CTRL_forbid"]=np.empty(S,int); feat["CTRL_forbid"][mask]=forb
obsc,argc=best_over(empties,["CTRL_forbid"],tgt_n)
pc=null_p(empties,["CTRL_forbid"],tgt_n,obsc,lambda v,o:v>=o,200)
print(f"  CONTROL: max empty-cells={obsc}  perm-p={pc:.3f}  (planted forbidden combos)")

print("\nRead: REAL small MI + REAL empties at perm-p>>0.05, while BOTH controls")
print("fire (p small) => no n leak by prediction OR by exclusion, test has power.")

# ---- same battery, target = k (coprime numerator) ----
common_k=[k for k,_ in Counter(ks.tolist()).most_common(16)]
mk=np.isin(ks,common_k); remapk={k:i for i,k in enumerate(sorted(common_k))}
tgt_k=np.array([remapk[k] for k in ks[mk]]); mask=mk   # reuse mask var in best_over
print(f"\n=== target = k, 16 most-common {sorted(common_k)} (n_samples={mk.sum()}) ===")
obs,arg=best_over(mi,fnames,tgt_k); p=null_p(mi,fnames,tgt_k,obs,lambda v,o:v>=o,200)
print(f"  DIRECT  REAL   : best MI={obs:.5f} bits  perm-p={p:.3f}  ({arg})")
feat["CTRL_kmod3_full"]=(ks%3)
obsc,_=best_over(mi,["CTRL_kmod3_full"],tgt_k); pc=null_p(mi,["CTRL_kmod3_full"],tgt_k,obsc,lambda v,o:v>=o,200)
print(f"  DIRECT  CONTROL: best MI={obsc:.5f} bits  perm-p={pc:.3f}  (planted k%3)")
obs,arg=best_over(empties,fnames,tgt_k); p=null_p(empties,fnames,tgt_k,obs,lambda v,o:v>=o,200)
print(f"  EXCLUDE REAL   : max empty-cells={obs}  perm-p={p:.3f}  ({arg})")
