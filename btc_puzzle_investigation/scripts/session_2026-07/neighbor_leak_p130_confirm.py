"""
CONFIRM: are the high-bit / sign(delta) "hits" in neighbor_leak_p130.py a real
leak, or an artifact of an invalid i.i.d. permutation null on a serially-
structured target?

High scalar bits and sign(delta) are near-monotone across a +/-10k window (bit 15
flips at most once in 20,001 consecutive integers). A target with serial
structure is NOT exchangeable, so shuffling it (which destroys the block
structure) gives a null that is far too tight -> false positives.

Correct null = CIRCULAR SHIFT of the target: preserves the target's block
structure AND each feature's autocorrelation, randomizing only their relative
alignment. A genuine feature->position leak survives shifting (obs >> null); a
drift/autocorrelation artifact does not (obs sits inside the shift null).

Caches the 20k-point feature matrix so this is fast to iterate.
"""
import os, numpy as np

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
def affine_add(x1,y1,x2,y2):
    if x1 is None: return (x2,y2)
    if x1==x2 and (y1+y2)%P==0: return (None,None)
    if x1==x2: s=(3*x1*x1)*pow(2*y1,P-2,P)%P
    else:      s=(y2-y1)*pow(x2-x1,P-2,P)%P
    x3=(s*s-x1-x2)%P; y3=(s*(x1-x3)-y1)%P; return (x3,y3)

D130=0x33e7665705359f04f28b88cf897c603c9
Wlo=D130-10000; Whi=D130+10000; N=Whi-Wlo+1
CACHE=os.path.join(os.path.dirname(__file__),"p130_feats.npz")
_PR=(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71)

if os.path.exists(CACHE):
    z=np.load(CACHE,allow_pickle=True); F=z["F"]; names=list(z["names"])
    print("loaded cached features")
else:
    print("computing 20k points ...")
    sx,sy=mulxy(Wlo); Xs=[sx]; Ys=[sy]; cx,cy=sx,sy
    for _ in range(1,N):
        cx,cy=affine_add(cx,cy,Gx,Gy); Xs.append(cx); Ys.append(cy)
    assert Xs[10000]==0x633cbe3ec02b9401c5effa144c5b4d22f87940259634858fc7e59b1c09937852
    cols=[]; names=[]
    for m in _PR:
        cols.append([x%m for x in Xs]); names.append(f"X%{m}")
        cols.append([y%m for y in Ys]); names.append(f"Y%{m}")
        cols.append([(x*y)%m for x,y in zip(Xs,Ys)]); names.append(f"XY%{m}")
    for b in range(0,256,4):
        cols.append([(x>>b)&1 for x in Xs]); names.append(f"Xb{b}")
        cols.append([(y>>b)&1 for y in Ys]); names.append(f"Yb{b}")
    for p in (3,5,7,11,13,17,19,23,29,31):
        cols.append([pow(x%p,(p-1)//2,p) for x in Xs]); names.append(f"Xleg{p}")
    cols.append([bin(x).count('1') for x in Xs]); names.append("Xhw")
    cols.append([bin(y).count('1') for y in Ys]); names.append("Yhw")
    F=np.array(cols,dtype=float).T
    np.savez(CACHE,F=F,names=np.array(names,dtype=object))
    print("cached")

D=F.shape[1]
scalars=np.arange(Wlo,Whi+1)
# precompute rank matrix once (features are fixed): rank of each feature value
order=F.argsort(0)
RANK=np.empty_like(F)
for j in range(D):
    RANK[order[:,j],j]=np.arange(F.shape[0])

def best_auc_from_target(tgt):
    a=tgt==1; na=int(a.sum()); nb=int((~a).sum())
    if na==0 or nb==0: return 0.0,-1
    ra=RANK[a].sum(0)                      # (D,)
    auc=(ra-na*(na-1)/2)/(na*nb)
    d=np.abs(auc-0.5); j=int(d.argmax()); return float(d[j]),j

rng=np.random.default_rng(7)
def iid_null_p(tgt,obs,iters=300):
    c=1
    for _ in range(iters):
        v,_=best_auc_from_target(rng.permutation(tgt))
        if v>=obs: c+=1
    return c/(iters+1)
def circshift_null_p(tgt,obs,iters=300):
    c=1
    for _ in range(iters):
        k=int(rng.integers(1,N))
        v,_=best_auc_from_target(np.roll(tgt,k))
        if v>=obs: c+=1
    return c/(iters+1)

print(f"\n{'target':>12} | best|AUC-.5| | feature | iid-p  | circ-shift-p")
for lbl,tgt in [("bit 3",((scalars>>3)&1).astype(int)),
                ("bit 10",((scalars>>10)&1).astype(int)),
                ("bit 12",((scalars>>12)&1).astype(int)),
                ("bit 15",((scalars>>15)&1).astype(int)),
                ("sign(delta)",(scalars>D130).astype(int))]:
    obs,arg=best_auc_from_target(tgt)
    pi=iid_null_p(tgt,obs); pc=circshift_null_p(tgt,obs)
    print(f"{lbl:>12} |   {obs:6.4f}   | {names[arg]:>6} | {pi:5.3f}  |   {pc:5.3f}")

print("\niid-p small BUT circ-shift-p large  => artifact (invalid null), not a leak.")
print("both large                          => genuinely flat.")
