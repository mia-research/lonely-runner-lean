"""
SINGLE-WINDOW DEEP LEAK TEST -- puzzle 130, +/-10,000 (20,001 candidates).

Motivation: the cross-puzzle neighbor test (neighbor_leak.py) had only ~71
"samples" (one chosen key per puzzle) so its power was limited. Here we go the
other way: ONE puzzle, but a deep window of 20,001 consecutive integers around
the true key d130. Now n = 20,001 real (scalar -> pubkey) pairs in a single
locale, which is enough to (a) run a high-power within-window leak test and, more
importantly, (b) CALIBRATE the detection floor: what size of leak could 20k
samples actually see? That floor is the real answer to "is 20k useful".

The leakage question, made precise: converting all 20,001 surrounding integers to
their public keys (X,Y), does any PUBLIC feature carry information about the
PRIVATE scalar -- specifically its low bits or its position (offset) in the
window? If yes at any bit, the public key leaks the scalar. If flat, it does not.

  target family (private, what a leak would expose):
    - low bits 0..15 of the candidate scalar c
    - sign of the offset delta = c - d130  (is c above or below the true key)
  detector: best single public feature, |AUC-0.5|, with a shuffle-target null.
  CALIBRATION: plant a synthetic feature = target XOR Bernoulli(eps) for a sweep
    of leak strengths; report the weakest planted leak still flagged at n=20k.
    That converts "20k" into a concrete sensitivity number.

Public only: features are functions of (X,Y). No private value is a feature.
"""
import csv
import numpy as np

# --- secp256k1 (Jacobian), reused verbatim ---
P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
def dbl(X1,Y1,Z1):
    if Y1==0: return (0,0,0)
    S=(4*X1*Y1*Y1)%P; M=(3*X1*X1)%P; X3=(M*M-2*S)%P
    Y3=(M*(S-X3)-8*(Y1*Y1%P)**2)%P; Z3=(2*Y1*Z1)%P; return (X3,Y3,Z3)
def add(X1,Y1,Z1,X2,Y2,Z2):
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
        if d&1: RX,RY,RZ=add(RX,RY,RZ,AX,AY,AZ)
        AX,AY,AZ=dbl(AX,AY,AZ); d>>=1
    z=pow(RZ,P-2,P); z2=z*z%P; return (RX*z2%P, RY*z2*z%P)

# --- incremental window: compute d*G once, then add G repeatedly (P+G) ---
# Affine add for stepping by +G across the window (fast, avoids 20k full muls).
def affine_add(x1,y1,x2,y2):
    if x1 is None: return (x2,y2)
    if x1==x2 and (y1+y2)%P==0: return (None,None)
    if x1==x2: s=(3*x1*x1)*pow(2*y1,P-2,P)%P
    else:      s=(y2-y1)*pow(x2-x1,P-2,P)%P
    x3=(s*s-x1-x2)%P; y3=(s*(x1-x3)-y1)%P; return (x3,y3)

D130=0x33e7665705359f04f28b88cf897c603c9
BITS=130
Wlo=D130-10000; Whi=D130+10000
N=Whi-Wlo+1
print(f"puzzle 130 key d=0x{D130:x}  window [d-10000, d+10000], n={N}")

# start at Wlo*G, then step +G
sx,sy=mulxy(Wlo)
Xs=np.empty(N,dtype=object); Ys=np.empty(N,dtype=object)
Xs[0],Ys[0]=sx,sy
cx,cy=sx,sy
for i in range(1,N):
    cx,cy=affine_add(cx,cy,Gx,Gy)
    Xs[i],Ys[i]=cx,cy
# sanity: the center must equal the recorded pubkey X
assert Xs[10000]==0x633cbe3ec02b9401c5effa144c5b4d22f87940259634858fc7e59b1c09937852, "center X mismatch!"
print("center pubkey X matches puzzles_verified.csv  (conversion reproduced)")

scalars=np.arange(Wlo,Whi+1)

# --- public feature matrix (functions of X,Y only) ---
_PR=(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71)
def build_features():
    cols=[]; names=[]
    Xa=Xs; Ya=Ys
    for m in _PR:
        cols.append(np.array([int(x)%m for x in Xa])); names.append(f"X%{m}")
        cols.append(np.array([int(y)%m for y in Ya])); names.append(f"Y%{m}")
        cols.append(np.array([(int(x)*int(y))%m for x,y in zip(Xa,Ya)])); names.append(f"XY%{m}")
    for b in range(0,256,4):
        cols.append(np.array([(int(x)>>b)&1 for x in Xa])); names.append(f"Xb{b}")
        cols.append(np.array([(int(y)>>b)&1 for y in Ya])); names.append(f"Yb{b}")
    for p in (3,5,7,11,13,17,19,23,29,31):
        cols.append(np.array([pow(int(x)%p,(p-1)//2,p) for x in Xa])); names.append(f"Xleg{p}")
    cols.append(np.array([bin(int(x)).count('1') for x in Xa])); names.append("Xhw")
    cols.append(np.array([bin(int(y)).count('1') for y in Ya])); names.append("Yhw")
    return np.array(cols,dtype=float).T, names
F,names=build_features()
D=F.shape[1]
print(f"features: {D} public columns\n")

rng=np.random.default_rng(130130)

def best_auc(F, tgt):
    """max_j |AUC-0.5| for binary target tgt over all feature columns."""
    a=tgt==1; b=~a
    na=a.sum(); nb=b.sum()
    if na==0 or nb==0: return 0.0, -1
    best=0.0; arg=-1
    order=F.argsort(0)
    ranks=np.empty_like(F);
    for j in range(F.shape[1]):
        r=np.empty(F.shape[0]); r[order[:,j]]=np.arange(F.shape[0]);
        ra=r[a].sum(); auc=(ra-na*(na-1)/2)/(na*nb)
        d=abs(auc-0.5)
        if d>best: best=d; arg=j
    return best, arg

def perm_p(F, tgt, obs, iters=200):
    cnt=1
    for _ in range(iters):
        t=rng.permutation(tgt)
        v,_=best_auc(F,t)
        if v>=obs: cnt+=1
    return cnt/(iters+1)

print("=== Within-window leak: predict PRIVATE scalar bits from PUBLIC (X,Y) ===")
print(f"{'target':>14} | best|AUC-.5| |  perm-p  | feature")
for bit in [0,1,2,3,4,6,8,10,12,15]:
    tgt=((scalars>>bit)&1).astype(int)
    obs,arg=best_auc(F,tgt)
    p=perm_p(F,tgt,obs,iters=150)
    print(f"   scalar bit {bit:>2} |   {obs:6.4f}   |  {p:5.3f}  | {names[arg]}")
# offset sign
tgt=(scalars>D130).astype(int)
obs,arg=best_auc(F,tgt); p=perm_p(F,tgt,obs,iters=150)
print(f"   sign(delta)  |   {obs:6.4f}   |  {p:5.3f}  | {names[arg]}")

print("\n=== CALIBRATION: detection floor at n=20k (planted leak sweep) ===")
print("plant one synthetic feature = target XOR Bernoulli(eps); report best|AUC-.5|")
base=((scalars>>7)&1).astype(int)
for eps in [0.50,0.45,0.40,0.30,0.20,0.10]:
    flips=rng.random(N)<eps
    planted=(base^flips.astype(int)).astype(float)
    Fp=np.column_stack([F,planted])
    obs,arg=best_auc(Fp,base)
    fired = "FIRES" if arg==D else "(real feat won)"
    print(f"   leak eps={eps:.2f} (corr~{1-2*eps:+.2f}) : best|AUC-.5|={obs:6.4f}  {fired}")

print("\nRead: real-scalar rows at perm-p>>0.05 = no leak. Calibration row where the")
print("planted feature stops winning = the weakest leak 20k samples can still catch.")
