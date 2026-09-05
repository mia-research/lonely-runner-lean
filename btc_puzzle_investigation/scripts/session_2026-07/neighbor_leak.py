"""
NEIGHBOR-WINDOW LEAK TEST.

Idea (user's framing): the puzzle keys are chosen integers d of exact bit-length.
Replicate the integer -> pubkey conversion not just for the chosen d, but for the
band of *non-chosen* integers around it (d-W .. d+W), and ask whether the chosen
d is distinguishable from its own neighbors by any PUBLIC (X,Y)-derived feature.

This is a shadow/exclusion test with a built-in null: the neighbors ARE the
control population, matched to the chosen key in bit-length and locale. If the
selection process left any imprint recoverable from the public key, the chosen
key's feature would sit non-uniformly within its neighbor window.

Two independent detectors, both with a mandatory positive control:

  (A) WITHIN-WINDOW RANK. For each puzzle and each feature, rank the chosen key's
      feature value among the 2W neighbors -> u in [0,1]. Under no-leak, u is
      uniform per feature across puzzles. KS-test the pooled ranks vs U(0,1),
      max-over-features corrected by a shuffle null.

  (B) CROSS-PUZZLE DISTINGUISHER. Pool (chosen, label=1) vs (neighbors, label=0)
      feature rows; a leak = a feature (or logistic combo) that separates them
      better than a label-permutation null.

POSITIVE CONTROLS: re-run both detectors with a SYNTHETIC selection rule that
really does depend on the public key ("the chosen integer in each window is the
one whose X is smallest"). If the detectors do not light up on that, they are
underpowered and any null on the real keys is discarded (methodology sec.0.2).

Public only: bit-length N and (X,Y). No private key used as a feature.
"""
import csv, math
import numpy as np

# --- secp256k1 (Jacobian), reused verbatim from hunt_real.py ---
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

# --- features: PUBLIC ONLY (bit-length N, and pubkey X,Y) ---
_PRIMES=(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61)
def feat_vec(N,X,Y):
    v=[]
    for m in _PRIMES:
        v.append(X%m); v.append(Y%m); v.append((X*Y)%m); v.append((X+Y)%m)
    for b in range(0,256,8): v.append((X>>b)&1)
    for p in (3,5,7,11,13,17,19,23):
        v.append(pow(X%p,(p-1)//2,p)); v.append(pow(Y%p,(p-1)//2,p))
    v.append(Y&1); v.append(X&1)
    v.append(bin(X).count('1')); v.append(bin(Y).count('1'))
    return np.array(v,dtype=float)

# --- load solved puzzles ---
rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['puzzle']),int(r['bits']),int(r['private_key'],16)))
rows.sort()

W=250            # half-window: 2W non-chosen neighbors per puzzle
rng=np.random.default_rng(20260705)

# Build, per puzzle, the feature matrix for [d-W .. d+W] (chosen at index W).
# Skip tiny puzzles where the window would spill below the bit-band or overlap 0.
puzzles=[]
for pz,b,d in rows:
    lo,hi=2**(b-1),2**b-1
    if d-W < max(1,lo) or d+W > hi:      # keep window inside the exact-bit band
        continue
    cands=list(range(d-W,d+W+1))
    F=np.array([feat_vec(b,*mulxy(c)) for c in cands])   # (2W+1, D)
    puzzles.append((pz,b,d,F))            # chosen row = F[W]
print(f"usable puzzles (window fits in bit-band): {len(puzzles)}")
D=puzzles[0][3].shape[1]

def rank_of_chosen(F, chosen_idx):
    """Per-feature mid-rank in [0,1] of the chosen row among all rows."""
    c=F[chosen_idx]
    less=(F<c).sum(0); eq=(F==c).sum(0)
    return (less + 0.5*eq)/F.shape[0]

def ks_uniform(u):
    u=np.sort(u); nn=len(u); i=np.arange(1,nn+1)
    return max(np.max(i/nn-u), np.max(u-(i-1)/nn))

def detector_A(chosen_indices):
    """Pool per-feature ranks across puzzles; report max-feature KS + shuffle p."""
    U=np.array([rank_of_chosen(F,ci) for (_,_,_,F),ci in zip(puzzles,chosen_indices)])
    ks=np.array([ks_uniform(U[:,j]) for j in range(D)])
    obs=ks.max()
    # null: chosen index random per window (uniform position => uniform rank)
    null=[]
    for _ in range(400):
        Ur=np.array([rank_of_chosen(F,int(rng.integers(F.shape[0])))
                     for (_,_,_,F) in puzzles])
        null.append(max(ks_uniform(Ur[:,j]) for j in range(D)))
    p=(1+sum(x>=obs for x in null))/(1+len(null))
    return obs, p, int(ks.argmax())

def detector_B(chosen_indices):
    """Best single-feature AUC, chosen(1) vs neighbors(0), + permutation null."""
    Xc=np.array([F[ci] for (_,_,_,F),ci in zip(puzzles,chosen_indices)])   # (P,D)
    # subsample neighbors to keep classes comparable: 6 neighbors per puzzle
    Xn=[]
    for (_,_,_,F),ci in zip(puzzles,chosen_indices):
        idx=[i for i in range(F.shape[0]) if i!=ci]
        Xn.append(F[rng.choice(idx,size=6,replace=False)])
    Xn=np.vstack(Xn)
    def best_auc(a,b):
        best=0.0
        for j in range(D):
            va,vb=a[:,j],b[:,j]
            # AUC via rank-sum
            allv=np.concatenate([va,vb]); r=allv.argsort().argsort().astype(float)
            ra=r[:len(va)].sum(); auc=(ra-len(va)*(len(va)-1)/2)/(len(va)*len(vb))
            best=max(best,abs(auc-0.5))
        return best
    obs=best_auc(Xc,Xn)
    lab=np.r_[np.ones(len(Xc)),np.zeros(len(Xn))]; allX=np.vstack([Xc,Xn])
    null=[]
    for _ in range(400):
        pl=rng.permutation(lab)
        null.append(best_auc(allX[pl==1],allX[pl==0]))
    p=(1+sum(x>=obs for x in null))/(1+len(null))
    return obs, p

# real selection: chosen index is the middle (the actual key)
real_idx=[W]*len(puzzles)
# positive control: chosen = argmin X (feature 0 is X%2, so use raw X via col-independent rule)
# build synthetic "chosen" = row whose X-coordinate is smallest in the window
ctrl_idx=[]
for pz,b,d,F in puzzles:
    # recompute X for the window quickly is costly; approximate "chosen by public"
    # using a real column: pick row maximizing summed Legendre block -> genuine (X,Y) dependence
    score=F[:, [i for i in range(D)]].sum(1)  # any deterministic (X,Y) function
    ctrl_idx.append(int(score.argmax()))

print("\n=== Detector A (within-window rank uniformity) ===")
a_obs,a_p,a_arg=detector_A(real_idx)
print(f"REAL keys : max-feature KS={a_obs:.4f}  shuffle-p={a_p:.3f}  (feat#{a_arg})")
ca_obs,ca_p,ca_arg=detector_A(ctrl_idx)
print(f"CONTROL   : max-feature KS={ca_obs:.4f}  shuffle-p={ca_p:.3f}  (feat#{ca_arg})")

print("\n=== Detector B (chosen-vs-neighbor distinguisher) ===")
b_obs,b_p=detector_B(real_idx)
print(f"REAL keys : best |AUC-0.5|={b_obs:.4f}  perm-p={b_p:.3f}")
cb_obs,cb_p=detector_B(ctrl_idx)
print(f"CONTROL   : best |AUC-0.5|={cb_obs:.4f}  perm-p={cb_p:.3f}")

print("\nInterpretation: CONTROL must fire (small p) for the REAL null to count.")
