"""
GENERATIVE: assume public info leaks the key's position bucket (=> n). Hunt hard.
ADVERSARIAL: kill every hit with (a) 2000-shuffle permutation null (max-over-
features corrected) and (b) a control-keypair null: same labels, FRESH random
(X,Y). A real public->position leak must beat BOTH.
Trained ONLY on public quantities of the 82 solved keys. No private key used
as a feature. Target = top-2 bits of u (4 buckets); also n-parity reported.
"""
import csv, math
import numpy as np

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

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['puzzle']),int(r['bits']),int(r['private_key'],16),
                     int(r['X'],16),int(r['Y'],16)))
rows.sort()

def pub_features(N,X,Y):
    """ONLY public quantities: puzzle bit-length N and the public key (X,Y)."""
    f={'N':N,'N%4':N%4,'N%8':N%8}
    for m in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71):
        f[f'X%{m}']=X%m; f[f'Y%{m}']=Y%m; f[f'XY%{m}']=(X*Y)%m; f[f'X+Y%{m}']=(X+Y)%m
    for b in range(0,256,16): f[f'Xb{b}']=(X>>b)&3
    for p in (3,5,7,11,13,17,19): f[f'Xleg{p}']=pow(X%p,(p-1)//2,p); f[f'Yleg{p}']=pow(Y%p,(p-1)//2,p)
    f['Ypar']=Y&1; f['Xpar']=X&1
    f['Xhw']=bin(X).count('1'); f['Yhw']=bin(Y).count('1')
    f['Xtop']=X>>252
    return f

N=len(rows)
u=np.array([(k-2**(b-1))/2**(b-1) for _,b,k,_,_ in rows])
Q=np.floor(u*4).astype(int)                 # top-2 bits of position: target (4 buckets)
feats=[pub_features(b,X,Y) for _,b,k,X,Y in rows]
names=list(feats[0].keys())
Fr=np.array([[f[n] for n in names] for f in feats])

def loo_mi(labels,col):
    lab=np.asarray(labels); n=len(lab); tot=0.0
    for i in range(n):
        tr=[j for j in range(n) if j!=i]
        same=[j for j in tr if col[j]==col[i]]
        from collections import Counter
        c_all=Counter(lab[j] for j in tr); c_bin=Counter(lab[j] for j in same)
        nc=len(set(lab))
        p_all=(c_all.get(lab[i],0)+1)/(n-1+nc)
        p_bin=(c_bin.get(lab[i],0)+1)/(len(same)+nc)
        tot+=math.log(p_bin)-math.log(p_all)          # LOO predictive gain (nats)
    return tot/n

def detector(labels,F): return np.array([loo_mi(labels,F[:,j]) for j in range(F.shape[1])])

# ---------- GENERATIVE: rank public features by predictive gain on real data ----------
scores=detector(Q,Fr)
order=np.argsort(scores)[::-1]
print("=== GENERATIVE PHASE: top public features predicting position-bucket Q (4 buckets) ===")
for j in order[:8]:
    print(f"  {names[j]:>8}  gain={scores[j]:+.4f} nats")
best_j=order[0]; best_real=scores[best_j]

# ---------- ADVERSARIAL 1: permutation null (max over features) ----------
rng=np.random.default_rng(0)
null_max=[]
for _ in range(2000):
    perm=rng.permutation(Q)
    null_max.append(detector(perm,Fr).max())
null_max=np.array(null_max)
p_perm=np.mean(null_max>=best_real)
print(f"\n=== ADVERSARIAL 1: permutation null ===")
print(f"  best real feature '{names[best_j]}' gain={best_real:+.4f}")
print(f"  null max-gain: mean={null_max.mean():+.4f}  p95={np.quantile(null_max,0.95):+.4f}  max={null_max.max():+.4f}")
print(f"  corrected p-value = {p_perm:.3f}   -> {'SURVIVES' if p_perm<0.05 else 'KILLED (indistinguishable from chance)'}")

# ---------- ADVERSARIAL 2: control-keypair null ----------
# same Q labels, but FRESH random (X,Y): does the REAL pubkey beat a random one?
print(f"\n=== ADVERSARIAL 2: control-keypair null (same labels, fresh random X,Y) ===")
ck=[]
crng=np.random.default_rng(7)
for _ in range(200):
    ff=[]
    for (_,b,k,_,_),q in zip(rows,Q):
        # random d' in same interval, SAME Q bucket, so labels identical
        R=2**(b-1); lo=R+int(q/4*R); hi=R+int((q+1)/4*R)
        dp=int(crng.integers(lo,max(hi,lo+1)))
        Xp,Yp=mulxy(dp); ff.append(pub_features(b,Xp,Yp))
    Fc=np.array([[f[n] for n in names] for f in ff])
    ck.append(detector(Q,Fc).max())
ck=np.array(ck)
print(f"  real best={best_real:+.4f}   control(random pubkey) best: mean={ck.mean():+.4f} p95={np.quantile(ck,0.95):+.4f}")
print(f"  real percentile vs control = {100*np.mean(ck<best_real):.0f}%   "
      f"-> {'REAL pubkey carries extra signal' if best_real>np.quantile(ck,0.95) else 'KILLED (random pubkey does just as well)'}")

# sanity: does N alone (public puzzle size) relate to Q or n? (ECDLP-free channel)
print(f"\n[sanity] corr(N, u)   = {np.corrcoef([b for _,b,_,_,_ in rows],u)[0,1]:+.3f}")
