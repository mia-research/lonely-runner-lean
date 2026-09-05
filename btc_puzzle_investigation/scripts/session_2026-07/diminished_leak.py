"""
Directly test the 'diminished use leaks' hypothesis: does (X,Y)=d*G leak the
position of d MORE as d shrinks? If ECC's coordinate-pseudorandomness weakens in
the small-d regime, best-feature MI should RISE as bit-length N falls, and exceed
the permutation null at small N. Full-256-bit keys = the control regime.
Positive control proves the detector has power.
"""
import math, random
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

def features(X,Y):
    f=[]
    for m in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61):
        f+=[X%m,Y%m,(X*Y)%m,(X+Y)%m]
    for b in range(0,256,16): f+=[(X>>b)&3]
    for p in (3,5,7,11,13): f+=[pow(X%p,(p-1)//2,p)]
    return f
def mi(a,b):
    a=np.asarray(a); b=np.asarray(b); n=len(a); m=0.0
    ua,ia=np.unique(a,return_inverse=True); ub,ib=np.unique(b,return_inverse=True)
    J=np.zeros((len(ua),len(ub))); np.add.at(J,(ia,ib),1.0); J/=n
    pa=J.sum(1,keepdims=True); pb=J.sum(0,keepdims=True); nz=J>0
    return float((J[nz]*np.log(J[nz]/(pa*pb)[nz])).sum())
def best_and_null(F,lab,nperm=25):
    real=max(mi(lab,F[:,j]) for j in range(F.shape[1]))
    nulls=[]
    for s in range(nperm):
        p=np.array(lab).copy(); np.random.default_rng(s).shuffle(p)
        nulls.append(max(mi(p,F[:,j]) for j in range(F.shape[1])))
    return real,np.array(nulls)

M=4000
print(f"M={M} keys per bit-length. Target = top-3 position bits (8 buckets).")
print(f"{'N(bits)':>8} {'realMI':>8} {'nullMean':>9} {'nullMax':>8} {'real>nullMax?':>13}")
for N in (20,30,50,80,130,256):
    rng=random.Random(N)
    if N<256: keys=[ (1<<(N-1))+rng.randrange(1<<(N-1)) for _ in range(M)]
    else:     keys=[ rng.randrange(1<<255,1<<256) for _ in range(M)]
    lab=[ ((d-(1<<(N-1)))>>max(0,N-1-3)) & 7 for d in keys] if N<256 else [ (d>>253)&7 for d in keys]
    F=np.array([features(*mulxy(d)) for d in keys])
    real,nulls=best_and_null(F,lab)
    flag = "YES -> LEAK" if real>nulls.max() else "no"
    print(f"{N:>8} {real:>8.4f} {nulls.mean():>9.4f} {nulls.max():>8.4f} {flag:>13}")

# positive control at N=30: plant a 25% leak, confirm detector fires
rng=random.Random(1); keys=[(1<<29)+rng.randrange(1<<29) for _ in range(M)]
lab=[((d-(1<<29))>>26)&7 for d in keys]
F=np.array([features(*mulxy(d)) for d in keys])
plant=np.array([[lab[i] if rng.random()<0.25 else rng.randrange(8)] for i in range(M)])
Fp=np.hstack([F,plant])
real,nulls=best_and_null(Fp,lab)
print(f"\n[positive control N=30, 25% planted leak] realMI={real:.4f} nullMax={nulls.max():.4f} "
      f"-> {'detector HAS power' if real>nulls.max() else 'underpowered'}")
