"""
Well-powered independence test: does the secp256k1 public key (X,Y) = d*G leak
the Farey-'n' label of d?  The 82-sample detector in the folder could not detect
even a 100%-strength planted leak (findings sec 3.2), so its negatives are
'underpowered', not 'no leak'. Here we crank the sample size to M and add a
positive control to PROVE the estimator has power, then read the real result.
"""
import random, math
import numpy as np

# secp256k1
P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

def jac_double(X1,Y1,Z1):
    if Y1==0: return (0,0,0)
    S=(4*X1*Y1*Y1)%P
    M=(3*X1*X1)%P
    X3=(M*M-2*S)%P
    Y3=(M*(S-X3)-8*(Y1*Y1%P)*(Y1*Y1%P))%P
    Z3=(2*Y1*Z1)%P
    return (X3,Y3,Z3)

def jac_add(X1,Y1,Z1,X2,Y2,Z2):
    if Z1==0: return (X2,Y2,Z2)
    if Z2==0: return (X1,Y1,Z1)
    Z1Z1=Z1*Z1%P; Z2Z2=Z2*Z2%P
    U1=X1*Z2Z2%P; U2=X2*Z1Z1%P
    S1=Y1*Z2*Z2Z2%P; S2=Y2*Z1*Z1Z1%P
    if U1==U2:
        if S1!=S2: return (0,0,0)
        return jac_double(X1,Y1,Z1)
    H=(U2-U1)%P; I=(2*H)%P*((2*H)%P)%P; J=H*I%P
    r=(2*(S2-S1))%P; V=U1*I%P
    X3=(r*r-J-2*V)%P
    Y3=(r*(V-X3)-2*S1*J)%P
    Z3=((Z1+Z2)*(Z1+Z2)-Z1Z1-Z2Z2)%P*H%P
    return (X3,Y3,Z3)

def scalar_mul_x(d):
    # returns affine (x,y) of d*G
    RX,RY,RZ=0,0,0
    AX,AY,AZ=Gx,Gy,1
    while d:
        if d&1: RX,RY,RZ=jac_add(RX,RY,RZ,AX,AY,AZ)
        AX,AY,AZ=jac_double(AX,AY,AZ)
        d>>=1
    z=pow(RZ,P-2,P)
    z2=z*z%P
    return (RX*z2%P, RY*z2*z%P)

# Farey-n label (their NS logic, restricted to labels achievable in a fixed window)
NS=(39,65,80,135)
def farey_n(bits,key):
    R=2**(bits-1); best=None
    for n in NS:
        ks=[k for k in range(1,n) if math.gcd(k,n)==1]
        u=(key-R)/R
        k=min(ks,key=lambda k:abs(u-k/n)); base=R+(R*k)//n
        if best is None or abs(key-best)>abs(key-base):
            best=base; bestn=n
    return bestn

def features(X,Y):
    f={}
    for m in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53):
        f[f"X%{m}"]=X%m; f[f"Y%{m}"]=Y%m; f[f"XY%{m}"]=(X*Y)%m
    for b in range(0,256,32):
        f[f"Xbit{b}"]=(X>>b)&7
    for p in (3,5,7,11,13):
        f[f"Xleg{p}"]=pow(X%p,(p-1)//2,p)
    return f

def mutual_info(labels, feat):
    # discrete MI in nats
    labels=np.asarray(labels); feat=np.asarray(feat)
    N=len(labels); mi=0.0
    for lv in np.unique(labels):
        pl=np.mean(labels==lv)
        for fv in np.unique(feat):
            pf=np.mean(feat==fv)
            pjoint=np.mean((labels==lv)&(feat==fv))
            if pjoint>0:
                mi+=pjoint*math.log(pjoint/(pl*pf))
    return mi

def run(bits=40, M=8000, seed=0):
    rng=random.Random(seed)
    R=2**(bits-1)
    keys=[R+rng.randrange(R) for _ in range(M)]
    labels=[farey_n(bits,d) for d in keys]
    feats=[features(*scalar_mul_x(d)) for d in keys]
    names=list(feats[0].keys())
    labarr=np.array(labels)

    # permutation null: MI of best feature under label shuffle (noise floor w/ this M)
    def best_real():
        return max(mutual_info(labels,[f[n] for f in feats]) for n in names)
    real=best_real()
    nulls=[]
    for s in range(40):
        perm=labarr.copy(); np.random.default_rng(s).shuffle(perm)
        nulls.append(max(mutual_info(perm,[f[n] for f in feats]) for n in names))
    nulls=np.array(nulls)

    # positive control: feature that equals label 20% of the time -> MUST be detected
    rc=random.Random(123)
    ctrl=[labels[i] if rc.random()<0.20 else rc.randrange(len(NS)) for i in range(M)]
    ctrl_mi=mutual_info(labels,ctrl)

    print(f"bits={bits}  M={M}  labels seen={sorted(set(labels))}")
    print(f"  REAL best-feature MI      = {real:.5f} nats")
    print(f"  NULL (label-shuffle) mean = {nulls.mean():.5f}  max = {nulls.max():.5f}  (n=40 perms)")
    print(f"  REAL percentile vs null   = {100*np.mean(nulls<real):.0f}%")
    print(f"  POS-CONTROL (20% leak) MI = {ctrl_mi:.5f} nats   <- estimator power check")
    print(f"  --> real is {'ABOVE' if real>nulls.max() else 'WITHIN'} the noise floor")

if __name__=="__main__":
    run(bits=40, M=8000, seed=0)
