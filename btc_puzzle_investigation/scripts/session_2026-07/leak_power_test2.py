"""
Stronger, assumption-free leak hunt. No reliance on any prior result:
we generate fresh keys, compute d*G ourselves, and MEASURE whether any
single feature OR any feature PAIR (interaction) of the public key predicts
the attack-relevant quantity: the high bits of d. Positive controls prove the
detector has power against BOTH single and interaction leaks.
"""
import random, math
import numpy as np

P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

def dbl(X1,Y1,Z1):
    if Y1==0: return (0,0,0)
    S=(4*X1*Y1*Y1)%P; M=(3*X1*X1)%P; X3=(M*M-2*S)%P
    Y3=(M*(S-X3)-8*(Y1*Y1%P)**2)%P; Z3=(2*Y1*Z1)%P
    return (X3,Y3,Z3)
def add(X1,Y1,Z1,X2,Y2,Z2):
    if Z1==0: return (X2,Y2,Z2)
    if Z2==0: return (X1,Y1,Z1)
    Z1Z1=Z1*Z1%P; Z2Z2=Z2*Z2%P; U1=X1*Z2Z2%P; U2=X2*Z1Z1%P
    S1=Y1*Z2*Z2Z2%P; S2=Y2*Z1*Z1Z1%P
    if U1==U2: return dbl(X1,Y1,Z1) if S1==S2 else (0,0,0)
    H=(U2-U1)%P; I=((2*H)%P)**2%P; J=H*I%P; r=(2*(S2-S1))%P; V=U1*I%P
    X3=(r*r-J-2*V)%P; Y3=(r*(V-X3)-2*S1*J)%P; Z3=((Z1+Z2)**2-Z1Z1-Z2Z2)%P*H%P
    return (X3,Y3,Z3)
def mul_xy(d):
    RX,RY,RZ=0,0,0; AX,AY,AZ=Gx,Gy,1
    while d:
        if d&1: RX,RY,RZ=add(RX,RY,RZ,AX,AY,AZ)
        AX,AY,AZ=dbl(AX,AY,AZ); d>>=1
    z=pow(RZ,P-2,P); z2=z*z%P
    return (RX*z2%P, RY*z2*z%P)

def features(X,Y):
    f=[]
    for m in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61):
        f+=[X%m, Y%m, (X*Y)%m, (X+Y)%m]
    for b in range(0,256,32): f+=[(X>>b)&7,(Y>>b)&7]
    for p in (3,5,7,11,13): f+=[pow(X%p,(p-1)//2,p)]
    return f

def mi(a,b):
    a=np.asarray(a); b=np.asarray(b); n=len(a); m=0.0
    ua,ia=np.unique(a,return_inverse=True); ub,ib=np.unique(b,return_inverse=True)
    joint=np.zeros((len(ua),len(ub)))
    np.add.at(joint,(ia,ib),1.0); joint/=n
    pa=joint.sum(1,keepdims=True); pb=joint.sum(0,keepdims=True)
    nz=joint>0
    return float((joint[nz]*np.log(joint[nz]/(pa*pb)[nz])).sum())

def run(bits=48, topbits=4, M=20000, seed=0):
    rng=random.Random(seed); R=2**(bits-1)
    keys=[R+rng.randrange(R) for _ in range(M)]
    # TARGET = top `topbits` bits of d below the leading 1  (attack-relevant)
    label=[ (d>>(bits-1-topbits)) & ((1<<topbits)-1) for d in keys ]
    F=np.array([features(*mul_xy(d)) for d in keys])   # M x nfeat
    nfeat=F.shape[1]; lab=np.array(label)
    print(f"bits={bits} target=top{topbits}bits ({1<<topbits} classes) M={M} nfeat={nfeat}")

    # ---- single-feature ----
    single=[mi(lab,F[:,j]) for j in range(nfeat)]
    best_s=max(single)
    null_s=[]
    for s in range(30):
        p=lab.copy(); np.random.default_rng(s).shuffle(p)
        null_s.append(max(mi(p,F[:,j]) for j in range(nfeat)))
    null_s=np.array(null_s)
    # positive control: a feature that agrees with label 20% of the time
    rc=random.Random(7)
    ctrl=np.array([label[i] if rc.random()<0.2 else rc.randrange(1<<topbits) for i in range(M)])
    print(f"  SINGLE: real_best={best_s:.4f}  null(mean={null_s.mean():.4f},max={null_s.max():.4f})  "
          f"pctile={100*np.mean(null_s<best_s):.0f}%  POScontrol={mi(lab,ctrl):.4f}")

    # ---- pairs (interactions) among top-14 single features ----
    top=np.argsort(single)[-14:]
    def pack(u,v): return u.astype(np.int64)*1000+v  # joint code
    pair_real=max(mi(lab,pack(F[:,i],F[:,j])) for a,i in enumerate(top) for j in top[a+1:])
    null_p=[]
    for s in range(15):
        p=lab.copy(); np.random.default_rng(100+s).shuffle(p)
        null_p.append(max(mi(p,pack(F[:,i],F[:,j])) for a,i in enumerate(top) for j in top[a+1:]))
    null_p=np.array(null_p)
    # positive control for INTERACTION: label recoverable only from (a XOR b), each alone uniform
    rc2=random.Random(11)
    C=1<<topbits
    a=np.array([rc2.randrange(C) for _ in range(M)])
    b=np.array([(label[i]-a[i])%C for i in range(M)])   # a,b each ~uniform; (a+b)%C == label
    mi_a=mi(lab,a); mi_b=mi(lab,b); mi_ab=mi(lab,pack(a,b))
    print(f"  PAIR  : real_best={pair_real:.4f}  null(mean={null_p.mean():.4f},max={null_p.max():.4f})  "
          f"pctile={100*np.mean(null_p<pair_real):.0f}%")
    print(f"  PAIR POScontrol (interaction): MI(a)={mi_a:.4f} MI(b)={mi_b:.4f} -> MI(a,b)={mi_ab:.4f} "
          f"(single detector blind, pair detector sees it)")
    print(f"  VERDICT: single {'ABOVE' if best_s>null_s.max() else 'at floor'}; "
          f"pair {'ABOVE' if pair_real>null_p.max() else 'at floor'}")

if __name__=="__main__":
    run()
