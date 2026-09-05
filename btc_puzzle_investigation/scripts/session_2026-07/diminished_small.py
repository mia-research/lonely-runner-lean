"""
Push the 'does (X,Y) leak position' test into the SMALL-d regime the sampling
version couldn't reach. For small N the whole range is enumerable, so we compute
d*G for EVERY key (complete population -> exact, stronger than sampling) and
measure coordinate->position dependence vs a permutation null. Iterate P += G to
avoid a scalar-mult per key.
"""
import math
import numpy as np

P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

def dbl(X1,Y1,Z1):
    if Y1==0: return (0,0,0)
    S=(4*X1*Y1*Y1)%P; M=(3*X1*X1)%P; X3=(M*M-2*S)%P
    Y3=(M*(S-X3)-8*(Y1*Y1%P)**2)%P; Z3=(2*Y1*Z1)%P; return (X3,Y3,Z3)
def jadd(X1,Y1,Z1,X2,Y2,Z2):
    if Z1==0: return (X2,Y2,Z2)
    if Z2==0: return (X1,Y1,Z1)
    Z1Z1=Z1*Z1%P; Z2Z2=Z2*Z2%P; U1=X1*Z2Z2%P; U2=X2*Z1Z1%P
    S1=Y1*Z2*Z2Z2%P; S2=Y2*Z1*Z1Z1%P
    if U1==U2: return dbl(X1,Y1,Z1) if S1==S2 else (0,0,0)
    H=(U2-U1)%P; I=((2*H)%P)**2%P; J=H*I%P; r=(2*(S2-S1))%P; V=U1*I%P
    X3=(r*r-J-2*V)%P; Y3=(r*(V-X3)-2*S1*J)%P; Z3=((Z1+Z2)**2-Z1Z1-Z2Z2)%P*H%P
    return (X3,Y3,Z3)
def smul(d):
    RX,RY,RZ=0,0,0; AX,AY,AZ=Gx,Gy,1
    while d:
        if d&1: RX,RY,RZ=jadd(RX,RY,RZ,AX,AY,AZ)
        AX,AY,AZ=dbl(AX,AY,AZ); d>>=1
    return RX,RY,RZ

def affine_add_G(x1,y1):    # (x1,y1)+G in affine, one inversion
    if x1==Gx: return None
    inv=pow((Gx-x1)%P,P-2,P); lam=((Gy-y1)*inv)%P
    x3=(lam*lam-x1-Gx)%P; y3=(lam*(x1-x3)-y1)%P; return x3,y3

def features(X,Y):
    f=[X%2,Y%2,X%3,Y%3,X%4,X%5,X%7,X%8,X%9,(X*Y)%3,(X+Y)%5,
       (X>>0)&7,(X>>8)&7,pow(X%3,1,3),pow(X%5,2,5),pow(X%7,3,7),Y%3,Y%5,X%16]
    return f
def mi(a,b):
    a=np.asarray(a); b=np.asarray(b); n=len(a); m=0.0
    ua,ia=np.unique(a,return_inverse=True); ub,ib=np.unique(b,return_inverse=True)
    J=np.zeros((len(ua),len(ub))); np.add.at(J,(ia,ib),1.0); J/=n
    pa=J.sum(1,keepdims=True); pb=J.sum(0,keepdims=True); nz=J>0
    return float((J[nz]*np.log(J[nz]/(pa*pb)[nz])).sum())

print("EXHAUSTIVE small-d test: full population per bit-length.")
print(f"{'N':>3} {'#keys':>8} {'realMI':>8} {'nullMean':>9} {'nullMax':>8} {'leak?':>12}")
for N in (6,8,10,12,14,16,18,20):
    lo=1<<(N-1); hi=1<<N
    x,y,_=None,None,None
    X,Y,_=smul(lo); pt=None
    # convert base to affine
    Zinv=pow(_ if False else 1,1,P)
    Xj,Yj,Zj=smul(lo); zi=pow(Zj,P-2,P); z2=zi*zi%P
    ax,ay=Xj*z2%P, Yj*z2*zi%P
    feats=[]; labs=[]
    d=lo
    while d<hi:
        feats.append(features(ax,ay))
        r=d-lo; w=N-1
        labs.append((r>>max(0,w-3))&7 if w>=3 else r)   # top-3 position bits
        nxt=affine_add_G(ax,ay)
        if nxt is None: break
        ax,ay=nxt; d+=1
    F=np.array(feats); lab=np.array(labs)
    real=max(mi(lab,F[:,j]) for j in range(F.shape[1]))
    rng=np.random.default_rng(0)
    nulls=[]
    for _ in range(200):
        pms=lab.copy(); rng.shuffle(pms)
        nulls.append(max(mi(pms,F[:,j]) for j in range(F.shape[1])))
    nulls=np.array(nulls)
    flag="LEAK!" if real>nulls.max() else "no (floor)"
    print(f"{N:>3} {hi-lo:>8} {real:>8.4f} {nulls.mean():>9.4f} {nulls.max():>8.4f} {flag:>12}")
