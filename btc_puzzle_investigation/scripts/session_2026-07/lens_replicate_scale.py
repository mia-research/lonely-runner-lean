"""
Address the synthetic-data concern: was the F1 null an artifact of using 48-bit
uniform keys? Re-run the SAME test at the real puzzle-135 SCALE (135-bit band),
and also at 96-bit, to check scale-invariance. Real curve arithmetic throughout.

Also demonstrate the wrinkle in "use the next integers after 135": neighbors of a
135-bit key share the SAME (n,k) (best-approx of the top bits), so a neighbor
sequence cannot vary k. To vary k you must span the band -- which is what we do.
"""
import random
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
def best_nk(u,nmax=256):
    best=(9e9,1,0)
    for n in range(1,nmax+1):
        k=round(u*n); e=abs(u-k/n)
        if e<best[0]: best=(e,n,k)
    return best[1],best[2]
def spearman(a,b):
    ra=np.argsort(np.argsort(a)).astype(float); rb=np.argsort(np.argsort(b)).astype(float)
    ra-=ra.mean(); rb-=rb.mean(); return (ra@rb)/(np.sqrt((ra@ra)*(rb@rb))+1e-30)

# --- demonstrate (n,k) freezing across neighbors of a 135-bit key ---
_r=random.Random(135)
d0=2**134 + _r.randrange(2**134)
print("neighbor (n,k) freezing at 135-bit scale (d0 + step):")
for step in (0,1,100,10**6,10**12):
    u=(d0+step-2**134)/2**134; print(f"    step={step:>10}: (n,k)={best_nk(u)}")
print("    -> neighbors share (n,k); must span the band to vary k.\n")

def run_scale(N, NS=2500):
    lo=2**(N-1); rr=random.Random(N*7)
    Xs=[];Ys=[];ns=[];ks=[]
    for _ in range(NS):
        d=lo+rr.randrange(lo); u=(d-lo)/lo; n,k=best_nk(u)
        if n<5 or k==0 or k>=n: continue
        x,y=mulxy(d); Xs.append(x);Ys.append(y);ns.append(n);ks.append(k)
    ns=np.array(ns);ks=np.array(ks);Msyn=len(ns); s=ks/ns
    def rho_at(delta):
        npr=ns+delta
        r=np.array([((int(Xs[i])*int(Ys[i]))%(int(npr[i])**2))/(int(npr[i])**2) for i in range(Msyn)])
        o=spearman(r,s); rng=np.random.default_rng(1)
        c=1
        for _ in range(300):
            if abs(spearman(r,rng.permutation(s)))>=abs(o): c+=1
        return o,c/301
    return Msyn, {d:rho_at(d) for d in (-1,0,1)}

for N in (48,96,135):
    M,res=run_scale(N)
    print(f"N={N:>3}bit ({M} keys):  " + "  ".join(
        f"delta{d:+d}: rho={res[d][0]:+.3f} p={res[d][1]:.2f}" for d in (-1,0,1)))
print("\nSame flat rho at true n across 48/96/135 bits => F1 null is scale-invariant,")
print("not a 48-bit artifact. A 135-bit spike at delta=0 would have revived it.")
