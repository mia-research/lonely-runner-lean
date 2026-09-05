#!/usr/bin/env python3
"""
Q: if we CONSTRUCT integers with specific Z[omega] properties, does the curve's CM
structure create DETECTABLE patterns in the output point?

Two distinct Z[omega] properties of a scalar d in F_n = Z[omega]/(pi_n):
 (A) the ENDOMORPHISM orbit: multiply d by the CM unit lambda (lambda^3=1 mod n).
     Prediction (exact CM identity phi=[lambda], phi(x,y)=(beta x,y)):
         x([lambda*d]G) = beta * x([d]G),  y unchanged.
     => a DETECTABLE, exact pattern (and chi6(X) shifts by chi6(beta),
        Eisenstein lift rotates by beta).
 (B) the intrinsic multiplicative class: chi3(d) (cubic residue in F_n).
     Test whether constructing cubic-residue scalars biases the point's CM features
     (chi6(X), Eisenstein-lift angle) vs random scalars. (Prediction: NO -- scalar
     mult isn't a point ring-hom, so the F_n mult class is decoupled from the point.)
Also introduces the EISENSTEIN 2-D LIFT of X (reduce X against the (pi_p) lattice)
and its ARGUMENT = the genuine per-point CM angle.
Exact integers; null-subtracted where statistical.
"""
import random, math, cmath
from collections import Counter
p=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
LAM=0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
BET=0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE
Gx=0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy=0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
aP=367917413016453100223835821029139468249   # pi_p = aP + bP*omega, N(pi_p)=p
bP=303414439467246543595250775667605759171
assert (aP*aP-aP*bP+bP*bP)==p, "pi_p norm != p"
def inv(a):return pow(a,p-2,p)
# Jacobian coordinates (a=0 curve): one inverse per scalar-mult => ~50x faster
def jdouble(P):
    X1,Y1,Z1=P
    if Y1==0:return (0,0,0)
    A=(X1*X1)%p;B=(Y1*Y1)%p;C=(B*B)%p
    D=(2*(((X1+B)**2 -A -C)))%p; E=(3*A)%p; F=(E*E)%p
    X3=(F-2*D)%p; Y3=(E*(D-X3)-8*C)%p; Z3=(2*Y1*Z1)%p
    return (X3,Y3,Z3)
def jadd(P,Q):
    X1,Y1,Z1=P; X2,Y2,Z2=Q
    if Z1==0:return Q
    if Z2==0:return P
    Z1Z1=(Z1*Z1)%p;Z2Z2=(Z2*Z2)%p
    U1=(X1*Z2Z2)%p;U2=(X2*Z1Z1)%p
    S1=(Y1*Z2*Z2Z2)%p;S2=(Y2*Z1*Z1Z1)%p
    if U1==U2:
        return jdouble(P) if S1==S2 else (0,0,0)
    H=(U2-U1)%p;I=((2*H)**2)%p;J=(H*I)%p;r=(2*(S2-S1))%p;V=(U1*I)%p
    X3=(r*r-J-2*V)%p;Y3=(r*(V-X3)-2*S1*J)%p;Z3=(((Z1+Z2)**2-Z1Z1-Z2Z2)*H)%p
    return (X3,Y3,Z3)
def mul(k):
    R=(0,0,0);P=(Gx,Gy,1)
    while k:
        if k&1:R=jadd(R,P)
        P=jdouble(P);k>>=1
    if R[2]==0:return (0,0)
    zi=inv(R[2]);zi2=(zi*zi)%p
    return ((R[0]*zi2)%p,(R[1]*zi2*zi)%p)
e6=(p-1)//6
def prim6():
    for g in range(2,200):
        z=pow(g,e6,p)
        if pow(z,6,p)==1 and all(pow(z,t,p)!=1 for t in(1,2,3)):return z
z6=prim6(); six={pow(z6,j,p):j for j in range(6)}
def chi6(x):return six.get(pow(x%p,e6,p))
# Eisenstein lift: reduce X (integer, = X*1) against lattice (pi_p) in Z[omega].
# basis of (pi_p): pi_p*1=(aP,bP);  pi_p*omega = (-bP, aP-bP)
def rdiv(num,den):
    if den<0:num,den=-num,-den
    q,r=divmod(num,den)
    return q+1 if 2*r>=den else q
b1=(aP,bP); b2=(-bP,aP-bP)
def gauss(u,v):
    def dot(a,b):return a[0]*b[0]+a[1]*b[1]
    while True:
        if dot(v,v)<dot(u,u):u,v=v,u
        m=rdiv(dot(u,v),dot(u,u)); v=(v[0]-m*u[0],v[1]-m*u[1])
        if dot(v,v)>=dot(u,u):return u,v
r1,r2=gauss(b1,b2)
def eis_lift(X):   # short (uu,vv): uu+vv*omega == X mod pi_p
    det=r1[0]*r2[1]-r1[1]*r2[0]
    c1=rdiv(X*r2[1],det); c2=rdiv(-X*r1[1],det)
    lat=(c1*r1[0]+c2*r2[0], c1*r1[1]+c2*r2[1])
    return (X-lat[0], -lat[1])
def eis_angle(X):
    u,v=eis_lift(X); z=complex(u,0)+complex(-0.5,math.sqrt(3)/2)*v
    return math.atan2(z.imag,z.real)

rng=random.Random(2026)
print("=== (A) ENDOMORPHISM orbit: does d -> lambda*d create an exact point pattern? ===")
okx=oky=0; c6=Counter()
for _ in range(30):
    d=rng.randrange(2,n); X,Y=mul(d); Xl,Yl=mul((LAM*d)%n)
    if Xl==(BET*X)%p: okx+=1
    if Yl==Y: oky+=1
    c6[(chi6(Xl)-chi6(X))%6]+=1
print(f"  x([lambda d]G) == beta*x([d]G): {okx}/30 exact;  y unchanged: {oky}/30")
print(f"  chi6 shift chi6(X_lambda)-chi6(X) distribution: {dict(c6)}  (constant => detectable pattern)")
print(f"  => the CM endomorphism IS a detectable, EXACT pattern (chi6 shifts by chi6(beta)={chi6(BET)}).")
print("     But it relates d to lambda*d (both full-size) => no search leverage (this is GLV).")

print("\n=== (B) intrinsic mult class: do CUBIC-RESIDUE scalars bias the point's CM feature? ===")
M=6000
cubic=[pow(rng.randrange(2,n),3,n) for _ in range(M)]   # chi3(d)=1
randm=[rng.randrange(2,n) for _ in range(M)]
def sect_dist(ds):
    c=Counter(chi6(mul(d)[0]) for d in ds); return [c[j] for j in range(6)]
sc=sect_dist(cubic); sr=sect_dist(randm)
print(f"  chi6(X) sectors, CUBIC-residue scalars: {sc}")
print(f"  chi6(X) sectors, RANDOM scalars:        {sr}  (unif={M//6})")
def chisq(a,b):
    tot=sum(a)+sum(b); return sum((a[i]-(a[i]+b[i])*sum(a)/tot)**2/((a[i]+b[i])*sum(a)/tot+1e-9)+
                                  (b[i]-(a[i]+b[i])*sum(b)/tot)**2/((a[i]+b[i])*sum(b)/tot+1e-9) for i in range(6))
print(f"  cubic vs random chi6 dist: chi^2(5df)={chisq(sc,sr):.1f}  (unif~5 => decoupled)")
# Eisenstein-lift angle: 12-sector histogram, cubic vs random
def ang_dist(ds):
    c=Counter(int((eis_angle(mul(d)[0])+math.pi)/(2*math.pi)*12)%12 for d in ds)
    return [c[j] for j in range(12)]
ac=ang_dist(cubic); ar=ang_dist(randm)
print(f"  Eisenstein-lift ANGLE (12 sectors) cubic: {ac}")
print(f"  Eisenstein-lift ANGLE (12 sectors) random:{ar}")
print("\nreading: CM creates a detectable pattern ONLY along the endomorphism (lambda<->beta);")
print("a scalar's intrinsic F_n multiplicative class does NOT imprint the point's CM features.")
