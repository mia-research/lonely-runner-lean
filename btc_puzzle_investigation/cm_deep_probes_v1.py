#!/usr/bin/env python3
"""
Deep CM probes (user threads):
 P1. EISENSTEIN 2-D lift through the constructed-key frame: does the lift ANGLE
     distinguish anything the sextic sector couldn't? (richer point feature)
 P2. GLV-of-NORMS: d=N(alpha)=a^2-ab+b^2. Is GLV(d)=(d1,d2) special vs random d?
     This is the ONLY thread not behind the DLP -- GLV is a scalar-only map.
 P3. FOURIER-FLATNESS (mode-k=1 = G idea): DFT of chi6(x([d]G)) over d=1..T.
     If flat (no surviving additive mode, incl k=1) => "G=surviving mode" fails in the
     additive sense; that flatness IS the DLP pseudorandomness.
Jacobian mult (fast). Exact integers; stats null-subtracted / control-backed.
"""
import random, math, cmath
from collections import Counter
p=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
LAM=0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
Gx=0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy=0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
aP=367917413016453100223835821029139468249; bP=303414439467246543595250775667605759171
assert aP*aP-aP*bP+bP*bP==p
def inv(a):return pow(a,p-2,p)
def jd(P):
    X1,Y1,Z1=P
    if Y1==0:return(0,0,0)
    A=X1*X1%p;B=Y1*Y1%p;C=B*B%p;D=2*((X1+B)**2-A-C)%p;E=3*A%p;F=E*E%p
    return((F-2*D)%p,(E*(D-(F-2*D))-8*C)%p,2*Y1*Z1%p)
def ja(P,Q):
    X1,Y1,Z1=P;X2,Y2,Z2=Q
    if Z1==0:return Q
    if Z2==0:return P
    Z1Z1=Z1*Z1%p;Z2Z2=Z2*Z2%p;U1=X1*Z2Z2%p;U2=X2*Z1Z1%p
    S1=Y1*Z2*Z2Z2%p;S2=Y2*Z1*Z1Z1%p
    if U1==U2:return jd(P) if S1==S2 else (0,0,0)
    H=(U2-U1)%p;I=(2*H)**2%p;J=H*I%p;r=2*(S2-S1)%p;V=U1*I%p
    X3=(r*r-J-2*V)%p;return(X3,(r*(V-X3)-2*S1*J)%p,((Z1+Z2)**2-Z1Z1-Z2Z2)*H%p)
def mul(k):
    R=(0,0,0);P=(Gx,Gy,1)
    while k:
        if k&1:R=ja(R,P)
        P=jd(P);k>>=1
    if R[2]==0:return(0,0)
    zi=inv(R[2]);z2=zi*zi%p;return(R[0]*z2%p,R[1]*z2*zi%p)
e6=(p-1)//6
def prim6():
    for g in range(2,200):
        z=pow(g,e6,p)
        if pow(z,6,p)==1 and all(pow(z,t,p)!=1 for t in(1,2,3)):return z
z6=prim6();six={pow(z6,j,p):j for j in range(6)}
def chi6(x):return six.get(pow(x%p,e6,p))
def rdiv(nu,de):
    if de<0:nu,de=-nu,-de
    q,r=divmod(nu,de);return q+1 if 2*r>=de else q
# Eisenstein lift vs (pi_p)
def gauss(u,v):
    dot=lambda a,b:a[0]*b[0]+a[1]*b[1]
    while True:
        if dot(v,v)<dot(u,u):u,v=v,u
        m=rdiv(dot(u,v),dot(u,u));v=(v[0]-m*u[0],v[1]-m*u[1])
        if dot(v,v)>=dot(u,u):return u,v
r1,r2=gauss((aP,bP),(-bP,aP-bP))
def eis(X):
    det=r1[0]*r2[1]-r1[1]*r2[0];c1=rdiv(X*r2[1],det);c2=rdiv(-X*r1[1],det)
    return(X-(c1*r1[0]+c2*r2[0]),-(c1*r1[1]+c2*r2[1]))
def eis_ang_sector(X,S=12):
    u,v=eis(X);z=complex(u,0)+complex(-.5,math.sqrt(3)/2)*v
    return int((math.atan2(z.imag,z.real)+math.pi)/(2*math.pi)*S)%S
# GLV lattice L=<(n,0),(-LAM,1)>
g1,g2=gauss((n,0),(-LAM,1))
def glv(d):
    det=g1[0]*g2[1]-g1[1]*g2[0];c1=rdiv(d*g2[1],det);c2=rdiv(-d*g1[1],det)
    a=d-(c1*g1[0]+c2*g2[0]);b=-(c1*g1[1]+c2*g2[1]);return a,b
rng=random.Random(7)

print("=== P1. Eisenstein-lift ANGLE through constructed families (12 sectors) ===")
def famU(b):A=1<<(b-1);return A+rng.randrange(1<<(b-1))
def famS6(b):
    while True:
        d=famU(b)
        if chi6(mul(d)[0])==0:return d
def famSmooth(b):
    from sympy import primerange
    SP=list(primerange(2,300));A=1<<(b-1)
    for _ in range(300):
        d=1
        while d<A:d*=rng.choice(SP)
        if A<=d<2*A:return d
    return famU(b)
b=48;M=1200
def angdist(fn):
    c=Counter(eis_ang_sector(mul(fn(b))[0]) for _ in range(M));return[c[j] for j in range(12)]
U=angdist(famU);S6=angdist(famS6);SM=angdist(famSmooth)
def chisq(a,B):
    t=sum(a)+sum(B);e=lambda x,s:(x+y)*s/t
    s=0
    for i in range(len(a)):
        ea=(a[i]+B[i])*sum(a)/t;eb=(a[i]+B[i])*sum(B)/t
        s+=(a[i]-ea)**2/(ea+1e-9)+(B[i]-eb)**2/(eb+1e-9)
    return s
print(f"  uniform angle dist:      {U}")
print(f"  point-sextic0 (S6):      {S6}   chi^2 vs U={chisq(S6,U):.1f} (df11; LIGHT if >>19)")
print(f"  smooth key:              {SM}   chi^2 vs U={chisq(SM,U):.1f}")
print("  (S6 should LIGHT = angle sees point structure like sextic; smooth should NOT.)")

print("\n=== P2. GLV of NORMS d=N(alpha) vs random d, same size (~2^140) ===")
def normkey():
    while True:
        a=rng.randrange(1<<69,1<<70);bb=rng.randrange(1<<69,1<<70)
        d=a*a-a*bb+bb*bb
        if (1<<139)<=d<(1<<141):return d,a,bb
def randkey():
    return rng.randrange(1<<139,1<<141)
NN=3000
norm_short=[];rand_short=[];corr=[]
for _ in range(NN):
    d,a,bb=normkey();d1,d2=glv(d)
    norm_short.append(max(abs(d1),abs(d2)).bit_length())
    corr.append((d1,d2,a,bb))
for _ in range(NN):
    d=randkey();d1,d2=glv(d);rand_short.append(max(abs(d1),abs(d2)).bit_length())
import statistics
print(f"  GLV rep max-bits: norms mean={statistics.mean(norm_short):.2f}  random mean={statistics.mean(rand_short):.2f}")
print(f"  (equal => norms have NO special GLV rep; smaller for norms => structure)")
# correlation of (d1,d2) with (a,b): does GLV reveal alpha's parts?
import math as m
def pear(xs,ys):
    mx=statistics.mean(xs);my=statistics.mean(ys)
    num=sum((x-mx)*(y-my) for x,y in zip(xs,ys))
    den=m.sqrt(sum((x-mx)**2 for x in xs)*sum((y-my)**2 for y in ys))
    return num/den if den else 0
d1s=[c[0] for c in corr];d2s=[c[1] for c in corr];as_=[c[2] for c in corr];bs=[c[3] for c in corr]
print(f"  corr(d1,a)={pear(d1s,as_):+.3f}  corr(d1,b)={pear(d1s,bs):+.3f}  corr(d2,a)={pear(d2s,as_):+.3f}  corr(d2,b)={pear(d2s,bs):+.3f}")
print("  (all ~0 => GLV(N(alpha)) does NOT encode alpha's (a,b); norm structure decoupled)")

print("\n=== P3. FOURIER-FLATNESS: DFT of chi6(x([d]G)) over d=1..T (mode-k=1=G?) ===")
T=8192
sig=[cmath.exp(2j*math.pi*chi6(mul(d)[0])/6) for d in range(1,T+1)]
# DFT magnitudes at low frequencies
def dftmag(k):
    return abs(sum(sig[t]*cmath.exp(-2j*math.pi*k*t/T) for t in range(T)))/T
mags=[(k,dftmag(k)) for k in range(0,12)]
floor=1/math.sqrt(T)  # white-noise floor ~1/sqrt(T)
print(f"  white-noise floor ~1/sqrt(T)={floor:.4f}")
for k,mg in mags: print(f"    freq k={k:2d}: |DFT|={mg:.4f}  {'<-PEAK' if mg>4*floor else ''}")
print("  (all ~floor incl k=1 => spectrally FLAT: no surviving additive mode, so 'G=mode1'")
print("   fails in the additive sense; the flatness IS the DLP pseudorandomness.)")
