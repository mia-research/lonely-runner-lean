#!/usr/bin/env python3
"""
"Test smarter": CONSTRUCT keys carrying a known structure, then map which toolkit
detectors catch it. Random keys average structure away; designed families expose it.

Families (all L-bit small keys in [A,2A), A=2^(L-1)):
  U  uniform random                      (baseline)
  S6 point-sextic forced: chi6(X([d]G))=0  (rejection)  -- POINT-side structure
  SM smooth d (small-prime product)                     -- KEY-side structure (control)
  LH low Hamming weight d                               -- KEY-side structure (control)
Detectors (our toolkit): Hamming wt, smoothness(#small prime factors<=1000),
  decimal trailing zeros, decomposition denominator n (Farey), sextic sector chi6(X).
Each family vs U, each detector: two-sample permutation p on the mean (exact ints;
mean is a monotone stat ranked vs a matched shuffle). A cell 'lights' iff detector
distinguishes the family from uniform. Question: does S6 (point structure) light ANY
KEY-side detector? (DLP says no.) Controls SM/LH must light their natural detector.
"""
import random, math
from fractions import Fraction
from sympy import primerange
p=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Gx=0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy=0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
e6=(p-1)//6
def prim6():
    for g in range(2,200):
        z=pow(g,e6,p)
        if pow(z,6,p)==1 and all(pow(z,t,p)!=1 for t in(1,2,3)): return z
z6=prim6(); six={pow(z6,j,p):j for j in range(6)}
def inv(a): return pow(a,p-2,p)
def padd(P,Q):
    if P is None:return Q
    if Q is None:return P
    x1,y1=P;x2,y2=Q
    if x1==x2 and (y1+y2)%p==0:return None
    s=((3*x1*x1)*inv(2*y1) if P==Q else (y2-y1)*inv((x2-x1)%p))%p
    x3=(s*s-x1-x2)%p;return(x3,(s*(x1-x3)-y1)%p)
def mul(k):
    R=None;P=(Gx,Gy)
    while k:
        if k&1:R=padd(R,P)
        P=padd(P,P);k>>=1
    return R
SP=list(primerange(2,1000))
def chi6X(d):
    X=mul(d)[0]; return six.get(pow(X,e6,p))
L=48; A=1<<(L-1); Nper=1500
rng=random.Random(12345)
def f_uniform(): return A+rng.randrange(A)
def f_sextic0():
    while True:
        d=A+rng.randrange(A)
        if chi6X(d)==0: return d
def f_smooth():
    while True:
        d=1
        while d< A: d*=rng.choice(SP[:60])
        if A<=d<2*A: return d
def f_lowham():
    d=A
    for _ in range(rng.randint(2,5)): d|=1<<rng.randrange(L-1)
    return d
FAM={'U':f_uniform,'S6_pointSextic':f_sextic0,'SM_smooth':f_smooth,'LH_lowHam':f_lowham}
data={name:[fn() for _ in range(Nper)] for name,fn in FAM.items()}
print(f"L={L}, {Nper}/family. detectors on constructed families:")

def ham(d): return bin(d).count('1')
def smooth(d):
    c=0
    for q in SP:
        while d%q==0: d//=q; c+=1
    return c
def deczeros(d):
    s=str(d); return len(s)-len(s.rstrip('0'))
def denomn(d): return Fraction(d-A,A).limit_denominator(256).denominator
def sect(d): return chi6X(d)
DET={'Hamming':ham,'smoothCount':smooth,'decZeros':deczeros,'Farey_n':denomn,'sextic':sect}
# precompute detector values
feat={name:{dn:[df(d) for d in ds] for dn,df in DET.items()} for name,ds in data.items()}

def perm_p(a,b,reps=4000):
    # two-sample: |mean(a)-mean(b)| vs shuffled pooled
    obs=abs(sum(a)/len(a)-sum(b)/len(b)); pool=a+b; na=len(a); hits=0
    for _ in range(reps):
        rng.shuffle(pool)
        if abs(sum(pool[:na])/na-sum(pool[na:])/len(b))>=obs: hits+=1
    return hits/reps

print(f"\n{'family':16}"+"".join(f"{dn:>12}" for dn in DET))
for name in FAM:
    if name=='U': continue
    row=f"{name:16}"
    for dn in DET:
        p_=perm_p(feat[name][dn][:], feat['U'][dn][:])
        row+=f"{('LIGHT' if p_<0.01 else '.')+f'({p_:.3f})':>12}"
    print(row)
print("\nread: S6 lighting a KEY-side detector (Hamming/smooth/decZeros/Farey_n) would be")
print("a point->key trace (exploitable). Controls SM,LH must LIGHT their natural detector.")
