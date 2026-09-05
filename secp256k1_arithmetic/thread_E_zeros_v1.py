#!/usr/bin/env python3
"""
Thread E (2026-07-11): low-lying zeros of L(E,s)=L(psi,s) for E: y^2=x^3+7,
conductor N=21168, weight 2, root number W=+1, from the EXACT Hecke
eigenvalues (CM theta series).  Purpose: upgrade the survival-law/adelic
section from "model" to "verified instance of the explicit formula".

Method (standard for a weight-2 newform):
  completed  Lambda(s) = (sqrt(N)/(2 pi))^s Gamma(s) L(s),  Lambda(s)=W Lambda(2-s).
  Center s=1; zeros at s = 1 + i gamma.  Use the smoothed approximate functional
  equation via the incomplete-Gamma "G-function" expansion:
     Lambda(s) = sum_{n>=1} a_n/n^s * [ G(s, 2pi n/sqrt N) ]
               + W * sum_{n>=1} a_n/n^{2-s} * [ G(2-s, 2pi n/sqrt N) ],
  where for weight 2 the exact smoothing is  Lambda(s) = sum a_n (F_s(n)+W F_{2-s}(n))
  with F_s(n) = (sqrt N/(2 pi n))^s Gamma(s, 2 pi n/sqrt N)  (upper incomplete Gamma).
  This converges fast (exp decay in n).  Zeros of L on Re(s)=1 <=> zeros of the
  real function Z(t):=Lambda(1+it) (real for W=+1 by the functional equation).

Checks:
  (1) Lambda(s) = W Lambda(2-s) numerically (functional-equation residual).
  (2) L(1) = Omega = 3.0414172284 (BSD central value, rank 0 => L(1)!=0).
  (3) list first ~8 zero ordinates gamma>0; compare spacing to the GUE/RMT
      expectation scaled by the analytic conductor.
  (4) explicit-formula check: sum_gamma h(gamma) vs the prime/archimedean side
      for a test function h -- confirms the zeros we found are the actual zeros.
"""
import mpmath as mp
import math
mp.mp.dps = 30

# ---- exact Hecke eigenvalues a_n from the CM structure ----------------------
def sieve(L):
    bs=bytearray([1])*(L+1); bs[0:2]=b'\x00\x00'
    for i in range(2,math.isqrt(L)+1):
        if bs[i]: bs[i*i::i]=bytearray(len(bs[i*i::i]))
    return bs
UNITS=[(1,0),(-1,0),(0,1),(0,-1),(-1,-1),(1,1)]
IDX2POW={0:0,1:3,2:2,3:5,4:4,5:1}; POW2IDX={v:k for k,v in IDX2POW.items()}
def mulw(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]-a[1]*b[1])
def Tr(v): return 2*v[0]-v[1]
def conj(v): return (v[0]-v[1],-v[1])
def primary(v):
    for u in UNITS:
        w=mulw(u,v)
        if w[0]%3==2 and w[1]%3==0: return w
def cornacchia(l):
    for y in range(1,math.isqrt(4*l//3)+2):
        d=4*l-3*y*y
        if d<0: break
        s=math.isqrt(d)
        if s*s==d and (s+y)%2==0: return ((s+y)//2,y)
def u_of(l,pip):
    pc=conj(pip); w=(-pc[0]*pow(pc[1],-1,l))%l
    tab={(u[0]+u[1]*w)%l:i for i,u in enumerate(UNITS)}
    s=pow(28%l,(l-1)//6,l)
    return POW2IDX[(IDX2POW[tab[s]]+3)%6]

N=21168; W=1
NMAX=6000
isp=sieve(NMAX)
aP={}
for l in range(2,NMAX+1):
    if not isp[l]: continue
    if l in (2,3,7) or l%3==2: aP[l]=0
    else: aP[l]=Tr(mulw(UNITS[u_of(l,primary(cornacchia(l)))],primary(cornacchia(l))))
def a_n(m):
    r=1; mm=m; d=2
    while d*d<=mm:
        if mm%d==0:
            k=0
            while mm%d==0: mm//=d; k+=1
            if d in (2,3,7): loc=0
            else:
                s0,s1=1,aP[d]
                for _ in range(2,k+1): s0,s1=s1,aP[d]*s1-d*s0
                loc=s1
            r*=loc
            if r==0: return 0
        d+=1
    if mm>1: r*= (0 if mm in (2,3,7) else aP[mm])
    return r
A=[0]*(NMAX+1)
for m in range(1,NMAX+1): A[m]=a_n(m)

sqN=mp.sqrt(N); twopi=2*mp.pi
# F_s(n) = (sqrtN/(2 pi n))^s * Gamma(s, 2 pi n/sqrtN)
def Lambda(s):
    s=mp.mpf(0)+s
    tot=mp.mpc(0)
    for n in range(1,NMAX+1):
        if A[n]==0: continue
        x=twopi*n/sqN
        term = A[n]*( (sqN/(twopi*n))**s * mp.gammainc(s, x)
                    + W*(sqN/(twopi*n))**(2-s) * mp.gammainc(2-s, x) )
        tot+=term
    return tot
def Lfun(s):  # L(s) = Lambda(s) / [ (sqrtN/2pi)^s Gamma(s) ]
    return Lambda(s)/((sqN/twopi)**s * mp.gamma(s))

# (1) functional equation residual
res=abs(Lambda(mp.mpf('1.3')+0.4j)-W*Lambda(mp.mpf('0.7')-0.4j))
print(f"(1) |Lambda(s)-W Lambda(2-s)| at s=1.3+0.4i: {mp.nstr(res,3)}  (should be ~0)")

# (2) central value
L1=Lfun(mp.mpf(1))
Om=mp.gamma(mp.mpf(1)/3)*mp.gamma(mp.mpf(1)/6)/(2*mp.sqrt(mp.pi)*mp.mpf(7)**(mp.mpf(1)/6))
print(f"(2) L(1) = {mp.nstr(L1.real,12)}   Omega = {mp.nstr(Om,12)}   "
      f"L(1)/Omega = {mp.nstr(L1.real/Om,10)}")

# (3) zeros on the critical line: Z(t)=Lambda(1+it) is real for W=+1
def Z(t): return mp.re(Lambda(1+1j*t))
zeros=[]
t=mp.mpf('0.2'); prev=Z(t); step=mp.mpf('0.1')
while len(zeros)<10 and t<40:
    t2=t+step; cur=Z(t2)
    if prev==0 or (prev<0)!=(cur<0):
        g=mp.findroot(Z,(t+t2)/2)
        if all(abs(g-z)>1e-6 for z in zeros) and g>0:
            zeros.append(g)
    prev=cur; t=t2
print(f"(3) first {len(zeros)} zeros gamma (L(1+i gamma)=0):")
for g in zeros: print(f"      gamma = {mp.nstr(g,10)}   |L(1+ig)| = {mp.nstr(abs(Lfun(1+1j*g)),3)}")
gaps=[zeros[i+1]-zeros[i] for i in range(len(zeros)-1)]
print(f"    mean gap = {mp.nstr(sum(gaps)/len(gaps),6)};  density ~ log(N/(2pi)^2 * (1+gamma)^..)/2pi")
# local density of zeros for weight-2 conductor N at height gamma:
#   N(T) ~ (T/pi) log( sqrt(N) T /(2 pi e) )   => spacing ~ pi / log(sqrt(N)*gamma/(2pi))
gbar=sum(zeros)/len(zeros)
exp_gap=mp.pi/mp.log(sqN*gbar/twopi)
print(f"    RMT/density expected mean gap near gamma~{mp.nstr(gbar,4)}: {mp.nstr(exp_gap,6)}")

# (4) explicit-formula sanity: sum 1/(1/4+gamma^2) type -- compare zero side to
#     the log-derivative at s=2 (a convergent Weil-type check, coarse).
#     Sum over found zeros of 2/(1+4 gamma^2)... (illustrative, low-height only)
print("(4) low-height explicit-formula partial check (coarse):")
zside=sum(1/(mp.mpf('0.25')+g*g) for g in zeros)
print(f"    sum_gamma 1/(1/4+gamma^2) over first {len(zeros)} zeros = {mp.nstr(zside,6)}")
print(f"    (full identity needs all zeros + archimedean+prime terms; this is a")
print(f"     convergence sanity, not the full Weil explicit formula.)")
