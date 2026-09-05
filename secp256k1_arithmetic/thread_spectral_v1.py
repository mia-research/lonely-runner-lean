#!/usr/bin/env python3
"""
Spectral dig-in (2026-07-11): are the zeros of L(psi,s)=L(E,s) (E:y^2=x^3+7,
N=21168, W=+1) consistent with being the spectrum of a self-adjoint operator
(Hilbert-Polya)?  Disciplined: compute the objects, test with matched controls,
map proven-vs-open.  No operator is claimed.

Tests:
  (Z) compute ~40 zero ordinates gamma_i on Re(s)=1.
  (N) Riemann-von Mangoldt counting: #{gamma<T} vs (T/pi)log(sqrt(N)T/(2 pi e)).
  (S) nearest-neighbour spacing of UNFOLDED zeros vs GUE Wigner surmise vs
      Poisson (matched control = Poisson process, same count).
  (P) Montgomery pair-correlation (coarse histogram) vs 1-(sin(pi u)/(pi u))^2.
  (W) explicit-formula duality (smoothed): the zero-counting IS the integrated
      Weil formula; report residual.  Plus the log-derivative sum
      sum 1/(1+gamma^2) (converged tail estimated) as a coarse two-sided check.
Output saved to spectral_zeros.json for reuse.
"""
import mpmath as mp, math, json, os
mp.mp.dps = 18

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

N=21168; W=1; NMAX=2500
isp=sieve(NMAX); aP={}
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
    if mm>1: r*=(0 if mm in (2,3,7) else aP[mm])
    return r
A=[0]*(NMAX+1)
for m in range(1,NMAX+1): A[m]=a_n(m)
sqN=mp.sqrt(N); twopi=2*mp.pi
def Lambda(s):
    tot=mp.mpc(0)
    for n in range(1,NMAX+1):
        if A[n]==0: continue
        x=twopi*n/sqN
        tot+=A[n]*((sqN/(twopi*n))**s*mp.gammainc(s,x)+W*(sqN/(twopi*n))**(2-s)*mp.gammainc(2-s,x))
    return tot
def Z(t): return mp.re(Lambda(1+1j*t))

CACHE="spectral_zeros.json"
NZ=40
if os.path.exists(CACHE):
    zeros=[mp.mpf(z) for z in json.load(open(CACHE))]
else:
    zeros=[]; t=mp.mpf('0.1'); prev=Z(t); step=mp.mpf('0.08')
    while len(zeros)<NZ and t<60:
        t2=t+step; cur=Z(t2)
        if (prev<0)!=(cur<0):
            g=mp.findroot(Z,(t+t2)/2)
            if g>0 and all(abs(g-z)>1e-6 for z in zeros): zeros.append(g)
        prev=cur; t=t2
    json.dump([str(z) for z in zeros], open(CACHE,"w"))
print(f"(Z) computed {len(zeros)} zeros; gamma_1={mp.nstr(zeros[0],10)}, "
      f"gamma_{len(zeros)}={mp.nstr(zeros[-1],8)}")

# (N) counting vs Riemann-von Mangoldt
def Nmain(T):  # expected # zeros with 0<gamma<T for degree-2 conductor N
    return float((T/mp.pi)*mp.log(sqN*T/twopi) - (T/mp.pi))
print("\n(N) counting  #{gamma<T} vs (T/pi)(log(sqrtN T/2pi) - 1):")
for T in (5,10,15,20,25):
    cnt=sum(1 for z in zeros if z<T)
    print(f"    T={T:3d}: actual {cnt:3d}   main term {Nmain(T):6.2f}   diff {cnt-Nmain(T):+.2f}")

# unfolding: map gamma_i -> Nmain(gamma_i) so mean spacing = 1
uf=[Nmain(float(z)) for z in zeros]
sp=[uf[i+1]-uf[i] for i in range(len(uf)-1)]
sp=[s for s in sp if s>0]
import statistics
print(f"\n(S) unfolded spacings: n={len(sp)}, mean={statistics.mean(sp):.4f} (target 1.0)")
# GUE Wigner surmise CDF vs Poisson CDF, KS-style bucketed
def gue_cdf(s): return 1-math.exp(-4*s*s/math.pi)   # approx Wigner (beta=2 surmise)
def poi_cdf(s): return 1-math.exp(-s)
import bisect
sps=sorted(sp)
def ks(cdf):
    D=0
    for i,s in enumerate(sps):
        Fe=(i+1)/len(sps); D=max(D,abs(Fe-cdf(s)),abs(i/len(sps)-cdf(s)))
    return D
print(f"    KS distance to GUE(Wigner) = {ks(gue_cdf):.3f};  to Poisson = {ks(poi_cdf):.3f}")
print(f"    (smaller = better fit; GUE<Poisson => level repulsion, HP-consistent)")
# fraction of small spacings (repulsion signature): P(s<0.5)
small=sum(1 for s in sp if s<0.5)/len(sp)
print(f"    P(spacing<0.5): observed {small:.3f}; GUE {gue_cdf(0.5):.3f}; Poisson {poi_cdf(0.5):.3f}")

# (P) pair correlation (coarse): histogram of unfolded differences uf_j-uf_i in (0,3]
diffs=[uf[j]-uf[i] for i in range(len(uf)) for j in range(i+1,len(uf)) if uf[j]-uf[i]<=3]
import collections
bins=collections.Counter(int(d//0.5) for d in diffs)
print(f"\n(P) pair-correlation histogram (bin=0.5, count of unfolded gaps):")
for b in range(6):
    u=(b+0.5)*0.5
    montg=1-(math.sin(math.pi*u)/(math.pi*u))**2 if u>0 else 0
    print(f"    u~{u:.2f}: count {bins.get(b,0):3d}   Montgomery 1-(sin/..)^2={montg:.3f}")

# (W) coarse two-sided: sum 1/(1+gamma^2) over computed zeros (partial, +tail est)
partial=sum(1/(1+float(z)**2) for z in zeros)
# tail beyond last zero via density integral: int_{T0}^inf density(t)/(1+t^2) dt
T0=float(zeros[-1])
tail=float(mp.quad(lambda t: (1/mp.pi)*mp.log(sqN*t/twopi)/(1+t*t), [T0,mp.inf]))
print(f"\n(W) sum_gamma 1/(1+gamma^2): partial(40 zeros)={partial:.4f} + tail~{tail:.4f} "
      f"= {partial+tail:.4f}")
print("    (this equals Re[-L'/L(2)] + archimedean, the explicit-formula value;")
print("     a full check needs the exact archimedean constant -- flagged, not claimed.)")
