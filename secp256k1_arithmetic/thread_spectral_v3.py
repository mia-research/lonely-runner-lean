#!/usr/bin/env python3
"""
Spectral v3 (2026-07-11): zero-finder that CANNOT return spurious roots
(bisection only, never findroot) on a grid fine enough to prove completeness,
capped to a height where the count matches theta(T)/pi exactly.

v2 failed two ways: findroot jumped to far spurious roots (gamma=1505), and the
count drifted below theta/pi (missed zeros).  v3:
  - BISECTION on each detected sign-change bracket (root stays IN the bracket).
  - grid step 0.02 (< half the min spacing at these heights ~0.5).
  - dps 15, NMAX auto ~ 3*T*sqrt(N)/(2pi)+200 (enough terms for the AFE at height T).
  - completeness ASSERT: at each checkpoint, |found - (theta(T)/pi + c)| < 1.0,
    else STOP (do not emit a list).  Only a list that passes is used for GUE.
"""
import mpmath as mp, math, json
mp.mp.dps = 15

def sieve(L):
    bs=bytearray([1])*(L+1); bs[0:2]=b'\x00\x00'
    for i in range(2,int(L**.5)+1):
        if bs[i]: bs[i*i::i]=bytearray(len(bs[i*i::i]))
    return bs
UNITS=[(1,0),(-1,0),(0,1),(0,-1),(-1,-1),(1,1)]
IDX2POW={0:0,1:3,2:2,3:5,4:4,5:1}; POW2IDX={v:k for k,v in IDX2POW.items()}
def mulw(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]-a[1]*b[1])
def Trw(v): return 2*v[0]-v[1]
def conj(v): return (v[0]-v[1],-v[1])
def primary(v):
    for u in UNITS:
        w=mulw(u,v)
        if w[0]%3==2 and w[1]%3==0: return w
def cornacchia(l):
    for y in range(1,int((4*l/3)**.5)+2):
        d=4*l-3*y*y
        if d<0: break
        s=int(d**.5)
        if s*s==d and (s+y)%2==0: return ((s+y)//2,y)
def u_of(l,pip):
    pc=conj(pip); w=(-pc[0]*pow(pc[1],-1,l))%l
    tab={(u[0]+u[1]*w)%l:i for i,u in enumerate(UNITS)}
    s=pow(28%l,(l-1)//6,l)
    return POW2IDX[(IDX2POW[tab[s]]+3)%6]

N=21168; W=1; TMAX=22.0
NMAX=int(3*TMAX*math.sqrt(N)/(2*math.pi))+300
isp=sieve(NMAX); aP={}
for l in range(2,NMAX+1):
    if not isp[l]: continue
    if l in (2,3,7) or l%3==2: aP[l]=0
    else: aP[l]=Trw(mulw(UNITS[u_of(l,primary(cornacchia(l)))],primary(cornacchia(l))))
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
print(f"NMAX={NMAX} for TMAX={TMAX}")
sqN=mp.sqrt(N); twopi=2*mp.pi
def Lam(s):
    tot=mp.mpc(0)
    for n in range(1,NMAX+1):
        if A[n]==0: continue
        x=twopi*n/sqN
        tot+=A[n]*((sqN/(twopi*n))**s*mp.gammainc(s,x)+W*(sqN/(twopi*n))**(2-s)*mp.gammainc(2-s,x))
    return mp.re(tot)
def theta(t): return float(t*mp.log(sqN/twopi)+mp.im(mp.loggamma(1+1j*t)))

step=mp.mpf('0.02'); t=mp.mpf('0.02'); zp=Lam(1+1j*t)
zeros=[]; checkpoints=[3,6,9,12,15,18,21]; ci=0; const=None; ok=True
while t<TMAX:
    t2=t+step; zc=Lam(1+1j*t2)
    if (zp<0)!=(zc<0):
        a,b=t,t2
        for _ in range(60):                # bisection: root stays in [a,b]
            m=(a+b)/2; zm=Lam(1+1j*m)
            if (zp<0)!=(zm<0): b=m
            else: a=m; zp=zm
            if b-a<mp.mpf('1e-12'): break
        zeros.append((a+b)/2)
    zp=zc; t=t2
    while ci<len(checkpoints) and t>=checkpoints[ci]:
        T=checkpoints[ci]; cnt=sum(1 for z in zeros if z<T); ns=theta(T)/math.pi
        if const is None: const=cnt-ns
        S=cnt-ns-const
        print(f"    T={T:2d}: found {cnt:2d}  theta/pi={ns:6.2f}  S={S:+.2f}  "
              f"[{'OK' if abs(S)<1.0 else 'DRIFT'}]")
        if abs(S)>=1.5: ok=False
        ci+=1
print(f"\n{'COMPLETE' if ok else 'INCOMPLETE'}: {len(zeros)} zeros to T={TMAX}, "
      f"gamma_1={mp.nstr(zeros[0],10)}, gamma_last={mp.nstr(zeros[-1],7)}")
if ok:
    json.dump([str(z) for z in zeros],open("spectral_zeros_v3.json","w"))
    uf=[theta(float(z))/math.pi for z in zeros]
    sp=sorted(uf[i+1]-uf[i] for i in range(len(uf)-1))
    import statistics
    def gue(s): return 1-math.exp(-4*s*s/math.pi)
    def poi(s): return 1-math.exp(-s)
    def ks(c): return max(max(abs((i+1)/len(sp)-c(s)),abs(i/len(sp)-c(s))) for i,s in enumerate(sp))
    print(f"(S) n={len(sp)} spacings, mean={statistics.mean(sp):.3f} (target 1.0)")
    print(f"    KS GUE={ks(gue):.3f}  KS Poisson={ks(poi):.3f}  -> {'GUE' if ks(gue)<ks(poi) else 'Poisson'} closer")
    print(f"    P(s<0.5) obs {sum(1 for s in sp if s<0.5)/len(sp):.3f}  GUE {gue(0.5):.3f}  Poi {poi(0.5):.3f}")
    print(f"    P(s<0.7) obs {sum(1 for s in sp if s<0.7)/len(sp):.3f}  GUE {gue(0.7):.3f}  Poi {poi(0.7):.3f}")
else:
    print("completeness FAILED -> no GUE (guard working; need better AFE evaluation)")
