#!/usr/bin/env python3
"""PREREG_ell_ge5_mutual_information_v2 -- full run with R1/R2/R3/N1 fixes.
Exact integers for number theory; MI/T are monotone statistics vs exact permutation nulls."""
from math import isqrt, log
import random, sys
from collections import Counter
exec(open('cubic_bridge_v1.py').read().split('print("=== CONTROLS ===")')[0])  # is_prime, cornacchia3, instance, etc.

def tonelli(a,p):
    a%=p
    if a==0: return 0
    if pow(a,(p-1)//2,p)!=1: return None
    if p%4==3: return pow(a,(p+1)//4,p)
    q,s=p-1,0
    while q%2==0: q//=2; s+=1
    z=2
    while pow(z,(p-1)//2,p)!=p-1: z+=1
    m,c,t,r=s,pow(z,q,p),pow(a,q,p),pow(a,(q+1)//2,p)
    while t!=1:
        i,t2=0,t
        while t2!=1: t2=t2*t2%p; i+=1
        b=pow(c,1<<(m-i-1),p); m,c=i,b*b%p; t=t*c%p; r=r*b%p
    return r
def cornacchia_D(p,absD):
    D=-absD
    if pow(D%p,(p-1)//2,p)!=1: return None
    x0=tonelli(D%p,p)
    if x0 is None: return None
    if (x0-D)%2: x0=p-x0
    a,b=2*p,x0; c=isqrt(4*p)
    while b>c: a,b=b,a%b
    r=4*p-b*b
    if r%absD: return None
    v2=r//absD; v=isqrt(v2)
    return (b,v) if v*v==v2 and v>0 else None
def lpr(p):
    fac=[]; m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
def expo(base,mod,ell,zeta):
    val=pow(base%mod,(mod-1)//ell,mod); z=1
    for jj in range(ell):
        if z==val: return jj
        z=z*zeta%mod
    raise AssertionError

# ---------- statistics ----------
def MI(js,ks):
    N=len(js); j=Counter(js);k=Counter(ks);jt=Counter(zip(js,ks));I=0.0
    for (a,b),c in jt.items(): I+=(c/N)*log((c/N)/((j[a]/N)*(k[b]/N)))
    return I
def Tstat(js,ks,ell):   # choice-free targeted shift statistic (N1)
    N=len(js); best=0.0
    for b in range(1,ell):
        d=Counter((x-b*y)%ell for x,y in zip(js,ks))
        chi=sum((d.get(r,0)-N/ell)**2/(N/ell) for r in range(ell))
        if chi>best: best=chi
    return best
def permp(js,ks,ell,stat,rnd,sh=10000):
    obs=stat(js,ks,ell) if stat is Tstat else stat(js,ks)
    kl=list(ks); ge=0
    for _ in range(sh):
        rnd.shuffle(kl)
        v=stat(js,kl,ell) if stat is Tstat else stat(js,kl)
        if v>=obs-1e-12: ge+=1
    return obs,(ge+1)/(sh+1)

# ---------- sample builder ----------
def build_arm(absD,ell,target,bits,rnd,cap=3000000):
    """one uniformly-chosen prime-order twist per p (N5). returns js,ks and also (U,p,n) meta."""
    js=[];ks=[];csr=[];meta=[]
    tries=0
    while len(js)<target and tries<cap:
        tries+=1
        p=rnd.randrange(1<<(bits-1),1<<bits); p-=(p%ell)-1
        if p%2==0: p+=ell
        if p%ell!=1 or p%3!=1 or p<7 or not is_prime(p,bases=(2,3,5,7,11,13)): continue
        if absD==3:
            rep=cornacchia3(p,rnd)
            if not rep: continue
            a,b=rep
            if a*a+3*b*b!=p: continue
            ts=[a+3*b,-(a+3*b),a-3*b,-(a-3*b)]
        else:
            rep=cornacchia_D(p,absD)
            if not rep: continue
            t0,v=rep; ts=[t0,-t0]
        cand=[]
        for t in ts:
            n=p+1-t
            if n<=3 or n%ell!=1 or t==1: continue
            if not is_prime(n,bases=(2,3,5,7,11,13)): continue
            if p%n==0: continue
            cand.append((t,n))
        if not cand: continue
        t,n=cand[rnd.randrange(len(cand))]
        zn=pow(lpr(n),(n-1)//ell,n); zp=pow(lpr(p),(p-1)//ell,p)
        j=expo(p,n,ell,zn); k=expo(n,p,ell,zp)
        js.append(j);ks.append(k)
        csr.append(pow(rnd.randrange(2,n),(n-1)//ell,n))  # random-base numerator (for C-r)
        meta.append((abs(t-1),p,n))
    return js,ks,csr,meta

# ================= MACHINERY (R1-fixed M0, M1, N2) =================
print("=== M0 (R1-fixed): MI + T invariant under UNIT relabelings ===")
rnd=random.Random(10); ell=7
js=[rnd.randrange(ell) for _ in range(3000)]; ks=[(2*j+rnd.randrange(3))%ell for j in js]
b0=MI(js,ks); t0=Tstat(js,ks,ell); okmi=okt=True
for a,b in ((2,3),(3,5),(6,4)):  # all units mod 7
    j2=[(a*j)%ell for j in js]; k2=[(b*k)%ell for k in ks]
    okmi&=abs(MI(j2,k2)-b0)<1e-12; okt&=abs(Tstat(j2,k2,ell)-t0)<1e-12
print(f"  MI choice-free: {okmi}   T choice-free: {okt}")

# ================= R2: INJECTION POWER on real-ish marginals =================
print("\n=== R2: injected shift-bridge detection (min s at ~80% power), N=8000 ===")
print(f"  {'ell':>3} {'MI 50%s':>8} {'MI 80%s':>8} {'T 50%s':>8} {'T 80%s':>8}   (s=P(C=0); s=1/ell is null)")
rnd=random.Random(11)
for ell in (5,7,11,13):
    N=8000
    row={}
    for stat,nm in ((MI,'MI'),(Tstat,'T')):
        detect={}
        for s in (1/ell,0.22,0.30,0.42):
            hits=0; R=25
            for _ in range(R):
                ks=[rnd.randrange(ell) for _ in range(N)]
                js=[k if rnd.random()<s else rnd.randrange(ell) for k in ks]  # shift with P(C=0)=s (+ uniform noise)
                _,pv=permp(js,ks,ell,stat,rnd,sh=400)
                hits+=(pv<0.01)
            detect[s]=hits/R
        # min s reaching 0.5 / 0.8
        s50=min([s for s in sorted(detect) if detect[s]>=0.5], default=None)
        s80=min([s for s in sorted(detect) if detect[s]>=0.8], default=None)
        row[nm]=(s50,s80)
    print(f"  {ell:>3} {str(row['MI'][0]):>8} {str(row['MI'][1]):>8} {str(row['T'][0]):>8} {str(row['T'][1]):>8}")
    sys.stdout.flush()

# ================= CONTROLS on real data =================
print("\n=== C+ / C- controls (ell=3) ===")
rnd=random.Random(12)
for absD,lbl,exp in ((3,'C+ D=-3 (bridge KNOWN)','ASSOC'),(11,'C- D=-11 (no bridge)','null')):
    js,ks,csr,meta=build_arm(absD,3,4000,26,rnd)
    _,pmi=permp(js,ks,3,MI,rnd); _,pt=permp(js,ks,3,Tstat,rnd)
    print(f"  {lbl:<26} N={len(js)}  MI p={pmi:.4f}  T p={pt:.4f}  [{exp}]")
    sys.stdout.flush()

# ================= ARMS ell=5,7,11,13 at D=-3 + C-r + C-cong =================
print("\n=== ARMS: ell in {5,7,11,13}, D=-3, N target 8000 ===")
print(f"  {'ell':>3} {'N':>6} {'MI p':>8} {'T p':>8} {'C-r MI p':>9} {'C-cong MI p':>11} {'#U cube':>8}")
rnd=random.Random(13)
def is_ellpow(u,ell):
    if u<1: return False
    lo,hi=0,1
    while hi**ell<=u: hi<<=1
    while lo+1<hi:
        m=(lo+hi)//2
        if m**ell<=u: lo=m
        else: hi=m
    return lo**ell==u
for ell in (5,7,11,13):
    js,ks,csr,meta=build_arm(3,ell,8000,30,rnd)
    _,pmi=permp(js,ks,ell,MI,rnd); _,pt=permp(js,ks,ell,Tstat,rnd)
    # C-r: random-base numerator vs k
    csr_j=[expo_from_pow(v,meta[i][2],ell) if False else None for i,v in enumerate(csr)]
    # csr holds pow(r,(n-1)/ell,n); convert to exponent with same zeta as j used (recompute zeta_n)
    cr_j=[]
    for i,v in enumerate(csr):
        n=meta[i][2]; zn=pow(lpr(n),(n-1)//ell,n); z=1
        for jj in range(ell):
            if z==v%n: cr_j.append(jj); break
            z=z*zn%n
        else: cr_j.append(0)
    _,pcr=permp(cr_j,ks,ell,MI,rnd)
    ncube=sum(1 for U,_,_ in meta if is_ellpow(U,ell))
    # C-cong (R3): for each U draw two INDEPENDENT primes P=Q=rr (mod U), both =1 mod ell;
    #   symbols of the SAME U -> keeps the shared-U congruence, breaks the CM tie.
    #   Start from the smallest CRT residue and walk by U*ell (first prime in ~ln steps).
    ccj=[];cck=[]
    for U,_,_ in meta[:1500]:
        if U<2 or U%ell==0: continue
        rr=rnd.randrange(1,U)                       # random common residue mod U
        # x = rr (mod U), x = 1 (mod ell) via CRT; step = U*ell
        inv=pow(U%ell,-1,ell)
        x0=(rr + U*(((1-rr)*inv)%ell))              # smallest >0 solution
        step=U*ell
        found=[]; v=x0; guard=0
        while len(found)<2 and guard<4000:
            guard+=1
            if v>3 and is_prime(v,bases=(2,3,5,7,11,13)) and U%v: found.append(v)
            v+=step
        if len(found)==2:
            P,Q=found
            zP=pow(lpr(P),(P-1)//ell,P); zQ=pow(lpr(Q),(Q-1)//ell,Q)
            ccj.append(expo(U,P,ell,zP)); cck.append(expo(U,Q,ell,zQ))
    pcc=permp(ccj,cck,ell,MI,rnd)[1] if len(ccj)>=200 else float('nan')
    print(f"  {ell:>3} {len(js):>6} {pmi:>8.4f} {pt:>8.4f} {pcr:>9.4f} {pcc:>11.4f} {ncube:>8} (C-cong N={len(ccj)})")
    sys.stdout.flush()
