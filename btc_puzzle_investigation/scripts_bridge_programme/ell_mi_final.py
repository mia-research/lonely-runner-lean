import random,sys
from math import log,gcd
from collections import Counter
exec(open('ell_mi_v3f.py').read().split('# ==== MACHINERY M0 ====')[0])
def MI(js,ks):
    N=len(js); j=Counter(js);k=Counter(ks);jt=Counter(zip(js,ks));I=0.0
    for (a,b),c in jt.items(): I+=(c/N)*log((c/N)/((j[a]/N)*(k[b]/N)))
    return I
def Tstat(js,ks,ell):
    N=len(js);best=0.0
    for b in range(1,ell):
        d=Counter((x-b*y)%ell for x,y in zip(js,ks))
        best=max(best,sum((d.get(r,0)-N/ell)**2/(N/ell) for r in range(ell)))
    return best
def permp(js,ks,ell,stat,rnd,sh=20000):
    obs=stat(js,ks,ell) if stat is Tstat else stat(js,ks)
    kl=list(ks);ge=0
    for _ in range(sh):
        rnd.shuffle(kl)
        v=stat(js,kl,ell) if stat is Tstat else stat(js,kl)
        if v>=obs-1e-12: ge+=1
    return obs,(ge+1)/(sh+1)
rnd=random.Random(424242)
print("=== ell=13 OOS (the other in-sample low one, was 0.013) + C-cong functionality check ===")
js,ks,csr,meta=build_arm(3,13,9000,30,rnd)
_,pmi=permp(js,ks,13,MI,rnd); _,pt=permp(js,ks,13,Tstat,rnd)
print(f"  ell=13 OOS: N={len(js)}  MI p={pmi:.4f}  T p={pt:.4f}  (in-sample was MI 0.0130)")
# C-cong functionality (fixed rr-coprime): does it now produce instances?
def is_ellpow(u,ell):
    if u<1:return False
    lo,hi=0,1
    while hi**ell<=u:hi<<=1
    while lo+1<hi:
        m=(lo+hi)//2
        if m**ell<=u:lo=m
        else:hi=m
    return lo**ell==u
ell=5; ccj=[];cck=[]
for U,_,_ in meta[:1500]:
    if U<2 or U%ell==0: continue
    rr=rnd.randrange(1,U)
    while gcd(rr,U)>1: rr=rnd.randrange(1,U)
    inv=pow(U%ell,-1,ell); x0=rr+U*(((1-rr)*inv)%ell); step=U*ell
    found=[];v=x0;g=0
    while len(found)<2 and g<4000:
        g+=1
        if v>3 and is_prime(v,bases=(2,3,5,7,11,13)) and U%v: found.append(v)
        v+=step
    if len(found)==2:
        P,Q=found
        zP=pow(lpr(P),(P-1)//ell,P);zQ=pow(lpr(Q),(Q-1)//ell,Q)
        ccj.append(expo(U,P,ell,zP));cck.append(expo(U,Q,ell,zQ))
if len(ccj)>=200:
    _,pcc=permp(ccj,cck,ell,MI,rnd)
    print(f"  C-cong (rr-coprime FIX): produced N={len(ccj)} pairs, MI p={pcc:.4f}  -> control now FUNCTIONAL")
else:
    print(f"  C-cong still short: N={len(ccj)}")
