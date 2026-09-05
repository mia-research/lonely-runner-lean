import random,sys
exec(open('ell_mi_v3f.py').read().split('# ==== MACHINERY M0 ====')[0])   # defs only
def MI(js,ks):
    from math import log
    from collections import Counter
    N=len(js); j=Counter(js);k=Counter(ks);jt=Counter(zip(js,ks));I=0.0
    for (a,b),c in jt.items(): I+=(c/N)*log((c/N)/((j[a]/N)*(k[b]/N)))
    return I
def Tstat(js,ks,ell):
    from collections import Counter
    N=len(js);best=0.0
    for b in range(1,ell):
        d=Counter((x-b*y)%ell for x,y in zip(js,ks))
        chi=sum((d.get(r,0)-N/ell)**2/(N/ell) for r in range(ell))
        if chi>best:best=chi
    return best
def permp(js,ks,ell,stat,rnd,sh=20000):
    obs=stat(js,ks,ell) if stat is Tstat else stat(js,ks)
    kl=list(ks);ge=0
    for _ in range(sh):
        rnd.shuffle(kl)
        v=stat(js,kl,ell) if stat is Tstat else stat(js,kl)
        if v>=obs-1e-12: ge+=1
    return obs,(ge+1)/(sh+1)
rnd=random.Random(777333)   # FRESH seed, independent of v3
print("=== OOS RETEST: fresh seed, 32-bit p, N=12000, 20k shuffles ===")
print(f"  {'ell':>3} {'N':>6} {'MI p':>8} {'T p':>8}   verdict")
for ell in (5,7,11,13):
    js,ks,csr,meta=build_arm(3,ell,12000,32,rnd)
    _,pmi=permp(js,ks,ell,MI,rnd); _,pt=permp(js,ks,ell,Tstat,rnd)
    v="** MI<0.01 **" if pmi<0.01 else ("MI<0.05" if pmi<0.05 else "null")
    print(f"  {ell:>3} {len(js):>6} {pmi:>8.4f} {pt:>8.4f}   {v}")
    sys.stdout.flush()
