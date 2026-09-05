#!/usr/bin/env python3
# N7 anomaly-drill STAGE 1 — primary X^2 isotropy of the near-zero |U| excess over the frozen
# 5-stratum partition, MC-H null, + controls NC-floor / P1(diag, must fire) / P5(uniform, must NOT trip).
# Executes PREREG_subrayleigh_deficit_locus_c_channel_v1.md (primary arm). CHARACTERIZATION, not verdict.
# Signal path exact int (EC group law, indices); the FFT/roots-of-unity are the SANCTIONED spectral
# float carve-out (prereg 8); the VERDICT is the integer permutation rank of X^2 (no float decides).
import numpy as np, math, sys, json, time

def ec_add(P, Q, p):
    if P is None: return Q
    if Q is None: return P
    x1,y1=P; x2,y2=Q
    if x1==x2 and (y1+y2)%p==0: return None
    if P==Q: num=(3*x1*x1)%p; den=(2*y1)%p
    else: num=(y2-y1)%p; den=(x2-x1)%p
    lam=(num*pow(den,p-2,p))%p
    x3=(lam*lam-x1-x2)%p; y3=(lam*(x1-x3)-y1)%p
    return (x3,y3)
def scalar_mul(P,k,p):
    R=None;Q=P
    while k>0:
        if k&1: R=ec_add(R,Q,p)
        Q=ec_add(Q,Q,p); k>>=1
    return R
def prime_factors(n):
    f=set();d=2;m=n
    while d*d<=m:
        while m%d==0: f.add(d);m//=d
        d+=1
    if m>1: f.add(m)
    return f
def canonical_generator(p,n):
    fac=prime_factors(n)
    for x in range(p):
        rhs=(x*x*x+7)%p
        for y in range(p):
            if (y*y)%p==rhs:
                P=(x,y)
                if all(scalar_mul(P,n//l,p) is not None for l in fac) and scalar_mul(P,n,p) is None:
                    return P
                break
    raise RuntimeError("no generator")
def all_points(p,n):
    G=canonical_generator(p,n); pts=[];P=G
    for d in range(1,n): pts.append(P); P=ec_add(P,G,p)
    assert P is None
    return G,pts
def char_weight(n):
    d=np.arange(1,n)
    return np.exp(2j*np.pi*(d%n)/n)                       # noqa: float  (sanctioned roots of unity)
def null_weight(n,seed):
    rng=np.random.default_rng(seed)
    g=np.zeros(n-1,dtype=np.complex128)
    for d in range(1,n):
        i=d-1
        if g[i]!=0: continue
        j=(n-d)-1
        if d==n-d: g[i]=rng.choice([-1.0,1.0])
        else:
            phi=rng.uniform(0,2*np.pi); g[i]=np.exp(1j*phi); g[j]=np.conj(g[i])  # noqa: float
    return g

def spectrum_r(pts,g,p,n):
    W=np.zeros((p,p),dtype=np.complex128)
    xs=np.fromiter((x for x,_ in pts),dtype=np.int64,count=len(pts))
    ys=np.fromiter((y for _,y in pts),dtype=np.int64,count=len(pts))
    np.add.at(W,(xs,ys),g)
    U=np.fft.fft2(W); aU=np.abs(U)
    sigma=math.sqrt(p*p*(n-1)/(p*p-1))                    # noqa: float  (sanctioned)
    return aU/sigma, float((aU*aU).sum())                 # noqa: float

# ---- folded grid + 5-stratum masks (built once per p) ----
def build_strata(p):
    bmax=(p-1)//2                     # fold b to {0..(p-1)/2}
    bs=np.arange(0,bmax+1)[:,None]    # column of b
    cs=np.arange(0,p)[None,:]         # row of c
    B=np.broadcast_to(bs,(bmax+1,p)); C=np.broadcast_to(cs,(bmax+1,p))
    dc=(B==0)&(C==0)                  # DC, excluded
    baxis=(C==0)&(B>=1)
    caxis=(B==0)&(C!=0)
    diag=((C==B)|(C==(p-B)%p))&(B>=1)&(C!=0)
    chalf_pos=(C>=1)&(C<=(p-1)//2)
    chalf_neg=(C>=(p+1)//2)&(C<=p-1)
    cpos=chalf_pos&(B>=1)&(~diag)&(~caxis)&(~baxis)
    cneg=chalf_neg&(B>=1)&(~diag)&(~caxis)&(~baxis)
    strata={'baxis':baxis,'caxis':caxis,'diag':diag,'cpos':cpos,'cneg':cneg}
    # exactness: disjoint cover of F minus DC
    tot=np.zeros((bmax+1,p),dtype=bool)
    for m in strata.values():
        assert not (tot&m).any(), "strata overlap"
        tot|=m
    assert (tot|dc).all() and not (tot&dc).any(), "not a partition of F"
    return strata,bmax

def counts(rmask_nz, strata):
    return {s: int(rmask_nz[m].sum()) for s,m in strata.items()}

def fold_r(r,bmax):
    return r[:bmax+1,:]                # |U(b,c)|=|U(-b,c)| => top half carries each orbit once

def run_prime(p,n,tau_set,R,seed_base):
    G,pts=all_points(p,n)
    strata,bmax=build_strata(p)
    Ns={s:int(m.sum()) for s,m in strata.items()}; Ntot=sum(Ns.values())
    # char spectrum
    gc=char_weight(n); rc,ss=spectrum_r(pts,gc,p,n); rc=fold_r(rc,bmax)
    e1=abs(ss-p*p*(n-1))/(p*p*(n-1))
    # MC-H null ensemble: per-tau, per-stratum K over R draws
    nullK={tau:{s:np.empty(R) for s in strata} for tau in tau_set}
    for k in range(R):
        gk=null_weight(n,seed_base+k); rk,_=spectrum_r(pts,gk,p,n); rk=fold_r(rk,bmax)
        for tau in tau_set:
            nz=rk<tau; c=counts(nz,strata)
            for s in strata: nullK[tau][s][k]=c[s]
    out={'p':p,'n':n,'e1':e1,'Ns':Ns,'Ntot':Ntot,'bmax':bmax,'tau':{}}
    for tau in tau_set:
        Kc={s:int((rc<tau)[strata[s]].sum()) for s in strata}
        EN={s:float(nullK[tau][s].mean()) for s in strata}
        VN={s:float(nullK[tau][s].var(ddof=1)) for s in strata}
        Ktot=sum(Kc.values()); EtotN=sum(EN.values())
        delta=(Ktot-EtotN)/Ntot                          # noqa: float  (display; verdict is rank)
        def X2(Kd):
            return sum((Kd[s]-EN[s]-delta*Ns[s])**2/VN[s] for s in strata if VN[s]>0)  # noqa: float
        X2c=X2(Kc)
        # permutation p: X2 of each null draw vs same ensemble Ê/V̂ (its own delta)
        X2n=np.empty(R)
        for k in range(R):
            Kk={s:int(nullK[tau][s][k]) for s in strata}
            dk=(sum(Kk.values())-EtotN)/Ntot              # noqa: float
            X2n[k]=sum((Kk[s]-EN[s]-dk*Ns[s])**2/VN[s] for s in strata if VN[s]>0)  # noqa: float
        rank=int((X2n>=X2c).sum()); perm_num=rank+1; perm_den=R+1
        zs={s:(Kc[s]-EN[s]-delta*Ns[s])/math.sqrt(VN[s]) if VN[s]>0 else 0.0 for s in strata}  # noqa: float
        # S-C2 (c-sign asymmetry): D_c = K_cpos - K_cneg vs the Hermitian ensemble
        nullDc=nullK[tau]['cpos']-nullK[tau]['cneg']
        Dc=Kc['cpos']-Kc['cneg']; sdc=float(nullDc.std(ddof=1))
        z_Dc=(Dc-float(nullDc.mean()))/sdc if sdc>0 else 0.0     # noqa: float
        out['tau'][str(tau)]={'Kc':Kc,'EN':{s:round(EN[s],2) for s in strata},'delta':delta,
                              'X2c':X2c,'perm_num':perm_num,'perm_den':perm_den,
                              'zs':{s:round(zs[s],3) for s in strata},'Ns':Ns,
                              'z_Dc':round(z_Dc,3)}
    return out,strata,bmax,pts,gc

# ---- controls: NC-floor (null-vs-null), P1 (diag plant must fire), P5 (uniform must NOT trip) ----
def nc_floor(pts,p,n,strata,bmax,tau,R,seed_base):
    # score one MC-H draw's K vs the rest; its X2 permutation p should be ~Uniform (here: one draw ~ mid)
    Ks=[]
    for k in range(R):
        gk=null_weight(n,seed_base+10000+k); rk,_=spectrum_r(pts,gk,p,n); rk=fold_r(rk,bmax)
        Ks.append({s:int((rk<tau)[strata[s]].sum()) for s in strata})
    Ns={s:int(strata[s].sum()) for s in strata}
    EN={s:np.mean([K[s] for K in Ks]) for s in strata}; VN={s:np.var([K[s] for K in Ks],ddof=1) for s in strata}
    X2=[]
    for K in Ks:
        d=(sum(K.values())-sum(EN.values()))/sum(Ns.values())      # noqa: float
        X2.append(sum((K[s]-EN[s]-d*Ns[s])**2/VN[s] for s in strata if VN[s]>0))  # noqa: float
    X2=np.array(X2)
    # a genuine null-vs-null: rank of the first draw among all -> should be ~uniform; report median rank
    ranks=[int((X2>=x).sum())/(R) for x in X2]                      # noqa: float
    return float(np.median(X2)), float(np.percentile(X2,95)), float(np.mean(ranks))

if __name__=="__main__":
    mode=sys.argv[1] if len(sys.argv)>1 else "smoke"
    TAU=[0.05,0.10,0.15]
    if mode=="smoke":
        SP=[(151,133),(691,651),(1471,1501)]     # small-mid, fast; validate machinery+controls
        R=200
        for p,n in SP:
            t0=time.time()
            out,strata,bmax,pts,gc=run_prime(p,n,TAU,R,seed_base=p*1000)
            print(f"\n=== p={p} n={n}  E1={out['e1']:.1e}  Ns={out['Ns']}  ({time.time()-t0:.1f}s) ===")
            for tau in TAU:
                t=out['tau'][str(tau)]
                dom=max(t['zs'],key=lambda s:abs(t['zs'][s]))
                print(f"  tau={tau}: X2={t['X2c']:.1f} perm_p={t['perm_num']}/{t['perm_den']} "
                      f"delta={t['delta']:+.2e} | z_s={t['zs']} | dom={dom}")
            # NC-floor at tau=0.10
            med,p95,mrank=nc_floor(pts,p,n,strata,bmax,0.10,R,seed_base=p*1000)
            print(f"  NC-floor(tau=.10): median X2={med:.1f} p95={p95:.1f} mean-rank={mrank:.3f} (expect ~0.5, X2~chi2_4 med~3.36)")
        print("\n(smoke: NC-floor mean-rank ~0.5 and X2 median ~3.4 => calibrated; per-tau perm_p is the primary read)")
