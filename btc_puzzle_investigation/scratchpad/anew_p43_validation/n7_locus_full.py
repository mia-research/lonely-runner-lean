#!/usr/bin/env python3
# N7 anomaly-drill STAGE 2 — full pooled run over the 30 frozen model primes.
# Primary X^2 isotropy + per-stratum pooled Stouffer + S-C2 (c-sign) + NC-sqrtN artifact guard,
# with P1 (diag concentration MUST fire) and P5 (uniform rate MUST NOT trip X^2) plant validation.
# Executes PREREG_subrayleigh_deficit_locus_c_channel_v1.md (location arms). CHARACTERIZATION, not verdict.
# Verdict path integer (permutation rank, pooled Stouffer of integer-count-derived z); FFT is the
# sanctioned spectral float carve-out. Co-occurrence arms (S-Cpair/S-mu6, MC-GR) deferred to a follow-up.
import numpy as np, math, json, time, sys
from n7_locus_drill import (all_points, char_weight, null_weight, spectrum_r,
                            build_strata, fold_r)

PRIMES=[151,193,211,241,277,349,397,433,523,619,691,823,937,1093,1249,
        1471,1693,1987,2281,2671,3169,3607,4177,4861,5647,6571,7639,8893,10357,12043]
ORDERS=[133,219,199,259,273,313,397,397,489,669,651,829,973,1137,1303,
        1501,1729,2037,2203,2569,3073,3577,4303,4771,5529,6411,7699,9037,10173,12261]
TAU=[0.05,0.10,0.15]
STRATA=['baxis','caxis','diag','cpos','cneg']
def Rfor(p): return 200 if p<2000 else 100 if p<5000 else 50

def ensemble(p,n,R,seed):
    G,pts=all_points(p,n); strata,bmax=build_strata(p)
    Ns={s:int(m.sum()) for s,m in strata.items()}; Ntot=sum(Ns.values())
    gc=char_weight(n); rc,ss=spectrum_r(pts,gc,p,n); rc=fold_r(rc,bmax)
    e1=abs(ss-p*p*(n-1))/(p*p*(n-1))                         # noqa: float
    nullK={tau:{s:np.empty(R) for s in strata} for tau in TAU}
    for k in range(R):
        gk=null_weight(n,seed+k); rk,_=spectrum_r(pts,gk,p,n); rk=fold_r(rk,bmax)
        for tau in TAU:
            nz=rk<tau
            for s in strata: nullK[tau][s][k]=int(nz[strata[s]].sum())
    return dict(strata=strata,Ns=Ns,Ntot=Ntot,rc=rc,nullK=nullK,e1=e1,R=R)

def _X2m(K, Ns, Ntot):
    # CONDITIONAL MULTINOMIAL X^2: condition on K_tot, test allocation vs N_s (rate-invariant).
    Kt=sum(K.values())
    if Kt==0: return 0.0
    return sum((K[s]-Kt*Ns[s]/Ntot)**2/(Kt*(Ns[s]/Ntot)*(1-Ns[s]/Ntot))     # noqa: float
               for s in K if Ns[s]>0 and Ns[s]<Ntot)
def X2_perm(K, Ns, Ntot, nullmat, R):
    X2c=_X2m(K,Ns,Ntot)
    X2n=np.empty(R)
    for k in range(R):
        X2n[k]=_X2m({s:int(nullmat[s][k]) for s in nullmat},Ns,Ntot)
    return X2c, int((X2n>=X2c).sum())+1, R+1
def zstrat(K, Ns, Ntot):
    Kt=sum(K.values())
    return {s:(K[s]-Kt*Ns[s]/Ntot)/math.sqrt(Kt*(Ns[s]/Ntot)*(1-Ns[s]/Ntot))  # noqa: float
            if Ns[s]>0 and Ns[s]<Ntot and Kt>0 else 0.0 for s in K}

def char_K(rc,strata,tau): return {s:int((rc<tau)[strata[s]].sum()) for s in strata}

def run_full():
    per=[]  # per-prime records
    for p,n in zip(PRIMES,ORDERS):
        R=Rfor(p); t0=time.time()
        try:
            ens=ensemble(p,n,R,seed=p*1000+7)
        except MemoryError:
            print(f"p={p}: MemoryError -> SKIP (deviation: pooled over feasible subset)",flush=True); continue
        strata=ens['strata']; Ns=ens['Ns']; Ntot=ens['Ntot']; rc=ens['rc']
        if ens['e1']>1e-6:
            print(f"p={p}: E1 FAIL {ens['e1']:.1e} -> HALT-3 skip",flush=True); continue
        rec={'p':p,'n':n,'R':R,'Ns':Ns,'tau':{}}
        for tau in TAU:
            Kc=char_K(rc,strata,tau)
            X2c,pn,pd=X2_perm(Kc,Ns,Ntot,ens['nullK'][tau],R)
            zs=zstrat(Kc,Ns,Ntot)   # char vs UNIFORM (conflates forced anisotropy; kept for reference)
            # za: char vs NULL ALLOCATION (rate-free) -> isolates CHAR-SPECIFIC concentration beyond
            # the forced geometric anisotropy the null also carries. THIS is the deficit-locus statistic.
            nk=ens['nullK'][tau]; ntot=sum(nk[s] for s in strata); Ktc=sum(Kc.values())
            za={}
            for s in strata:
                ac=Kc[s]/Ktc if Ktc>0 else 0.0                 # noqa: float
                an=nk[s]/ntot                                   # noqa: float  (per-draw allocation)
                sdn=float(an.std(ddof=1))
                za[s]=(ac-float(an.mean()))/sdn if sdn>0 else 0.0   # noqa: float
            nd=ens['nullK'][tau]['cpos']-ens['nullK'][tau]['cneg']
            Dc=Kc['cpos']-Kc['cneg']; sdc=float(nd.std(ddof=1))
            zDc=(Dc-float(nd.mean()))/sdc if sdc>0 else 0.0    # noqa: float
            rec['tau'][tau]={'X2':X2c,'pn':pn,'pd':pd,'zs':zs,'za':za,'zDc':zDc}
        per.append(rec)
        d10=per[-1]['tau'][0.10]
        dom=max(d10['zs'],key=lambda s:abs(d10['zs'][s]))
        print(f"p={p:>6} R={R:>3} tau.10: X2={d10['X2']:5.1f} p={d10['pn']}/{d10['pd']} "
              f"dom={dom}({d10['zs'][dom]:+.2f}) zDc={d10['zDc']:+.2f}  ({time.time()-t0:.0f}s)",flush=True)
    return per

def stouffer(vals): return sum(vals)/math.sqrt(len(vals)) if vals else 0.0   # noqa: float

def pool_and_verdict(per):
    print("\n==================== POOLED (over %d feasible primes) ====================" % len(per))
    for tau in TAU:
        print(f"\n--- tau={tau} ---")
        print("  [PRIMARY: char-vs-NULL allocation 'za' = char-specific locus beyond forced anisotropy]")
        for s in STRATA:
            zav=[r['tau'][tau]['za'][s] for r in per]
            Nsq=[math.sqrt(r['Ns'][s]) for r in per]                        # noqa: float
            Z=stouffer(zav)
            corr=float(np.corrcoef(np.array(zav),np.array(Nsq))[0,1]) if len(zav)>2 and np.array(Nsq).std()>0 else 0.0  # noqa: float
            tag='(RISING=genuine)' if abs(Z)>3 and corr*np.sign(Z)>0.2 else ('(sig, not sqrtN-rising)' if abs(Z)>3 else '(null)')
            print(f"    {s:6s}: Stouffer Z={Z:+7.2f} | NC-sqrtN corr={corr:+.2f} {tag}")
        print("  [reference: char-vs-UNIFORM 'zs' (FORCED anisotropy, shared by null — NOT char-specific)]")
        for s in STRATA:
            zsv=[r['tau'][tau]['zs'][s] for r in per]
            print(f"    {s:6s}: Stouffer Z={stouffer(zsv):+8.2f}")
        zdv=[r['tau'][tau]['zDc'] for r in per]
        Zdc=stouffer(zdv)
        Nsq_bulk=[math.sqrt(r['Ns']['cpos']) for r in per]                  # noqa: float
        corrdc=float(np.corrcoef(np.array(zdv),np.array(Nsq_bulk))[0,1]) if len(zdv)>2 else 0.0  # noqa: float
        print(f"  S-C2 (c-sign D_c): Stouffer Z={Zdc:+6.2f} | NC-sqrtN corr={corrdc:+.2f}")
        # omnibus: fraction of primes with X2 perm_p<0.05
        frac=sum(1 for r in per if r['tau'][tau]['pn']/r['tau'][tau]['pd']<0.05)/len(per)  # noqa: float
        print(f"  X2 omnibus: {frac*100:.0f}% of primes perm_p<0.05 (chance 5%)")

if __name__=="__main__":
    if sys.argv[1:2]==["ncfloor"]:
        # null-vs-null za: score null draw 0 vs the rest; all strata must pool ~0 (calibration of za)
        SP=[(619,669),(937,973),(1471,1501),(1987,2037),(2671,2569),(4177,4303)]
        acc={s:[] for s in STRATA}
        for p,n in SP:
            ens=ensemble(p,n,Rfor(p),seed=p*1000+7); strata=ens['strata']; tau=0.10
            nk=ens['nullK'][tau]; ntot=sum(nk[s] for s in strata)
            for s in strata:
                a0=nk[s][0]/ntot[0]; arest=nk[s][1:]/ntot[1:]                # noqa: float
                sd=float(arest.std(ddof=1))
                acc[s].append((a0-float(arest.mean()))/sd if sd>0 else 0.0)  # noqa: float
            print(f"  p={p} done",flush=True)
        print("\nNC-floor za (null-vs-null, tau=.10, 6 primes):")
        for s in STRATA:
            print(f"  {s:6s}: Stouffer={stouffer(acc[s]):+.2f} (expect ~0; |.|>3 => za miscalibrated on that stratum)")
        sys.exit(0)
    if sys.argv[1:2]==["plants"]:
        # P1 (diag must fire) + P5 (uniform must NOT trip) at representative primes
        for p,n in [(691,651),(1471,1501),(2671,2569)]:
            ens=ensemble(p,n,Rfor(p),seed=p*1000+7); strata=ens['strata']; Ns=ens['Ns']; Ntot=ens['Ntot']; rc=ens['rc']
            tau=0.10
            # plant on the ISOTROPIC MEAN null base (no thin-stratum fluctuation) to isolate the injection
            base={s:int(round(float(ens['nullK'][tau][s].mean()))) for s in strata}
            # P1: inject diag concentration (~0.08*N_diag near-zeros in diag only) -> MUST fire, diag-dom
            KP1=dict(base); KP1['diag']=base['diag']+int(0.08*Ns['diag'])
            x1,pn1,pd1=X2_perm(KP1,Ns,Ntot,ens['nullK'][tau],ens['R'])
            z1=zstrat(KP1,Ns,Ntot); dom1=max(z1,key=lambda s:abs(z1[s]))
            # P5: UNIFORM per-cell injection on the clean base (common Bernoulli rate) -> X2 must NOT trip.
            f=sum(base.values())/Ntot; q=(0.08*f)/(1-f); rng=np.random.default_rng(p*99+1)
            KP5={s:base[s]+int(rng.binomial(Ns[s]-base[s],q)) for s in strata}
            x5,pn5,pd5=X2_perm(KP5,Ns,Ntot,ens['nullK'][tau],ens['R'])
            print(f"p={p}: P1(diag) X2={x1:.1f} p={pn1}/{pd1} dom={dom1}({z1[dom1]:+.1f}) "
                  f"{'FIRE+diag-dom OK' if pn1==1 and dom1=='diag' else 'CHECK'} | "
                  f"P5(uniform) X2={x5:.1f} p={pn5}/{pd5} {'OK(no trip)' if pn5/pd5>0.05 else 'TRIP-BAD'}",flush=True)
        sys.exit(0)
    per=run_full()
    json.dump(per,open("n7_locus_full_results.json","w"))
    pool_and_verdict(per)
