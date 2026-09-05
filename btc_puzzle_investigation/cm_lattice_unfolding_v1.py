#!/usr/bin/env python3
"""
cm_lattice_unfolding_v1 — FROZEN RUN of PREREG_cm_lattice_unfolding_v1.md.
Does the public single-point Eisenstein lift eis([d]G) carry the private CM-lattice
unfolding (a,b)=LATT(d), beyond the d<->[d]G bijection? + amicable second-equation arm.

DEVIATIONS (disclosed):
 D1 transversal: frozen `e=0∧s=0` does NOT quotient mu3 (eps,s const on mu3-suborbit);
    corrected to the TRUE mu6-orbit transversal (canonical min-d rep per {±λ^j d}),
    N=(n-1)/6. mu6-witness confirms it removes the inflation the full set shows.
 D2 plant/hard-null use B=1999 (min p=1/2000<α=0.001; decision unaffected); primary B=9999.
 D3 real-key witness uses #135 only (#140 pubkey not on disk); records the public secp feature.
Exact int/Fraction signal path; math.log in MI ranked vs permutation null (carve-out).
Usage: cm_lattice_unfolding_v1.py [B] [pmin]
"""
import sys, math, random
from collections import Counter
from fractions import Fraction
from cm_lattice_setup_v1 import (is_prime, count_E, ec_add, find_gen, frobenius, partner_frob,
                                 ideal_basis, babai, ladder, B_CURVE)
from int1_frame_operator_v1 import build

LS = [2,3,5,7]
ALPHA = Fraction(1,1000)


def MI(F, T):
    N=len(F); jf=Counter(F); jt=Counter(T); jj=Counter(zip(F,T)); mi=0.0
    for (f,t),c in jj.items():
        mi += (c/N)*math.log2((c*N)/(jf[f]*jt[t]))
    return mi

def scalar_mul_table(G,p,n):
    xs=[None]*n; ys=[None]*n; P=None
    for d in range(0,n):
        if d>0: P=ec_add(P,G,p) if P is not None else G
        if d>=1: xs[d]=P[0]; ys[d]=P[1]
    return xs,ys

def mu6_reps(n,lam):
    seen=bytearray(n); reps=[]
    for d in range(1,n):
        if seen[d]: continue
        orb=set(); t=d
        for _ in range(3):
            orb.add(t); orb.add((n-t)%n); t=t*lam%n
        for o in orb: seen[o]=1
        reps.append(min(orb))
    return reps


def run_rung(p, n, B, out):
    pip=frobenius(p,n); pin=partner_frob(p,n)
    A,Bc=pip; Rt1,Rt2=ideal_basis((A-1,Bc)); Rn1,Rn2=ideal_basis((pin[0]-1,pin[1]))
    eis,eps=build(p); G=find_gen(p,n)
    lam=next(c for c in range(2,n) if c!=1 and pow(c,3,n)==1)
    xs,ys=scalar_mul_table(G,p,n)
    reps=mu6_reps(n,lam); N=len(reps)
    # features/targets on transversal (exact int)
    U=[];V=[];E=[];UP=[];VP=[];Aa=[];Bb=[]
    for d in reps:
        x=xs[d]; u,v=eis(x); up,vp=babai((x%p,0),Rn1,Rn2); a,b=babai((d%n,0),Rt1,Rt2)
        U.append(u);V.append(v);E.append(eps(x));UP.append(up);VP.append(vp);Aa.append(a);Bb.append(b)
    import numpy as np
    def enc(cols):
        out=np.zeros(N,dtype=np.int64)
        for c in cols:
            c=np.asarray(c,dtype=np.int64); out=out*(int(c.max())+1)+c
        return out
    def MIc(fa, ta):   # MI in bits from two int-label arrays (fast, numpy)
        F=int(fa.max())+1; T=int(ta.max())+1
        j=np.bincount(fa*T+ta, minlength=F*T).reshape(F,T).astype(float)
        Nn=j.sum(); pf=j.sum(1)/Nn; pt=j.sum(0)/Nn; mi=0.0
        nz=j>0; pj=j/Nn
        return float(np.sum(pj[nz]*np.log2(pj[nz]/(pf[:,None]*pt[None,:])[nz])))
    Phic={l:enc([[u%l for u in U],[v%l for v in V],E]) for l in LS}
    Psic={l:enc([[u%l for u in UP],[v%l for v in VP]]) for l in LS}
    PhiPsic={l:enc([[u%l for u in U],[v%l for v in V],E,[u%l for u in UP],[v%l for v in VP]]) for l in LS}
    Tc={l:enc([[a%l for a in Aa],[b%l for b in Bb]]) for l in LS}
    obs={}
    for l in LS:
        obs[('P',l)]=MIc(Phic[l],Tc[l]); obs[('N',l)]=MIc(PhiPsic[l],Tc[l])-obs[('P',l)]
    keys=[('P',l) for l in LS]+[('N',l) for l in LS]
    ge={k:0 for k in keys}; ge_fw=0; obs_max=max(obs[k] for k in keys)
    rng=np.random.default_rng(20260819)
    for _ in range(B):
        perm=rng.permutation(N)
        st={};
        for l in LS:
            Tp=Tc[l][perm]
            p_=MIc(Phic[l],Tp); st[('P',l)]=p_; st[('N',l)]=MIc(PhiPsic[l],Tp)-p_
        for k in keys:
            if st[k]>=obs[k]: ge[k]+=1
        if max(st[k] for k in keys)>=obs_max: ge_fw+=1
    pfw=(1+ge_fw)/(B+1)
    Phis={l:list(zip([u%l for u in U],[v%l for v in V],E)) for l in LS}  # for plant/hard-null below
    def Phi(l): return Phis[l]
    def Tg(l): return list(zip([a%l for a in Aa],[b%l for b in Bb]))
    out.append("  p=%d n=%d N=%d cls=%d"%(p,n,N,p%12))
    for l in LS:
        out.append("    ARM P l=%d MI=%.5f p_single=%.4f | ARM N l=%d dMI=%.5f p_single=%.4f"
                   %(l,obs[('P',l)],(1+ge[('P',l)])/(B+1),l,obs[('N',l)],(1+ge[('N',l)])/(B+1)))
    out.append("    FAMILY-WISE max-T p=%.4f  -> %s"%(pfw, "LEAK" if pfw<float(ALPHA) else "null"))
    # POWER I_min for primary l=2 (df=(A-1)(l^2-1), A=|Phi2 alphabet|)
    A2=len(set(Phis[2])); df=(A2-1)*(4-1); lam_nc=27.0  # ~chi2 ncp df~9 alpha .001 pow .8
    Imin=lam_nc/(2*N*math.log(2))
    out.append("    POWER l=2: |Phi2|=%d df~%d  I_min~=%.2e bits (powered iff <=0.01: %s)"
               %(A2,df,Imin,Imin<=0.01))
    # POSITIVE PLANT eps-sweep (numpy MIc; must fire at eps=1); report eps_min
    Ta=Tc[2]; Fa=Phic[2]; eps_min=None; Bp=1999
    for k in range(0,7):
        e=Fraction(1,1<<k) if k>0 else Fraction(1,1)
        r3=np.random.default_rng(777+k)
        cvec=np.where(r3.random(N)<float(e), np.array([a%2 for a in Aa]), r3.integers(0,2,N))
        Fpl=Fa*2+cvec
        oo=MIc(Fpl,Ta); gg=0
        for _ in range(Bp):
            Ts=Ta[np.random.default_rng(9000+k*Bp+_).permutation(N)]
            if MIc(Fpl,Ts)>=oo: gg+=1
        if (1+gg)/(Bp+1)<float(ALPHA): eps_min=e
    out.append("    PLANT eps-sweep: fires (p<0.001) down to eps_min=%s"%(eps_min))
    # HARD NULL (numpy; must NOT fire): 30 random re-pairings
    fp=0
    for j in range(30):
        Tp=Ta[np.random.default_rng(555+j).permutation(N)]
        oo=MIc(Fa,Tp); gg=0
        for _ in range(Bp):
            Ts=Tp[np.random.default_rng(600000+j*Bp+_).permutation(N)]
            if MIc(Fa,Ts)>=oo: gg+=1
        if (1+gg)/(Bp+1)<float(ALPHA): fp+=1
    out.append("    HARD-NULL false-positive rate = %d/30 (need <=1/30 ~ 2a)"%fp)
    return dict(p=p,n=n,pfw=pfw,eps_min=eps_min,fp=fp,Imin=Imin,leak=pfw<float(ALPHA))


def mu6_witness(p,n):
    pip=frobenius(p,n); A,Bc=pip; Rt1,Rt2=ideal_basis((A-1,Bc)); eis,eps=build(p); G=find_gen(p,n)
    xs,ys=scalar_mul_table(G,p,n)
    Phi=[];T=[]
    for d in range(1,n):
        x=xs[d]; u,v=eis(x); a,b=babai((d%n,0),Rt1,Rt2)
        Phi.append((u%2,v%2,eps(x))); T.append((a%2,b%2))
    oo=MI(Phi,T); gg=0; rng=random.Random(3)
    for _ in range(499):
        Ts=[T[i] for i in rng.sample(range(len(T)),len(T))]
        if MI(Phi,Ts)>=oo: gg+=1
    return (1+gg)/500


def main():
    B=int(sys.argv[1]) if len(sys.argv)>1 else 9999
    pmin=int(sys.argv[2]) if len(sys.argv)>2 else 10000
    nrung=int(sys.argv[3]) if len(sys.argv)>3 else 3
    out=["="*84,"CM LATTICE-UNFOLDING LEAK TEST — frozen run  B=%d  pmin=%d  rungs/class=%d"%(B,pmin,nrung),"="*84]
    rungs=[]
    for cls in (1,7):
        for pr in ladder(cls,pmin,nrung):
            rungs.append(pr)
    out.append("ladder: %s"%rungs)
    # mu6-witness on one small prime (admissibility)
    wp,wn=ladder(1,2000,1)[0]
    wpv=mu6_witness(wp,wn)
    out.append("MU6-WITNESS (full-set plain-shuffle, p=%d): p_perm=%.4f  (expect INFLATED << transversal null)"%(wp,wpv))
    res=[]
    for p,n in rungs:
        res.append(run_rung(p,n,B,out))
        print("done p=%d"%p, flush=True)
    out.append("\n"+"="*84)
    leaks=sum(1 for r in res if r['leak']); pmins=[r for r in res if r['Imin']>0.01]
    out.append("SUMMARY: %d/%d rungs LEAK (family-wise p<0.001);  %d rungs under-powered (I_min>0.01)"
               %(leaks,len(res),len(pmins)))
    plant_ok=all(r['eps_min'] is not None for r in res); hn_ok=all(r['fp']<=2 for r in res)
    out.append("  plant fires all rungs: %s   hard-null FP<=2 all rungs: %s"%(plant_ok,hn_ok))
    out.append("  -> %s"%("LEAK detected (see rungs)" if leaks>0 else
                          "BOUNDED NULL: public single-point lift carries <I_min bits about (a,b) mod l on the transversal, at this ladder scope. Collapses the circular single-point arsenal at scope; NOT a closure, NOT a 2^256 claim."))
    # #135 secp public-feature record
    try:
        from int1_frame_operator_v1 import build_secp
        from glv_fundamental_domain_law_v1 import P_SECP
        eiss,epss=build_secp()
        x135=0x145d2611c823a396ef6712ce0f712f09b9b4f3135e3e0aa3230fb9b6d08d1e16
        u,v=eiss(x135)
        out.append("\n#135 secp public feature (record): eps=%d (u,v)mod2=(%d,%d)  [d unknown; per null, no actionable (a,b) prediction]"%(epss(x135),u%2,v%2))
    except Exception as ex:
        out.append("\n#135 record skipped: %s"%ex)
    out.append("CM_LATTICE_DONE")
    open("cm_lattice_unfolding_run_v1.out","w").write("\n".join(out))
    print("\n".join(out[-14:]))


if __name__=='__main__':
    main()
