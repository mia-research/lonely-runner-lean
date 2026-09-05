#!/usr/bin/env python3
"""
Analysis stage for PREREG_subrayleigh_deficit_arithmetic_scatter_v5.md (+ _DEVIATIONS.md).
Consumes arithmetic_scatter_sweep_v1_results.jsonl (delta per curve) and emits the §9 outcome.
NO delta is computed here (that is the frozen sweep). Directions locked from TRAINING only (D-A3).

Modes:
  selftest  -> run analysis-stage controls P1,P2,P3,P6 on SYNTHETIC data (pipeline validation;
               needs NO real delta; the frozen "controls fire before any verdict" gate).
  analyze   -> full §9 analysis on the JSONL (run when the sweep is complete).
Exactness: invariants are exact int; within-p H2 p-values are exact (enumerate m!); across-p tests are
fixed-seed Monte-Carlo permutation = integer-count p-values (D-A4). Fit is float on analytic delta (D-A1).
"""
import json, math, sys, itertools, random
import numpy as np

RESULTS="arithmetic_scatter_sweep_v1_results.jsonl"
SCREEN ="cyclicity_screen_v1_data.txt"
SEED=20260806
ALPHA=0.05
NPERM=200000

# ---------------- invariants (exact int) ----------------
def sextic_class_map():
    m={}
    for line in open(SCREEN):
        if line.startswith("#"): continue
        left=line.split("|")[0].split(); m[int(left[0])]=int(left[2])
    return m

# ---------------- rank / permutation primitives ----------------
def ranks(v):
    order=sorted(range(len(v)), key=lambda i:v[i]); R=[0.0]*len(v)
    i=0
    while i<len(v):
        j=i
        while j+1<len(v) and v[order[j+1]]==v[order[i]]: j+=1
        avg=(i+j)/2.0
        for t in range(i,j+1): R[order[t]]=avg
        i=j+1
    return R

def spearman(x,y):
    Rx,Ry=ranks(x),ranks(y); n=len(x)
    mx=sum(Rx)/n; my=sum(Ry)/n
    num=sum((Rx[i]-mx)*(Ry[i]-my) for i in range(n))
    den=math.sqrt(sum((Rx[i]-mx)**2 for i in range(n))*sum((Ry[i]-my)**2 for i in range(n)))
    return 0.0 if den==0 else num/den

def exact_slope_pvalues(deltas, aps, positive=True):
    """One-sided exact permutation p-value of Spearman(delta, a_p); also the FULL support list
    (one p-value per permutation, uniform under H0) for the Fisher combined null. m<=6 -> m!<=720."""
    m=len(deltas); base=list(ranks(aps))
    rhos=[]
    for perm in itertools.permutations(range(m)):
        dp=[deltas[perm[i]] for i in range(m)]
        rhos.append(spearman(dp, aps))
    rhos_sorted=sorted(rhos)
    def one_sided_p(r):
        if positive: return sum(1 for x in rhos if x>=r-1e-12)/len(rhos)
        return sum(1 for x in rhos if x<=r+1e-12)/len(rhos)
    obs=spearman(deltas, aps)
    support=[one_sided_p(r) for r in rhos]   # the m! achievable p-values, each equally likely under H0
    return one_sided_p(obs), support

def fisher_combined(observed_ps, supports, rng):
    """Exact-count combined p of X=-2 sum ln(pi) vs the H0 null (pi ~ Uniform(support_p))."""
    Xobs=-2*sum(math.log(max(p,1e-12)) for p in observed_ps)
    ge=0
    for _ in range(NPERM):
        X=-2*sum(math.log(max(rng.choice(s),1e-12)) for s in supports)
        if X>=Xobs-1e-12: ge+=1
    return (ge+1)/(NPERM+1), Xobs

def perm_test(values, labels, statfn, rng, two_sided=True, nperm=NPERM):
    """Generic label-permutation test. statfn(values,labels)->scalar. Integer-count p-value."""
    obs=statfn(values,labels); n=len(values); idx=list(range(n)); ge=0
    center=None
    for _ in range(nperm):
        rng.shuffle(idx); lp=[labels[i] for i in idx]
        s=statfn(values,lp)
        if two_sided:
            if abs(s)>=abs(obs)-1e-12: ge+=1
        else:
            if s>=obs-1e-12: ge+=1
    return (ge+1)/(nperm+1), obs

def mannwhitney_stat(values, labels):
    """rank-biserial-ish: mean rank difference between the two groups (labels in {0,1})."""
    R=ranks(values); g1=[R[i] for i in range(len(values)) if labels[i]==1]
    g0=[R[i] for i in range(len(values)) if labels[i]==0]
    if not g1 or not g0: return 0.0
    return sum(g1)/len(g1)-sum(g0)/len(g0)

def kruskal_stat(values, labels):
    """KW H statistic (omnibus, two-sided by nature)."""
    R=ranks(values); n=len(values); groups={}
    for i,l in enumerate(labels): groups.setdefault(l,[]).append(R[i])
    H=12.0/(n*(n+1))*sum((sum(g)**2)/len(g) for g in groups.values())-3*(n+1)
    return H

# ---------------- surface fit (float on analytic delta; D-A1) ----------------
def design(p,n):
    L=math.log(p); u=-(p+1-n)/math.sqrt(p)   # u = -a_p/sqrt(p)
    return [1.0,L,L*L,u,u*L,u*L*L]

def fit_surface(rows):
    """weighted LS: delta ~ g0(p)+g1(p)*u, g deg<=2 in ln p. rows: list of (p,n,delta,SE)."""
    A=np.array([design(p,n) for (p,n,d,se) in rows])
    y=np.array([d for (p,n,d,se) in rows]); w=np.array([1.0/se**2 for (p,n,d,se) in rows])
    sw=np.sqrt(w); Aw=A*sw[:,None]; yw=y*sw
    coef,_,_,_=np.linalg.lstsq(Aw,yw,rcond=None)
    return coef
def predict(coef,p,n): return float(np.dot(design(p,n),coef))

def within_prime_partial_R2_u(rows_by_prime):
    """per surface prime: R^2 of delta~u over its (k!=0) twists; return median over primes with >=3 twists."""
    r2s=[]
    for p,items in rows_by_prime.items():
        if len(items)<3: continue
        u=np.array([-(p+1-n)/math.sqrt(p) for (n,d,se) in items]); d=np.array([d for (n,d,se) in items])
        if u.std()==0 or d.std()==0: continue
        b=np.polyfit(u,d,1); pred=np.polyval(b,u)
        sst=((d-d.mean())**2).sum(); ssr=((d-pred)**2).sum()
        r2s.append(1-ssr/sst if sst>0 else 0.0)
    return (float(np.median(r2s)) if r2s else 0.0), len(r2s)

# ---------------- data loading ----------------
def load():
    rows=[json.loads(l) for l in open(RESULTS)]
    scl=sextic_class_map()
    for r in rows: r["sextic"]=scl.get(r["p"],-1)
    return rows

def split(rows):
    surf_knonzero=[r for r in rows if "surface" in r["roles"] and r["k"]!=0]   # f-hat fit set
    surf_all={} # p -> list for H2 (all cyclic twists incl k=0)
    for r in rows:
        if "surface" in r["roles"]: surf_all.setdefault(r["p"],[]).append(r)
    traj=[r for r in rows if "trajectory" in r["roles"] and r["k"]==0]           # H1 residual set
    return surf_knonzero, surf_all, traj

# ---------------- H2 ----------------
def run_H2(surf_all, rng):
    obs_ps=[]; supports=[]; used=0
    for p,items in surf_all.items():
        items=[it for it in items if it]  # cyclic twists at p
        if len(items)<3: continue
        deltas=[it["D"] for it in items]; aps=[it["a"] for it in items]; ses=[it["SE_D"] for it in items]
        # resolved-pair filter (D5): need >=3 pairs with |dD|>5*SE
        res=sum(1 for i in range(len(items)) for j in range(i+1,len(items))
                if abs(deltas[i]-deltas[j])>5*max(ses[i],ses[j]))
        if res<3: continue
        pv,supp=exact_slope_pvalues(deltas, aps, positive=True)
        obs_ps.append(pv); supports.append(supp); used+=1
    if used<3: return dict(fires=False, reason=f"only {used} usable primes", used=used)
    comb_p,Xobs=fisher_combined(obs_ps, supports, rng)
    return dict(fires=comb_p<0.01, comb_p=comb_p, Xobs=Xobs, used=used, median_pi=float(np.median(obs_ps)))

# ---------------- outcome ----------------
def holm(pvals, alpha=ALPHA):
    order=sorted(range(len(pvals)), key=lambda i:pvals[i]); m=len(pvals); rej=[False]*m
    for rank,i in enumerate(order):
        if pvals[i]<=alpha/(m-rank): rej[i]=True
        else: break
    return rej

def run_analysis():
    rng=random.Random(SEED); rows=load()
    surf_k, surf_all, traj=split(rows)
    print(f"[analyze] surface(k!=0)={len(surf_k)}  surface-primes={len(surf_all)}  trajectory={len(traj)}")
    if len(surf_k)<20 or len(traj)<20:
        print("[analyze] INSUFFICIENT DATA — sweep not complete. Re-run when JSONL is full.")
        return
    # surface fit (hold out k=0)
    coef=fit_surface([(r["p"],r["n"],r["D"],r["SE_D"]) for r in surf_k])
    rbp={}
    for r in surf_k: rbp.setdefault(r["p"],[]).append((r["n"],r["D"],r["SE_D"]))
    pr2,npr=within_prime_partial_R2_u(rbp)
    H2=run_H2(surf_all, rng)
    surface_ok = H2.get("fires",False) and pr2>=0.25
    print(f"[analyze] H2 {H2}   within-prime partial-R2(u) median={pr2:.3f} over {npr} primes  surface_ok={surface_ok}")
    # residuals
    for r in traj: r["r"]=r["D"]-predict(coef,r["p"],r["n"])
    rr=[r["r"] for r in traj]
    # SM control
    u2=[ (r["a"]**2)/r["p"] for r in traj]
    sm_p,_=perm_test(rr, u2, lambda v,l:spearman(v,l), rng, two_sided=True)
    sm_dirty=sm_p<ALPHA
    # H1a (two-sided, D-A2)
    def binlabels(mod): return [1 if (r["a"]%mod==min(set(x["a"]%mod for x in traj))) else 0 for r in traj]
    lab3=[r["a"]%3 for r in traj]; lab4=[r["a"]%4 for r in traj]
    # map to 0/1 by the two present residues
    def to01(labs):
        vals=sorted(set(labs)); return [0 if l==vals[0] else 1 for l in labs]
    p_mod3,_=perm_test(rr, to01(lab3), mannwhitney_stat, rng, two_sided=True)
    p_mod4,_=perm_test(rr, to01(lab4), mannwhitney_stat, rng, two_sided=True)
    h1a_rej=holm([p_mod3,p_mod4]); H1a_fires=any(h1a_rej)
    # H1a' (sextic, refit-protected)
    scl=[r["sextic"] for r in traj]
    p_sex,_=perm_test(rr, scl, kruskal_stat, rng, two_sided=True)
    # richer-u refit: regress r on {u2,u3,L,L^2}, take resid, re-KW
    U=np.array([[ (r["a"]**2)/r["p"], -(r["a"]/math.sqrt(r["p"]))**3, math.log(r["p"]), math.log(r["p"])**2] for r in traj])
    U=np.column_stack([np.ones(len(traj)),U]); rv=np.array(rr)
    b,_,_,_=np.linalg.lstsq(U,rv,rcond=None); r_refit=list(rv-U@b)
    p_sex_refit,_=perm_test(r_refit, scl, kruskal_stat, rng, two_sided=True)
    H1ap_fires=(p_sex<ALPHA) and (p_sex_refit<ALPHA)
    H1_fires=H1a_fires or H1ap_fires
    # H1b (gated)
    Ms=[r["M"] for r in traj]
    p_M,_=perm_test(rr, Ms, lambda v,l:spearman(v,l), rng, two_sided=True)  # two-sided (D-A3)
    # lag-1 autocorr of r ordered by p
    tsorted=sorted(traj,key=lambda r:r["p"]); rs=[r["r"] for r in tsorted]
    def lag1(v,_l):
        a=v[:-1]; b=v[1:]; return spearman(list(a),list(b))
    p_ac,_=perm_test(rs, list(range(len(rs))), lambda v,l: lag1(v,None), rng, two_sided=True)
    print(f"[analyze] SM(r~u^2) p={sm_p:.4f} dirty={sm_dirty}")
    print(f"[analyze] H1a: p(a_p mod3)={p_mod3:.4f} p(a_p mod4)={p_mod4:.4f} Holm-reject={h1a_rej} -> H1a_fires={H1a_fires}")
    print(f"[analyze] H1a': KW p={p_sex:.4f} refit-KW p={p_sex_refit:.4f} -> H1a'_fires={H1ap_fires}")
    print(f"[analyze] H1b(gated): p(M)={p_M:.4f} p(autocorr)={p_ac:.4f}  [valid only if H1 fires & SM clean]")
    # §9 outcome
    print("\n=== §9 OUTCOME ===")
    if surface_ok and H1_fires: print("A1: arithmetic-residue structure BEYOND the smooth surface. (SM dirty->H1b void, A1 stands on H1a/H1a').")
    elif surface_ok and not H1_fires: print("A2 (H0): scatter is delta's smooth dependence on group order n; no residue structure beyond the surface.")
    elif (not surface_ok) and H1_fires: print("A3: residue structure but surface underdetermined (H2 weak) -> provisional.")
    elif (not H2.get('fires',False)) and pr2<0.05: print("A5: no resolved n-dependence (g1~0) -> scatter is NOT group order.")
    else: print("A4/A6: inconclusive / underpowered — see per-test p-values and power floors.")

# ---------------- analysis-stage controls (SELFTEST, synthetic) ----------------
def selftest():
    rng=random.Random(SEED)
    # synthetic trajectory: 40 primes, real-ish a_p; residual r
    ps=[p for p in range(3061,12000) if p%3==1][:40]
    aps=[rng.choice([-1,1])*rng.randint(5,200) for _ in ps]
    base=[0.001+rng.gauss(0,3e-5) for _ in ps]
    print("=== ANALYSIS-STAGE CONTROLS (synthetic; validate pipeline before verdict) ===")
    # P1: inject r = c*(a_p mod3==1)+noise -> H1a must recover
    r1=[base[i]+(2e-4 if aps[i]%3==1 else 0)+rng.gauss(0,3e-5) for i in range(len(ps))]
    lab3=[0 if a%3==sorted(set(x%3 for x in aps))[0] else 1 for a in aps]
    p1,_=perm_test(r1, lab3, mannwhitney_stat, rng, two_sided=True)
    print(f"P1 (inject a_p mod3 effect): H1a p={p1:.5f}  {'FIRES' if p1<ALPHA else 'FAIL-did-not-fire'}")
    # P2: same r1 but SHUFFLED labels -> must be null (repeat, check false-positive rate ~alpha)
    fp=0; T=200
    for _ in range(T):
        sh=lab3[:]; rng.shuffle(sh)
        pp,_=perm_test(r1, sh, mannwhitney_stat, random.Random(rng.random()*1e9), two_sided=True, nperm=1000)
        if pp<ALPHA: fp+=1
    print(f"P2 (shuffled labels, {T} trials): false-positive rate={fp/T:.3f}  {'OK(~alpha)' if fp/T<0.12 else 'FAIL-too-high'}")
    # P3: inject g1 slope into synthetic twists -> H2 recovers
    supports=[]; obs=[]
    for _ in range(20):  # 20 synthetic primes, 4 twists each
        tw_a=sorted(rng.sample(range(-150,150),4))
        tw_d=[0.001 - 5e-6*a + rng.gauss(0,3e-6) for a in tw_a]  # delta decreases with... wait sign: delta increases with a_p
        tw_d=[0.001 + 5e-6*a + rng.gauss(0,3e-6) for a in tw_a]
        pv,supp=exact_slope_pvalues(tw_d, tw_a, positive=True); obs.append(pv); supports.append(supp)
    cp,_=fisher_combined(obs, supports, rng)
    print(f"P3 (inject g1>0 slope): H2 Fisher combined p={cp:.5f}  {'FIRES' if cp<0.01 else 'FAIL'}")
    # P6: out-of-class smooth surface (u^2) + ZERO arithmetic residual -> H1a/H1a' silent after refit; SM fires
    u2=[(a**2)/p for a,p in zip(aps,ps)]
    r6=[0.001+3e-4*(u2[i]/max(u2)) + rng.gauss(0,3e-5) for i in range(len(ps))]  # smooth u^2 leak, no arith
    scl6=[rng.randint(0,5) for _ in ps]  # random sextic classes (no real arith structure)
    psm,_=perm_test(r6, u2, lambda v,l:spearman(v,l), rng, two_sided=True)
    # refit out u^2 etc then KW by (random) sextic
    U=np.column_stack([np.ones(len(ps)), np.array(u2), np.array([(u2[i])**1.5 for i in range(len(ps))]), np.log(ps)])
    rv=np.array(r6); b,_,_,_=np.linalg.lstsq(U,rv,rcond=None); r6ref=list(rv-U@b)
    pk,_=perm_test(r6ref, scl6, kruskal_stat, rng, two_sided=True)
    print(f"P6 (u^2 leak, no arith): SM p={psm:.5f} {'FIRES(catches leak)' if psm<ALPHA else 'MISS'};  "
          f"H1a' post-refit KW p={pk:.4f} {'SILENT(good)' if pk>=ALPHA else 'FALSE-FIRE'}")

if __name__=="__main__":
    mode=sys.argv[1] if len(sys.argv)>1 else "selftest"
    if mode=="selftest": selftest()
    elif mode=="analyze": run_analysis()
