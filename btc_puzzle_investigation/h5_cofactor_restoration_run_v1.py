# h5_cofactor_restoration_run_v1.py -- run: sage h5_cofactor_restoration_run_v1.py [--smoke]
# Executes PREREG_h5_cofactor_restoration_plant_v1.md. FORWARD test: induce subgroup confinement on
# CYCLIC composite-order curves and ask whether the relation-yield lever reappears with slope beta_j0.
#
# Statistic: beta_induced = OLS slope of T1_induced(cell) on ln(c), where
#   T1_induced = logmean quo(confined to <c*G>) - logmean quo(full group, random_point).
# Target beta_j0 = OLS slope of j0 same-curve F8 differential (gens - randpoint) on ln(n2), |V|=6,
#   computed from the frozen h5_followup_results_v1.jsonl (prior data, step 0).
# Matched null: within-curve c-label permutation (1e4). Plants: confinement-verify, synthetic-slope,
#   additive+0.5, c=1 null.  Exact ints for #E,q,c,quo,orders; float only in logmean/OLS/perm-rank.

from sage.all import *
import json, sys, time, random, math
from collections import defaultdict

BASE="/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation"
H=BASE+"/semaev_elimination_v1.py"; _g={'__name__':'hm'}; exec(open(H).read(),_g)
decomposition_system=_g['decomposition_system']

SMOKE=('--smoke' in sys.argv)
m=3
Vs=[6] if SMOKE else [4,5,6]
K=5 if SMOKE else 25
QFLOOR=200
NEED_CURVES=4 if SMOKE else 25
PBAND=(2003,4001) if SMOKE else (10007,50021)
NPERM=1000 if SMOKE else 10000
OUT=BASE+("/h5_restoration_smoke_v1.jsonl" if SMOKE else "/h5_restoration_results_v1.jsonl")

def logmean(qs): return math.log(sum(qs)/len(qs))   # noqa: float — (stat) monotone stat on exact-int quo, ranked vs label-perm null

def quo_vsd(F, A, B, tval, V):
    Dmax=2**(m-1)+m*len(V)+5
    Rx,gens_list,xs=decomposition_system(F,A,B,m,tval,V)
    I=Rx.ideal(gens_list)
    if int(I.dimension())!=0: return None
    return int(I.vector_space_dimension())

# ---- step 0: beta_j0 from frozen prior data ----
def ols(xs, ys):  # noqa: float — (stat) OLS slope on logmean-of-exact-int-quo, ranked vs label-perm null
    n=len(xs); mx=sum(xs)/n; my=sum(ys)/n  # noqa: float — (stat) slope statistic
    sxx=sum((x-mx)**2 for x in xs); sxy=sum((x-mx)*(y-my) for x,y in zip(xs,ys))
    b=sxy/sxx if sxx else float('nan'); a=my-b*mx  # noqa: float — (stat) slope statistic
    ss=sum((y-my)**2 for y in ys); rr=sum((y-(a+b*x))**2 for x,y in zip(xs,ys))
    r2=1-rr/ss if ss else float('nan')  # noqa: float — (stat) fit-quality descriptor
    return b,a,r2

def compute_beta_j0():
    recs=[json.loads(l) for l in open(BASE+"/h5_followup_results_v1.jsonl")]
    byV=defaultdict(lambda: defaultdict(dict))   # V->p->{arm/lab: quos}
    for r in recs:
        if "q_inv" in r: continue
    idx=defaultdict(list)
    for r in recs: idx[(r["arm"],r["p"],r["V"])].append(r)
    Ps=sorted({r["p"] for r in recs})
    xs=[]; yd=[]; yc=[]
    for p in Ps:
        base_j0=[r for r in idx[("baseline",p,6)] if r["lab"]=="j0"]
        f8_j0  =[r for r in idx[("F8",p,6)] if r["lab"]=="j0"]
        ctrl   =[r for r in idx[("baseline",p,6)] if r.get("is_ctrl")]
        if not (base_j0 and f8_j0 and ctrl): continue
        F=GF(p); inv=EllipticCurve(F,[0,1]).abelian_group().invariants()
        n2=inv[0] if len(inv)>1 else 1
        if n2<=1: continue
        d_f8 = logmean(base_j0[0]["quos"]) - logmean(f8_j0[0]["quos"])       # same-curve gens - randpoint
        d_cc = logmean(base_j0[0]["quos"]) - logmean(ctrl[0]["quos"])         # cross-curve
        xs.append(math.log(n2)); yd.append(d_f8); yc.append(d_cc)  # noqa: float — (stat) ln(n2) regressor on exact-int n2
    b_same,_,r2s=ols(xs,yd); b_cc,_,r2c=ols(xs,yc)
    return dict(beta_j0_samecurve=b_same, r2_same=r2s, beta_j0_crosscurve=b_cc, r2_cc=r2c, n=len(xs))

# ---- curve search: cyclic, composite #E with enough usable c ----
def find_curves(pband, need):
    out=[]; p=pband[0]-1
    tries=0
    while len(out)<need and tries<200000:
        p=int(next_prime(p))
        if p>pband[1]: p=pband[0]  # wrap (shouldn't happen at this band)
        F=GF(p)
        for _ in range(6):
            tries+=1
            A=F(random.randrange(1,p)); B=F(random.randrange(1,p))
            if (4*A**3+27*B**2)==0: continue
            E=EllipticCurve(F,[A,B]); j=E.j_invariant()
            if j==F(0) or j==F(1728): continue
            inv=E.abelian_group().invariants()
            if len(inv)>1: continue          # require CYCLIC
            N=int(E.order())
            cs=[c for c in divisors(N) if c>=2 and N//c>=QFLOOR]
            if len(cs)<4: continue
            out.append(dict(p=p,A=int(A),B=int(B),N=N,cs=cs))
            break
    return out

def confined_target(E, G, c, q, extra, rng):
    """decomposable target with all points in H=<c*G> (order q)."""
    H=c*G; q=int(q)
    for _ in range(300):
        pts=[int(rng.randrange(1,q))*H for _ in range(m)]
        xs=[P[0] for P in pts]
        if any(P==E(0) for P in pts) or len(set(xs))<m: continue
        S=E(0)
        for P in pts: S=S+P
        T=-S
        if T==E(0): continue
        V=list(xs)
        for _ in range(extra):
            V.append((int(rng.randrange(1,q))*H)[0])
        return T[0],[E.base_field()(x) for x in V], pts
    return None

def full_target(E, extra, rng_seed):
    set_random_seed(int(rng_seed))
    for _ in range(300):
        pts=[E.random_point() for _ in range(m)]
        if any(P==E(0) for P in pts): continue
        xs=[P[0] for P in pts]
        if len(set(xs))<m: continue
        S=E(0)
        for P in pts: S=S+P
        T=-S
        if T==E(0): continue
        V=list(xs)
        for _ in range(extra):
            Q=E.random_point()
            if Q!=E(0): V.append(Q[0])
        return T[0],[E.base_field()(x) for x in V]
    return None

def verify_confinement(E, G, c, q):
    """plant 1: sampled confined points have order dividing q; H genuinely order q."""
    H=c*G
    if q*H != E(0): return False
    for ell in prime_divisors(q):
        if (q//ell)*H == E(0): return False
    return True

def cell_quo_confined(E, G, c, q, A, B, extra, K):
    F=E.base_field(); rng=random.Random(int(9000+c)); qs=[]
    for k in range(K):
        ct=confined_target(E,G,c,q,extra,rng)
        if ct is None: continue
        tval,V,pts=ct
        r=quo_vsd(F,A,B,tval,V)
        if r is not None: qs.append(r)
    return qs

def cell_quo_full(E, A, B, extra, K, seed0):
    F=E.base_field(); qs=[]
    for k in range(K):
        ft=full_target(E,extra,seed0+k)
        if ft is None: continue
        tval,V=ft
        r=quo_vsd(F,A,B,tval,V)
        if r is not None: qs.append(r)
    return qs

def main():
    t0=time.time()
    bj=compute_beta_j0()
    print("STEP0 beta_j0(same-curve)=%.4f r2=%.3f | beta_j0(cross)=%.4f r2=%.3f | n=%d"
          %(bj["beta_j0_samecurve"],bj["r2_same"],bj["beta_j0_crosscurve"],bj["r2_cc"],bj["n"]))
    open(OUT,"w").write(json.dumps(dict(kind="header",beta_j0=bj,Vs=Vs,K=K,QFLOOR=QFLOOR,PBAND=PBAND))+"\n")
    random.seed(4242)
    curves=find_curves(PBAND,NEED_CURVES)
    print("found %d cyclic composite-order curves in %s"%(len(curves),PBAND))
    for ci,cv in enumerate(curves):
        p=cv["p"]; F=GF(p); E=EllipticCurve(F,[cv["A"],cv["B"]]); G=E.gens()[0]; N=cv["N"]
        for V in Vs:
            extra=V-m
            full=cell_quo_full(E,cv["A"],cv["B"],extra,K,seed0=7000)
            if not full: continue
            lm_full=logmean(full)
            # c=1 null plant: an independent 2nd full-group draw, must give T1 ~ 0
            full2=cell_quo_full(E,cv["A"],cv["B"],extra,K,seed0=13000)
            if full2:
                open(OUT,"a").write(json.dumps(dict(kind="cell",p=int(p),A=cv["A"],B=cv["B"],N=int(N),
                    c=1,q=int(N),V=V,quo_conf=full2,quo_full=full,lm_conf=logmean(full2),lm_full=lm_full,
                    T1_induced=logmean(full2)-lm_full,sat_conf=(2*max(full2)>=V**m)))+"\n")
            for c in cv["cs"]:
                q=N//c
                if not verify_confinement(E,G,c,q):
                    print("  PLANT1 FAIL p=%d c=%d"%(p,c)); return
                conf=cell_quo_confined(E,G,c,q,cv["A"],cv["B"],extra,K)
                if not conf: continue
                lm_conf=logmean(conf)
                rec=dict(kind="cell",p=int(p),A=cv["A"],B=cv["B"],N=int(N),c=int(c),q=int(q),V=V,
                         quo_conf=conf,quo_full=full,lm_conf=lm_conf,lm_full=lm_full,
                         T1_induced=lm_conf-lm_full, sat_conf=(2*max(conf)>=V**m))  # exact int sat guard
                open(OUT,"a").write(json.dumps(rec)+"\n")
            print("  p=%-6d curve %d/%d |V|=%d cs=%s [%.0fs]"%(p,ci+1,len(curves),V,cv["cs"],time.time()-t0))
    print("DONE [%.0fs]"%(time.time()-t0))

if __name__=='__main__':
    sys.stdout.reconfigure(line_buffering=True); main()
