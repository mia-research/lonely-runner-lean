#!/usr/bin/env python3
"""
gamma_run_v1.py — executes PREREG_isotypic_trace_carry_stratify_v1 (frozen, p=43).
FULLY EXACT INTEGER (no float anywhere; no check_no_float carve-out needed).
Data: ell(d) from Sage trace_openq_test.sage; x([d]G) from Sage (G=(7,7), ord 31);
carry from the Eisenstein lift with pi=7+w (A_SP=7,B_SP=1,BETA=36) — the p=43 analog of the
secp carry construction (A_SP,B_SP = components of pi, norm A^2-AB+B^2=p, VERIFIED).
"""
from itertools import combinations, permutations
from math import comb, factorial

# ---- established data (p=43) ----
ELL = {3:1,4:206,6:1715,7:401,12:820,13:1849,15:43,17:903,20:1286,21:1780,22:21,23:969,26:260,29:1186,30:1811}
XD  = {3:29,4:32,6:37,7:34,12:25,13:12,15:2,17:35,20:20,21:40,22:13,23:38,26:42,29:21,30:7}
nE = 31; LAM = 25; MOD = 1893              # A_new order
p_field = 43; A_SP = 7; B_SP = 1; BETA = 36
RAT = sorted(ELL)

# ---- carry (exact int; carry class in {-1,0,+1} <-> {0,+w,-w}) ----
def lift_uv(X):
    ku = (2*X*(A_SP-B_SP)+p_field)//(2*p_field)
    kv = (-2*X*B_SP+p_field)//(2*p_field)
    return X*(A_SP-B_SP)-ku*p_field, -X*B_SP-kv*p_field
def carry(X):
    u,v = lift_uv(X); return (2*(u-v)+p_field)//(2*p_field)

# ---- FS2: GLV orbits of the scalars mod nE=31 under x25 ----
def orbit(d): return {d, (LAM*d)%nE, (LAM*LAM*d)%nE}
orbits=[]; seen=set()
for d in RAT:
    if d in seen: continue
    o = sorted(orbit(d) & set(RAT)); seen |= set(o); orbits.append(o)
M = len(orbits)

# ---- FS5 integrity ----
# (a) carry orbit-invariant
carry_of = {d: carry(XD[d]) for d in RAT}
fs5a = all(len({carry_of[d] for d in o})==1 for o in orbits)
# (b) ell covariance: for d'=25^t rep, ell(d')=k^t ell(rep) mod 1893, single k in {587,1849}
def covar_ok(o):
    rep = min(o); e0 = ELL[rep]
    for k in (587,1849):
        ok=True
        for d in o:
            # find t with 25^t rep = d mod nE
            t=0; cur=rep
            while cur!=d and t<3: cur=(cur*LAM)%nE; t+=1
            if (pow(k,t,MOD)*e0)%MOD != ELL[d]: ok=False; break
        if ok: return True
    return False
fs5b = all(covar_ok(o) for o in orbits)

# ---- reduced dataset: rep=min d per orbit ----
reps = [min(o) for o in orbits]
rows = [(r, ELL[r], carry_of[r]) for r in reps]     # (rep, e, class)

# ---- FS1/FS3/FS4 ----
from collections import Counter
pt_counts = Counter(carry_of[d] for d in RAT)        # FS1 (points)
orb_counts = Counter(c for (_,_,c) in rows)          # FS3 (orbits)
def nperm(counts):
    return factorial(sum(counts.values()))//(factorial(counts.get(-1,0))*factorial(counts.get(0,0))*factorial(counts.get(1,0)))
Nperm = nperm(orb_counts)

print("=== FS0 STRUCTURE REPORT (printed before any fit) ===")
print(f"FS1 point counts by carry {{0:{pt_counts.get(0,0)}, +:{pt_counts.get(1,0)}, -:{pt_counts.get(-1,0)}}} (sum {sum(pt_counts.values())})")
print(f"FS2 orbits (M={M}): "+"; ".join(f"{o}->e{ELL[min(o)]},c{carry_of[min(o)]:+d}" for o in orbits)+
      f" | sizes {sorted(len(o) for o in orbits)}")
print(f"FS3 orbit counts by carry {{0:{orb_counts.get(0,0)}, +:{orb_counts.get(1,0)}, -:{orb_counts.get(-1,0)}}}")
print(f"FS4 N_perm = {Nperm}")
print(f"FS5 (a) carry orbit-invariant: {fs5a} ; (b) ell covariance k^t: {fs5b}")

# ---- power gate P1,P2 ----
mmax = max(orb_counts.values())
P1 = mmax>=3; P2 = Nperm>=20
print(f"\nPOWER: P1 (some class m>=3): {P1} (max m={mmax}) ; P2 (N_perm>=20): {P2}")

def det(i,j,l,e,mod):     # collinearity determinant of rows i,j,l on (rep,e)
    ri,rj,rl=reps[i],reps[j],reps[l]
    return ((rj-ri)*(e[l]-e[i]) - (rl-ri)*(e[j]-e[i])) % mod
def Tstat(labels, e, mod):
    tot=0
    for c in (-1,0,1):
        idx=[i for i in range(M) if labels[i]==c]
        for (i,j,l) in combinations(idx,3):
            if det(i,j,l,e,mod)!=0: tot+=1
    return tot

if not (fs5a and fs5b):
    print("\n=> B0: integrity FAIL — established facts contradicted by table. ABSTAIN-with-flag.")
elif not (P1 and P2):
    print(f"\n=> B1: NOT POWERED (P1={P1}, P2={P2}). ABSTAIN — underpowered at p=43 with these class"
          f" sizes (N_perm={Nperm}). Not a null, not a positive. Larger A_new owed (blocked: Sage/Singular"
          " hang above p=43).")
else:
    labels=[c for (_,_,c) in rows]
    e_true=[e for (_,e,_) in rows]
    # all distinct label-partitions preserving orbit counts
    from itertools import permutations as perm
    base=labels[:]
    parts=set(perm(base)); parts=sorted(parts)
    def pval(e, mod):
        Tt=Tstat(labels,e,mod)
        le=sum(1 for pr in parts if Tstat(list(pr),e,mod)<=Tt)
        return Tt, le, len(parts)
    Tt,le,Np = pval(e_true, MOD)
    T3=Tstat(labels,e_true,3); T631=Tstat(labels,e_true,631)
    # component p-values
    _,le3,_=pval(e_true,3); _,le631,_=pval(e_true,631)
    print(f"\n=== PRIMARY ===  T_true={Tt}  p = {le}/{Np} = {le/Np:.4f}")
    print(f"component: T_3={T3} p={le3}/{Np}={le3/Np:.3f} ; T_631={T631} p={le631}/{Np}={le631/Np:.3f} (Bonf a=0.025)")
    # planted control f=0..3 (seed-disclosed)
    import random
    print("\n=== PLANTED-POSITIVE (power check) ===")
    for f in range(4):
        rng=random.Random(20260817+f)
        Ac={c: rng.randrange(1,MOD) for c in (-1,0,1)}; Bc={c: rng.randrange(MOD) for c in (-1,0,1)}
        ep=[(Ac[c]*r+Bc[c])%MOD for (r,_,c) in rows]
        # corrupt f reps in majority class
        maj=max((-1,0,1), key=lambda c: orb_counts.get(c,0))
        majidx=[i for i in range(M) if labels[i]==maj]
        for i in rng.sample(majidx, min(f,len(majidx))): ep[i]=(ep[i]+123)%MOD
        Tf,lef,_=pval(ep,MOD)
        print(f"  f={f}: T={Tf} p={lef}/{Np}={lef/Np:.4f}"+("  <= fires" if lef/Np<=0.05 else ""))
    # calibration-negative
    rng=random.Random(424242); lab2=labels[:]; rng.shuffle(lab2)
    Tc=Tstat(lab2,e_true,MOD); lec=sum(1 for pr in parts if Tstat(list(pr),e_true,MOD)<=Tc)
    print(f"=== CALIBRATION-NEGATIVE (fixed random partition): p={lec}/{Np}={lec/Np:.3f} (expect ~0.5) ===")
    verdict = "B2 SCOPED POSITIVE" if le/Np<=0.05 else "B3 SCOPED NULL"
    print(f"\n=> {verdict} (p=43, 15 d, scope-locked; a positive is a LEAD to re-run at larger A_new)")
