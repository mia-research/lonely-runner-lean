#!/usr/bin/env python3
"""
#1  E(F_l) point-reduction channel — the φ(n)/L-function bridge.

For each small prime l, reduce every key's point mod l and measure it against the
REDUCED curve:
    v_l  = ((Y mod l)^2 - (X mod l)^3 - 7) mod l   ∈ F_l   (point-vs-curve mod l)
    onC  = [v_l == 0]                                     (reduced pt ON E/F_l)
Compute a_l (Frobenius trace) by exact point count; split (a_l≠0) vs supersingular
(a_l=0, l≡2 mod3). Test v_l / onC / (X mod l) against d,n,k mod l and sign(D) with
the validated pipeline (analytic G-test z + min-residual triage → permutation-
confirm extremes). STRATIFY: do L-function-active (split) primes leak more than
supersingular ones? That is the a_l signal. Positive control: n vs k.
"""
import knd_common as K
c=K.load_decomp(64)
X=c["X"];Y=c["Y"];NS=c["n"];KS=c["k"];DS=c["d"];SG=c["signD"];M=len(X)
print(f"N>=64 keys: {M}")

PRIMES=[5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89]
al={l:K.a_ell(l) for l in PRIMES}
print("Frobenius a_l (0 = supersingular/inert, l≡2 mod3):")
print("  " + "  ".join(f"{l}:{al[l]:+d}{'ss' if al[l]==0 else ''}" for l in PRIMES))

def targets(l): return {"d":[v%l for v in DS],"n":[v%l for v in NS],
                        "k":[v%l for v in KS],"sgn":SG}

print("\nv_l vs d mod l  (analytic triage; * = perm-confirmed):")
print(f"{'l':>3} {'a_l':>4} {'type':>4} {'z(MI)':>7} {'minres':>7} {'MIbits':>9}")
rows=[]
for l in PRIMES:
    vl=[((Y[i]%l)**2-(X[i]%l)**3-7)%l for i in range(M)]
    td=targets(l)["d"]
    z=K.gtest_z(vl,td); mr,_=K.min_resid(vl,td); bits=K.mi_bits_bc(vl,td)
    typ="spl" if al[l]!=0 else "ss"
    rows.append((l,z,mr,bits,typ,vl))
    print(f"{l:>3} {al[l]:>+4d} {typ:>4} {z:>+7.2f} {mr:>+7.2f} {bits:>+9.2e}")

# permutation-confirm the strongest MI and strongest exclusion
rows_z=sorted(rows,key=lambda r:-abs(r[1]))[:2]
rows_m=sorted(rows,key=lambda r:r[2])[:2]
print("\nperm-confirm extremes (v_l vs d):")
seen=set(); extremes=[r for r in rows_z+rows_m if not (r[0] in seen or seen.add(r[0]))]
for l,z,mr,bits,typ,vl in extremes:
    td=[v%l for v in DS]
    _,pz=K.perm_p(vl,td,K.gtest_z,B=400,worse="ge")
    _,pm=K.perm_p(vl,td,lambda a,b:K.min_resid(a,b)[0],B=400,worse="le")
    print(f"  l={l:>3} ({typ}): MI perm p={pz:.3f}  exclusion perm p={pm:.3f}")

# split vs supersingular stratification (are L-active primes leakier?)
def frac_flagged(sub,thr=2.0):
    return sum(1 for r in rows if r[4]==sub and abs(r[1])>thr), sum(1 for r in rows if r[4]==sub)
fs,ns_=frac_flagged("spl"); fss,nss=frac_flagged("ss")
print(f"\nstratification (|z(MI)|>2 for v_l vs d):  split {fs}/{ns_}   supersingular {fss}/{nss}")
print("  (both ≈ 5% under the null => no a_l-dependent leakage)")

# onC (on-curve mod l) vs d — sparse binary, aggregate over primes
print("\nonC (reduced point ON E/F_l) vs sign(D) and d&1:")
for l in (5,7,11,13):
    onC=[1 if ((Y[i]%l)**2-(X[i]%l)**3-7)%l==0 else 0 for i in range(M)]
    rate=sum(onC)
    _,p1=K.perm_p(onC,SG,K.gtest_z,B=300)
    print(f"  l={l:>2}: onC rate={rate}/{M}  onC vs sign(D) MI perm p={p1:.3f}")

# positive control
print("\nPOSITIVE CONTROL n vs k (must fire):")
for l in (5,7):
    _,p=K.perm_p([v%l for v in NS],[v%l for v in KS],lambda a,b:K.min_resid(a,b)[0],B=300,worse="le")
    print(f"  n vs k mod {l}: exclusion perm p={p:.3f}")
