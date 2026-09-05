#!/usr/bin/env python3
"""
#4 (new perspective from project discoveries): DERIVED-POINT coordinates.

The curve's own maps give, from X alone, the x-coords of RELATED keys — for free:
  - GLV endomorphism  φ:(x,y)↦(βx,y)=[λ]P      => bX = βX mod p = x(λ·d·G)
  - doubling map       φ₂(x)=(x⁴−56x)/(4(x³+7)) => x2 = x(2·d·G)
These are the x-coords of scalars λd and 2d mod n — extra "views" of the key. If
ECDLP truly hides d, NONE of these (nor their joint with X) reduces d/n/k. Test
with the validated pipeline (analytic G-test z + min-residual triage → perm-confirm
extremes; n-vs-k positive control). Uses the μ₆/GLV + doubling atlas discoveries
as an information-extraction lens on (X,Y).
"""
import knd_common as K
p=K.P_FIELD
beta=0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE
assert pow(beta,3,p)==1, "beta not a cube root of unity"

c=K.load_decomp(64); X=c["X"];NS=c["n"];KS=c["k"];DS=c["d"];M=len(X)
print(f"N>=64 keys: {M};  β³≡1 mod p: OK")

bX=[(beta*X[i])%p for i in range(M)]                       # x(λP)
x2=[]
for i in range(M):
    den=(4*((X[i]*X[i]*X[i]+7)%p))%p
    if den==0: x2.append(0); continue
    num=((pow(X[i],4,p)-56*X[i])%p)
    x2.append((num*pow(den,p-2,p))%p)                     # x(2P)

def targets(l): return {"d":[v%l for v in DS],"n":[v%l for v in NS],"k":[v%l for v in KS]}
feats_of=lambda l: {
    "X":       [v%l for v in X],
    "bX=x(λP)":[v%l for v in bX],
    "x2=x(2P)":[v%l for v in x2],
    "X⊕bX":    [ (X[i]%l)*l+(bX[i]%l) for i in range(M)],   # joint pair (l² cells)
}

print("\nderived-coord features vs {d,n,k} mod l  (analytic z(MI) / min-resid):")
flagged=[]
for l in (5,7,11,13):
    tg=targets(l); fs=feats_of(l)
    for fn,fa in fs.items():
        for tn,tb in tg.items():
            z=K.gtest_z(fa,tb); mr,_=K.min_resid(fa,tb)
            if abs(z)>3 or mr<-4: flagged.append((fn,l,tn,fa,tb,z,mr))
    # compact per-l line for the KEY target d
    line=[f"{fn}:z={K.gtest_z(fs[fn],tg['d']):+.1f}/mr={K.min_resid(fs[fn],tg['d'])[0]:+.1f}" for fn in fs]
    print(f"  l={l:>2} vs d:  " + "   ".join(line))

print("\nperm-confirm any analytic flag (|z|>3 or min-resid<-4):")
if not flagged:
    print("  (none flagged by triage)")
for fn,l,tn,fa,tb,z,mr in flagged[:8]:
    _,pz=K.perm_p(fa,tb,K.gtest_z,B=400,worse="ge")
    _,pm=K.perm_p(fa,tb,lambda a,b:K.min_resid(a,b)[0],B=400,worse="le")
    print(f"  {fn} l={l} vs {tn}: z={z:+.2f}(MI p={pz:.3f})  min-resid={mr:+.2f}(excl p={pm:.3f})")

print("\nPOSITIVE CONTROL n vs k mod 7 (exclusion):")
_,p7=K.perm_p([v%7 for v in NS],[v%7 for v in KS],lambda a,b:K.min_resid(a,b)[0],B=400,worse="le")
print(f"  perm p={p7:.3f}")
