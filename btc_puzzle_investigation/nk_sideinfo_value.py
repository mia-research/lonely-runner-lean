import numpy as np, pandas as pd, math
from sympy import totient
df=pd.read_csv("constructed_keys_1to160_100k.csv", dtype={"D":str,"d":str})
def H(x):
    v,c=np.unique(x,return_counts=True); p=c/c.sum(); return -(p*np.log2(p)).sum()

print("=== (1) Is N -> D_terms? how many bits does D_terms add beyond N? ===")
print("  D_terms by top bands:")
for lo in (121,141):
    sub=df[(df.bits>=lo)&(df.bits<lo+20)]
    print(f"    bits {lo}-{lo+19}: D_terms dist = {dict(sub.D_terms.value_counts().sort_index())}")
# H(D_terms) marginal vs conditional on bits  -> info N gives about D_terms
HDt=H(df.D_terms.values)
HDt_given_N=np.average([H(df[df.bits==b].D_terms.values) for b in df.bits.unique()],
                       weights=[ (df.bits==b).sum() for b in df.bits.unique()])
print(f"  H(D_terms)={HDt:.3f} bits ; H(D_terms|N)={HDt_given_N:.3f} bits ; N tells you {HDt-HDt_given_N:.3f} bits about D_terms")
print("  => knowing D_terms beyond N is worth <= H(D_terms|N) bits, and D_terms<=~6 values (<3 bits total).")

print("\n=== (2) does the (n,k,D) decomposition beat direct kangaroo?  COST RATIO ===")
# per-cell (n,k): max|D| ~ Farey width ~ A/(n*n_next) ~ A/n^2 ; kangaroo cost ~ sqrt(max|D|) ~ sqrt(A)/n
# total decomposition attack cost (must try candidates until true one) = sqrt(A)*sum_{n,k gcd=1} 1/n
S=0.0
for n in range(1,257):
    S += totient(n)/n            # sum over k coprime to n of 1/n  = phi(n)/n
print(f"  sum_{{n<=256}} phi(n)/n = {S:.1f}  (= {math.log2(S):.2f} bits)")
print(f"  decomposition total cost = {math.log2(S):.2f} + (N-1)/2 bits ;  direct kangaroo = (N-1)/2 bits")
print(f"  => decomposition is ~2^{math.log2(S):.1f} = {S:.0f}x WORSE than direct (reparameterization, no entropy reduction).")
print(f"     Reason: cheap-to-guess (small n) cells have the LARGEST |D| (dearest DLP); the product is bounded below.")
print(f"     Only escape: a PUBLIC lean on (n,k) costing < {math.log2(S):.1f} bits. Battery found none.")

print("\n=== (3) are the REAL puzzle keys NESTED (cross-key structure)? ===")
try:
    pv=pd.read_csv("puzzles_verified.csv")
    print("  columns:", list(pv.columns))
    # find the private-key column
    kc=[c for c in pv.columns if c.lower() in ("d","priv","privkey","private_key","key","dec")]
    print("  candidate key cols:", kc, "| first rows:")
    print(pv.head(4).to_string(index=False)[:600])
except Exception as e:
    print("  could not load puzzles_verified.csv:", e)
print("\nDONE")
