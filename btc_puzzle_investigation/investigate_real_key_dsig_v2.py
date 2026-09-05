#!/usr/bin/env python3
"""
ALL real solved keys (not a low-bit subsample). Show every key's D-signature
magnitude pattern, reconstruct ALL, and hunt for any deviation from the generic
'doubling' pattern that would indicate a structured (sum-of-fractions) key.
"""
import csv
def d_recursion(N, error):
    sig=[]; e=abs(error)
    while e>0:
        D=N//e
        if D==0: break
        sig.append(D); e=abs(e-N//D)
    return sig
def reconstruct(N,D):
    Dl=D[-1]; poss=list(range(N//(Dl+1)+1, N//Dl+1))
    for d in reversed(D[:-1]):
        c=N//d; nn=[]
        for e in poss:
            for s in (1,-1):
                x=c+s*e
                if x>0 and N//x==d: nn.append(x)
        poss=sorted(set(nn))
        if not poss: return None
    return poss

rows=[(int(r["bits"]), int(r["private_key"],16), r["puzzle"])
      for r in csv.DictReader(open("puzzles_verified.csv"))]
rows=sorted([r for r in rows if r[0]>=20])          # drop degenerate tiny keys
print(f"real solved keys with P>=20: {len(rows)}\n")

print("ALL keys — full-key recursion (N=2^P): term bit-length pattern + early D-values")
print(f"{'pz':>4} {'P':>4} {'#t':>3}  {'D-term bit-lengths':<40} {'early D-values'}")
recon_ok=0; patterns=[]
for P,d,pz in rows:
    N=1<<P; sig=d_recursion(N,d)
    bl=[max(x.bit_length()-1,0) for x in sig]
    rec=reconstruct(N,sig); ok = rec is not None and d in rec
    recon_ok+=ok
    patterns.append((P,bl,sig))
    early=[x for x in sig[:4]]
    print(f"{pz:>4} {P:>4} {len(sig):>3}  {str(bl):<40} {early}")
print(f"\nreconstruction exact: {recon_ok}/{len(rows)}")

# ---- deviation from doubling: for each key, ratio pattern of consecutive term bitlens ----
print("\nDOUBLING CHECK — a 'structured' key would have early terms that DON'T double.")
print("For each key, gaps between consecutive nonzero term bit-lengths (doubling≈ each ~= previous):")
import statistics as st
allgaps=[]
for P,bl,sig in patterns:
    nz=[b for b in bl if b>0]
    gaps=[round(nz[i+1]/nz[i],2) for i in range(len(nz)-1)] if len(nz)>1 else []
    allgaps+=gaps
    if P>=60:
        print(f"  P={P:>3}: bitlens={nz}  ratios={gaps}")
print(f"\n  all consecutive ratios: mean={st.mean(allgaps):.2f} median={st.median(allgaps):.2f} "
      f"(≈2.0 = pure doubling / random; <1.5 early = structural)")

# ---- cross-key: do specific early D-values repeat more than chance? ----
from collections import Counter
print("\nCROSS-KEY early D-value frequency (D_1,D_2,D_3 pooled across all keys):")
for idx in (1,2,3):
    vals=[sig[idx] for P,bl,sig in patterns if len(sig)>idx]
    c=Counter(vals)
    print(f"  D_{idx}: {len(set(vals))} distinct / {len(vals)} keys; most common: {c.most_common(5)}")
