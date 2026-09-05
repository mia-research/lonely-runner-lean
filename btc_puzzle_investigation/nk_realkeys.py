import numpy as np, pandas as pd
pv=pd.read_csv("puzzles_verified.csv")
sv=pv[pv.private_key.notna()].copy()
sv["d"]=[int(str(v),16) for v in sv.private_key]
print(f"solved/known-d puzzles: {len(sv)}  (bits {sv.bits.min()}..{sv.bits.max()})")

print("\n=== (3) NESTING: does key_N share low bits with key_{N+1}? ===")
sv=sv.sort_values("bits")
bad=0; checks=0
for i in range(len(sv)-1):
    a,b=int(sv.iloc[i].d),int(sv.iloc[i+1].d); nb=int(sv.iloc[i].bits)
    checks+=1; bad += (a != (b & ((1<<nb)-1)))   # is key_N == key_{N+1} mod 2^N ?
print(f"  key_N == key_(N+1) mod 2^N :  {checks-bad}/{checks} pairs match  => nested? {'YES' if bad==0 else 'NO'}")

print("\n=== real solved-key (n,k): any puzzle-specific structure the synthetic set lacks? ===")
print(f"  n values across solved puzzles: min={sv.n.min()} max={sv.n.max()} mean={sv.n.mean():.1f}")
from sympy import isprime
print(f"  P(n prime) real solved = {np.mean([isprime(int(v)) for v in sv.n]):.3f}  (uniform-Farey ~0.31)")
# correlation of n and k with puzzle number (sequence structure)
print(f"  corr(puzzle#, n) = {np.corrcoef(sv.bits, sv.n)[0,1]:+.3f}   corr(puzzle#, k/n) = {np.corrcoef(sv.bits, sv.k/sv.n)[0,1]:+.3f}")
print(f"  u_position range: {sv.u_position.min():.3f}..{sv.u_position.max():.3f} mean={sv.u_position.mean():.3f} (uniform=>0.5)")
# is n ever repeated / small? small n = wide cell = closer to a rational
print(f"  small n (<=8) count: {(sv.n<=8).sum()}/{len(sv)};  n distribution head:")
print("   ", dict(sv.n.value_counts().head(10)))
print("\nDONE")
