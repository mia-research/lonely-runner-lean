"""
DISCOVERY, not confirmation. Reconstruct the (n,k) decomposition on the real keys
and LOOK at what n,k actually encode -- to settle "n,k are not just the top bits".

For each key:
  u   = (d - 2^{N-1}) / 2^{N-1}          position in the band, in [0,1)
  n,k = best rational approx of u, n<=256 (continued-fraction convergent)
  base= 2^{N-1} + floor(2^{N-1} * k/n)   the key you'd rebuild from (n,k) alone
  D   = d - base                          residual

Questions I actually want answered by the numbers, not by assertion:
  (a) How many bits does (n,k) pin?  |u - k/n| vs 2^-8 (top-8-bit precision)
      and vs 1/n^2 (generic best-approx precision). If << 2^-8, then (n,k) is
      NOT the literal top 8 bits -- it is a number-theoretic coordinate that can
      encode far more, non-positionally.
  (b) How big is the residual D, in bits, relative to the N-1 free bits?
  (c) Does k/n line up with the LITERAL top bits of u, or diverge? (compare k/n
      to the 8-bit truncation of u) -- shows top-bits vs Farey-coordinate.
"""
import csv
from math import gcd, log2
from fractions import Fraction

def best_nk(d, N, nmax=256):
    lo=2**(N-1)
    u=Fraction(d-lo, lo)                 # exact rational position
    best=None
    for n in range(1,nmax+1):
        k=round(u*n)                     # nearest numerator
        err=abs(u-Fraction(int(k),n))
        if best is None or err<best[0]:
            best=(err,n,int(k))
    return best[1],best[2],best[0],u

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['puzzle']),int(r['bits']),int(r['private_key'],16),
                     int(r['n']),int(r['k'])))
rows.sort()

print(f"{'pz':>3} {'N':>3} {'n':>4} {'k':>4} | {'-log2|u-k/n|':>12} | {'|D|bits':>7} | "
      f"{'free':>4} | k/n vs top8(u)")
agg_pin=[]; agg_res=[]
for pz,N,d,ncsv,kcsv in rows:
    if N<8: continue
    n,k,err,u=best_nk(d,N)
    # sanity vs CSV
    tag="" if (n==ncsv and k==kcsv) else f" (CSV n,k={ncsv},{kcsv})"
    lo=2**(N-1)
    base=lo + (lo*k)//n
    D=d-base
    pin = float(-log2(float(err))) if err>0 else 999.0     # bits of positional precision
    resbits = (abs(D).bit_length())
    free=N-1
    top8=int(u*256)                                        # literal top 8 bits of u
    kn_top8=int(Fraction(k,n)*256)
    match = "same" if top8==kn_top8 else f"DIFFER({top8} vs {kn_top8})"
    agg_pin.append(pin); agg_res.append(resbits/free if free else 0)
    if pz in (9,11,14,25,35,63,90,110,125,130) or N<=16:
        print(f"{pz:>3} {N:>3} {n:>4} {k:>4} | {pin:12.1f} | {resbits:>7} | {free:>4} | {match}{tag}")

import statistics as st
print(f"\naggregate over {len(agg_pin)} keys (N>=8):")
print(f"  positional precision -log2|u-k/n|: median {st.median(agg_pin):.1f} bits, "
      f"max {max(agg_pin):.1f}  (top-8-bit truncation would give ~8)")
print(f"  residual |D| as fraction of the N-1 free bits: median {st.median(agg_res):.2f}, "
      f"min {min(agg_res):.2f}")
print("  => if precision >> 8 for many keys, (n,k) encodes a number-theoretic")
print("     coordinate finer/other than the literal top 8 bits.")
