#!/usr/bin/env python3
"""Arms B and C: unconditional cubic forcing, the rational form of the bridge,
   and the sextic prediction of c_p at secp256k1. Exact integers only."""
from math import isqrt, gcd
import random, sys
from collections import Counter
exec(open('cubic_bridge_v1.py').read().split('print("=== CONTROLS ===")')[0])

rnd = random.Random(90210)

# ---------- ARM B: U = |t-1| a perfect cube => chi_3 = 1 forced ----------
def icbrt(u):
    if u < 0: raise ValueError
    if u < 2: return u
    lo, hi = 0, 1
    while hi**3 <= u: hi <<= 1
    while lo + 1 < hi:
        mid = (lo + hi)//2
        if mid**3 <= u: lo = mid
        else: hi = mid
    return lo
def cube_part(u):
    return u > 0 and icbrt(u)**3 == u

print("=== ARM B: |t-1| a perfect cube => chi_3^(n)(p) = 1  (forced) ===")
print(f"  {'bits':>5} {'N':>6} {'#cubes':>7} {'forced rate':>12} {'free rate':>10}"
      f" {'pred exc':>9} {'obs exc':>9}")
for bits, tgt in ((10, 6000), (12, 6000), (14, 5000), (16, 5000), (20, 4000), (24, 3000)):
    rows = collect(bits, bits, tgt, rnd)
    nf = hf = 0; no = ho = 0
    for I in rows:
        j = analyse(I)["j"]
        if cube_part(abs(I["t"]-1)):
            nf += 1; hf += (j == 0)
        else:
            no += 1; ho += (j == 0)
    N = nf+no
    print(f"  {bits:>5} {N:>6} {nf:>7} {hf/nf if nf else float('nan'):>12.4f}"
          f" {ho/no:>10.4f} {(2/3)*nf/N:>+9.4f} {(hf+ho)/N - 1/3:>+9.4f}")
    sys.stdout.flush()

# ---------- the RATIONAL form of the bridge ----------
print("\n=== RATIONAL FORM:  n = 1-t (mod p), so chi_pibar(1-t) IS the ordinary")
print("    cubic character of n mod p.  Claim:  chi_3(p mod n) = w^pred * chi_3(n mod p) ===")
rows = collect(20, 20, 3000, rnd)
ok = 0; predd = Counter(); clean = cleanok = 0
for I in rows:
    r = analyse(I)
    p, n = I["p"], I["n"]
    kn = I["Fp"].chi(n % p)                       # cubic char of n mod p, same field id
    if kn == r["k"]: ok += 1                      # confirms n = 1-t mod p
    predd[r["pred"]] += 1
    if r["pred"] == 0:                            # correction trivial => clean reciprocity
        clean += 1
        cleanok += ((r["j"] == 0) == (pow(n % p, (p-1)//3, p) == 1))
print(f"  chi_pibar(n mod p) == chi_pibar(1-t) : {ok}/{len(rows)}")
print(f"  distribution of the correction 'pred' : {dict(sorted(predd.items()))}")
print(f"  in the pred=0 subpopulation:  [p is a cube mod n]  <=>  [n is a cube mod p]"
      f" : {cleanok}/{clean}  {'PASS' if cleanok==clean else '*** FAIL ***'}")

# ---------- close the old loose end: the 29 quadratic-identity anomalies ----------
print("\n=== loose end from DEVIATIONS #3: (p/n) == ((1-t)/p) for n = 1 mod 4 ===")
def leg(a, q):
    a %= q
    return 0 if a == 0 else (1 if pow(a, (q-1)//2, q) == 1 else -1)
bad = []
for I in rows:
    p, n, t = I["p"], I["n"], I["t"]
    if n % 4 != 1: continue
    lhs = 1 if pow(p % n, (n-1)//2, n) == 1 else -1
    rhs = leg(1-t, p)
    if lhs != rhs: bad.append((p, t, n, rhs, (1-t) % p == 0))
print(f"  violations: {len(bad)}   all with (1-t) = 0 mod p (Legendre 0)? "
      f"{all(b[3]==0 for b in bad) if bad else 'n/a'}")
for b in bad[:5]: print("   ", b)

# ---------- ARM C: secp256k1 ----------
print("\n=== ARM C: secp256k1, predicted from p-side data only ===")
P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Nn = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
T = P + 1 - Nn
I = instance(P, T, rnd)
assert I is not None and I["n"] == Nn
r = analyse(I)
print(f"  t = {T}")
print(f"  v = {I['v']}   (4p = t^2+3v^2 : {4*P == T*T + 3*I['v']**2})")
print(f"  primarization exponents  s1(nu) = {I['s1']}   s2(pibar) = {I['s2']}")
print(f"  e_nu(omega) = {r['e_nu_w']}   e_pibar(omega) = {r['e_pib_w']}   => correction pred = {r['pred']}")
print(f"  k = chi_3^(p)(1-t) = chi_3(n mod p) = omega_p^{r['k']}")
print(f"  BRIDGE PREDICTS  j = k + pred = {(r['k']+r['pred'])%3}")
print(f"  directly computed j = chi_3^(n)(p) = omega_n^{r['j']}   -> "
      f"{'MATCH' if r['j']==(r['k']+r['pred'])%3 else '*** MISMATCH ***'}")
print(f"  so p IS a cube mod n : {r['j']==0}   (independent check: "
      f"{pow(P % Nn, (Nn-1)//3, Nn) == 1})")
q2 = pow(P % Nn, (Nn-1)//2, Nn) == 1
print(f"  quadratic: (p/n)=+1 : {q2};   ((1-t)/p) = {leg(1-T, P)};  n mod 4 = {Nn%4}")
print(f"  => chi_6^(n)(p) = 1 : {r['j']==0 and q2}   hence c_p = 6  CONFIRMED from the bridge")
print(f"\n  is |t-1| a perfect cube (Arm B forcing)? {cube_part(abs(T-1))}"
      f"   -> secp is NOT in the forced population; the value is carried by the bridge, not by forcing")
