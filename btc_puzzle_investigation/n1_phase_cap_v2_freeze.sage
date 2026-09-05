#!/usr/bin/env sage
# n1_phase_cap_v2_freeze.sage — C-FREEZE (spec section 4.4 of PREREG_n1_phase_cap_v2.md).
#
# Materializes the frozen holdout list and writes its SHA-256 BEFORE any V(a) is
# computed anywhere.  Only the SELECTION variables (p, n, primality, Hasse) are
# read here.  No S, no FFT, no character sum.
#
# Rule (verbatim from the spec, no discretion):
#   bands B_i = [10^(4.50+0.15(i-1)), 10^(4.50+0.15 i)), i = 1..10
#   per band, per stratum, scan p upward and accept iff
#     (a) p prime  (b) p = 7 mod 12 (ODD) or p = 1 mod 12 (EVEN)
#     (c) n = #E(F_p) prime  (d) integer Hasse guard (n-p-1)^2 <= 4p
#   take the FIRST 6 accepted per band per stratum  =>  K=60 per stratum, 120 total.
# Rejections are logged with a reason.  The run may not add, drop, re-band or re-order.

import hashlib

OUT = "PREREG_n1_phase_cap_v2_HOLDOUT.txt"
STRATA = [("ODD", 7), ("EVEN", 1)]

rows = []
rej = {"not_1mod3": 0, "n_composite": 0, "hasse": 0}
for i in range(1, 11):
    lo = ZZ(ceil(10 ** (4.50 + 0.15 * (i - 1))))
    hi = ZZ(ceil(10 ** (4.50 + 0.15 * i)))
    for sname, sres in STRATA:
        got = 0
        p = lo - 1
        while got < 6:
            p = next_prime(p)
            if p >= hi:
                raise RuntimeError(f"band {i} stratum {sname} exhausted at {p}")
            if p % 12 != sres:
                continue
            if p % 3 != 1:
                rej["not_1mod3"] += 1; continue
            n = EllipticCurve(GF(p), [0, 7]).cardinality()
            if not is_prime(n):
                rej["n_composite"] += 1; continue
            if (n - p - 1) ** 2 > 4 * p:                # integer Hasse guard
                rej["hasse"] += 1; continue
            rows.append((i, sname, int(p), int(n), int(p + 1 - n)))
            got += 1
        print(f"  band {i:>2} {sname:>4}: {[r[2] for r in rows[-6:]]}", flush=True)

with open(OUT, "w") as f:
    f.write("# PREREG_n1_phase_cap_v2 FROZEN HOLDOUT — band stratum p n trace\n")
    for b, s, p, n, t in rows:
        f.write(f"{b} {s} {p} {n} {t}\n")
h = hashlib.sha256(open(OUT, "rb").read()).hexdigest()

print()
print("=" * 88)
print("C-FREEZE COMPLETE — written BEFORE any V(a)/S is computed anywhere")
print("=" * 88)
print(f"  file    : {OUT}")
print(f"  primes  : {len(rows)}   ({sum(1 for r in rows if r[1]=='ODD')} ODD / "
      f"{sum(1 for r in rows if r[1]=='EVEN')} EVEN)")
print(f"  cells   : sum (n-1)/6 = {sum((r[3]-1)//6 for r in rows):,} distinct mu6 configurations")
print(f"  p range : {min(r[2] for r in rows)} .. {max(r[2] for r in rows)}")
print(f"  rejects : {rej}")
print(f"  SHA-256 : {h}")
print()
print("  PLANT PRIMES (P-DOSE) = first accepted of each band x stratum, frozen now:")
seen = set(); plant = []
for b, s, p, n, t in rows:
    if (b, s) not in seen:
        seen.add((b, s)); plant.append(p)
print(f"    {plant}")
