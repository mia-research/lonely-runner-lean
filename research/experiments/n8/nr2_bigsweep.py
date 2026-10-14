r"""
nr2_bigsweep  --  extend the empirical base for  (H):  every PRIMITIVE base tuple
other than {1,3,5,7,4} has |S| >= 1/2.

Two independent parts.

  (E) EXHAUSTIVE over q_rho in [0,QMAX] for all three rho0, primitive tuples only
      (gcd(E_non) = 1; the composite ones are closed by the Reduction Theorem).
      Reports min |S|, the argmin, and every tuple with |S| <= 1/2.

  (R) RANDOM, seeded, with speeds far outside the exhaustive box: q_rho drawn
      uniformly from [0,QBIG].  Same exact arithmetic; this probes the large-speed
      regime that an exhaustive sweep cannot reach.

Exact integer arithmetic; every cell evaluated at its ENTRY point; the full 8-bit
union mask is used, so every uncovered residue is tracked (requirement (ii)).

Usage:  python3 nr2_bigsweep.py QMAX QBIG NRAND SEED
"""
import itertools, sys, random
from math import gcd
from fractions import Fraction as F
from nr2_core import safe_measure

QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 8
QBIG = int(sys.argv[2]) if len(sys.argv) > 2 else 400
NRAND = int(sys.argv[3]) if len(sys.argv) > 3 else 20000
SEED = int(sys.argv[4]) if len(sys.argv) > 4 else 20260908

HALF = F(1, 2)
print(f"(E) EXHAUSTIVE  q <= {QMAX}  (speeds <= {8*QMAX+7}), primitive only")
for rho0 in (2, 4, 6):
    rhos = (1, 3, 5, 7, rho0)
    mn = None
    n = 0
    low = []
    for qs in itertools.product(range(QMAX + 1), repeat=5):
        sp = tuple(8 * q + r for q, r in zip(qs, rhos))
        if len(set(sp)) != 5:
            continue
        g = 0
        for e in sp:
            g = gcd(g, e)
        if g != 1:
            continue
        n += 1
        m = safe_measure(sp, rhos)
        if m <= HALF:
            low.append((m, sp))
        if mn is None or m < mn[0]:
            mn = (m, sp)
    print(f"   rho0={rho0}: {n} primitive tuples;  min |S| = {mn[0]} = {float(mn[0]):.6f}"
          f" at {mn[1]}")
    print(f"      tuples with |S| <= 1/2 : {len(low)}"
          + ("" if not low else "   -> " + ", ".join(f"{str(m)}@{sp}" for m, sp in sorted(low)[:6])))
    sys.stdout.flush()

print(f"\n(R) RANDOM  q in [0,{QBIG}] (speeds <= {8*QBIG+7}), {NRAND} draws per rho0,"
      f" seed {SEED}, primitive only")
rng = random.Random(SEED)
for rho0 in (2, 4, 6):
    rhos = (1, 3, 5, 7, rho0)
    mn = None
    n = 0
    low = []
    tries = 0
    while n < NRAND and tries < 40 * NRAND:
        tries += 1
        qs = [rng.randrange(QBIG + 1) for _ in range(5)]
        sp = tuple(8 * q + r for q, r in zip(qs, rhos))
        if len(set(sp)) != 5:
            continue
        g = 0
        for e in sp:
            g = gcd(g, e)
        if g != 1:
            continue
        n += 1
        m = safe_measure(sp, rhos)
        if m <= HALF:
            low.append((m, sp))
        if mn is None or m < mn[0]:
            mn = (m, sp)
    print(f"   rho0={rho0}: {n} primitive draws;  min |S| = {mn[0]} = {float(mn[0]):.6f}"
          f" at {mn[1]}")
    print(f"      draws with |S| <= 1/2 : {len(low)}"
          + ("" if not low else "   -> " + ", ".join(f"{str(m)}@{sp}" for m, sp in sorted(low)[:6])))
    sys.stdout.flush()

# (D) the dilate family, exactly: E_non = lam * {1,3,5,7,4}, lam odd -> |S| = 5/14
print("\n(D) the dilate family E_non = lam*{1,3,5,7,4}, lam odd (NON-primitive for lam>1)")
rows = []
for lam in range(1, 40, 2):
    sp = tuple(lam * e for e in (1, 3, 5, 7, 4))
    rhos = tuple(e % 8 for e in sp)
    if len(set(rhos)) != 5 or 0 in rhos:
        rows.append((lam, "not unit-complete", None))
        continue
    rows.append((lam, rhos, safe_measure(sp, rhos)))
for lam, rh, m in rows[:12]:
    print(f"   lam={lam:>3}: residues {rh}  |S| = {m}")
print("   (|S| = 5/14 throughout, as the Dilation Theorem predicts; only lam = 1 is")
print("    primitive, and that tuple is the one Lemma D closes.)")
