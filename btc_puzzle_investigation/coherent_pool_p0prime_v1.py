#!/usr/bin/env python3
"""
coherent_pool_p0prime_v1.py -- executes PREREG_coherent_pool_P0prime_v1.md.

P0' = the first statistic in the twist/row-budget suite with INV > 0: a SIGNED
cross-prime pool  W(A) = sum_p s_p^A * q_p  of the row-budget per-prime signed
score  q_p = R*charTotal_p - nullTotal_p  (exact integer; sign(q_p)=sign(z_p)),
ranked against the per-prime SIGN-PERMUTATION null with an EXACT integer p-value
(all 2^k sign patterns enumerated -- here via an exact integer DP over the
subset sums, which is the same count without the 4M-term Python loop).

The four existing detectors are sign-blind (S(s_p*plant)=S(plant), INV=0) because
each factors through |.|^2 / an even moment.  P0' pools the sign the others throw
away: flipping one prime's sign moves W by 2*s_p*q_p != 0, so INV > 0.

THIS FILE = the POOLING LAYER + its instrument validation on SYNTHETIC scores
(Stage A).  It touches NO real data, so it cannot see the pre-registered signal.
It (1) reproduces the frozen exact p-value floors 158/4096, 598/4096, 22/1024,
112/1024 IN CODE; (2) runs the three prereg gates PC-COH / PC-ANTI / NULL-vs-NULL
on synthetic scores; (3) confirms INV>0 operates.  The real-data hooks (q_p from
the row-budget instrument) are specified for Stage B/C but not exercised here.

EXACTNESS (btc CLAUDE.md).  The decision path is EXACT INTEGER end to end: q_p,
s_p, W, and the p-value (an integer count over 2^k patterns / 2^k) are all int.
The ONLY float is the cosmetic display Z=W/sqrt(k) (# noqa: float), never a
verdict.  check_no_float.py must pass on this file.
"""
import argparse
from fractions import Fraction


# ---------------------------------------------------------------------------
# EXACT p-value: distribution of  sum_p eps_p * |q_p|,  eps in {+-1}^k.
# Enumerating all 2^k sign patterns and counting |sum| >= |W| is exactly an
# integer convolution of {-|q|, +|q|} over the k unforced primes.  All counts
# are exact Python ints; no float, no sampling.
# ---------------------------------------------------------------------------
def sign_perm_distribution(mags):
    """mags: list of positive ints |q_p| (q_p != 0).  Returns dict {sum: count}
       giving the exact number of eps in {+-1}^k with sum_p eps_p*|q_p| == sum."""
    dist = {0: 1}
    for a in mags:
        nd = {}
        for s, ctimes in dist.items():
            nd[s + a] = nd.get(s + a, 0) + ctimes
            nd[s - a] = nd.get(s - a, 0) + ctimes
        dist = nd
    return dist


def exact_pool_pvalue(q, s):
    """q: list of int per-prime signed scores; s: list of int alignment signs +-1.
       Returns (num, den, W, k): two-sided exact integer sign-permutation p-value
       num/den for the observed pool W = sum s_p*q_p, over the k = #{q_p != 0}
       UNFORCED primes (q_p == 0 contribute 0 and are dropped, per the drill rule
       'count only unforced contributions')."""
    mags = [abs(qp) for qp in q if qp != 0]
    k = len(mags)
    W = sum(sp * qp for sp, qp in zip(s, q))
    if k == 0:
        return 1, 1, 0, 0
    dist = sign_perm_distribution(mags)
    aW = abs(W)
    num = sum(c for val, c in dist.items() if abs(val) >= aW)
    den = 1 << k
    return num, den, W, k


def z_display(W, k):
    return W / (k ** 0.5)                                   # noqa: float  (display only)


# ---------------------------------------------------------------------------
# (1) reproduce the frozen exact p-value floors (prereg section 5)
# ---------------------------------------------------------------------------
def reproduce_floors():
    checks = []
    # a aligned out of k, unit magnitudes: q = [+1]*a + [-1]*(k-a), A0 = all +1.
    # W = a - (k-a) = 2a-k; p = #{|sum eps|>=|W|}/2^k.
    def floor(k, a):
        q = [1] * a + [-1] * (k - a)
        s = [1] * k
        num, den, W, kk = exact_pool_pvalue(q, s)
        return num, den, W
    n1, d1, W1 = floor(12, 10); checks.append(("p(10/12)", n1, d1, W1, 158, 4096))
    n2, d2, W2 = floor(12, 9);  checks.append(("p(9/12)",  n2, d2, W2, 598, 4096))
    n3, d3, W3 = floor(10, 9);  checks.append(("p(9/10)",  n3, d3, W3, 22, 1024))
    n4, d4, W4 = floor(10, 8);  checks.append(("p(8/10)",  n4, d4, W4, 112, 1024))
    print("=== (1) EXACT p-value floors (reproduce frozen prereg section 5) ===")
    ok = True
    for name, num, den, W, enum, eden in checks:
        good = (num == enum and den == eden)
        ok = ok and good
        print(f"  {name:9s}  W={W:+3d}  p = {num:4d}/{den:5d}  "
              f"(frozen {enum}/{eden})  {'OK' if good else 'MISMATCH'}")
    return ok


# ---------------------------------------------------------------------------
# (2) power table cross-check, EXACT via Fraction (prereg section 5 table)
#     P(>=10 aligned | Binom(12, pi)),  pi = coherent-sign probability.
# ---------------------------------------------------------------------------
def binom_ge(k, a, pi):
    """Exact Fraction P(X >= a),  X ~ Binomial(k, pi),  pi a Fraction."""
    from math import comb
    return sum(Fraction(comb(k, i)) * pi ** i * (1 - pi) ** (k - i)
               for i in range(a, k + 1))


def power_table():
    print("\n=== (2) power table  P(>=10/12 aligned | Binom(12, pi))  [exact Fraction] ===")
    frozen = {Fraction(3, 5): "0.083", Fraction(7, 10): "0.253",
              Fraction(4, 5): "0.558", Fraction(9, 10): "0.889"}
    ok = True
    for pi, ref in frozen.items():
        val = binom_ge(12, 10, pi)
        approx = (val.numerator * 1000) // val.denominator          # milli, integer
        shown = f"0.{approx:03d}"
        good = abs(approx - round_str(ref)) <= 1                     # within 1 milli
        ok = ok and good
        print(f"  pi={str(pi):5s}  power = {val.numerator}/{val.denominator} "
              f"~ {shown}   (frozen {ref})  {'OK' if good else 'CHECK'}")
    return ok


def round_str(s):
    # "0.083" -> 83   (milli), integer only
    return int(s.split(".")[1])


# ---------------------------------------------------------------------------
# (3) the three prereg gates on SYNTHETIC scores (prereg section 4)
# ---------------------------------------------------------------------------
def gate_pc_coh(k=12, E=5):
    """Coherent plant q_p = +E for all p, A0 = all +1.  Must fire at the floor
       p = 2/2^k."""
    q = [E] * k
    s = [1] * k
    num, den, W, kk = exact_pool_pvalue(q, s)
    fires = (num == 2 and den == (1 << k))
    print(f"\n=== (3a) PC-COH  (coherent plant MUST fire) ===")
    print(f"  q_p=+{E} x{k}, A0=+1 -> W={W}  p = {num}/{den}  "
          f"(floor 2/{1<<k})  {'FIRES-at-floor' if fires else 'FAIL->VOID'}")
    return fires


def gate_pc_anti(E=5):
    """Anti-coherent plant q_p = chi4(p)*E on a residue-BALANCED set, A0=+1.
       Must COLLAPSE (W~0, p non-significant).  Uses a clean balanced 12-set to
       isolate INV: identical |q_p| magnitudes as PC-COH, opposite sign pattern
       -> wildly larger p.  That gap IS INV>0 operating in code."""
    # 6 primes p=1(4), 6 primes p=3(4): chi4 = +1 / -1
    chi4 = [1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1]
    q = [c * E for c in chi4]
    s = [1] * 12
    num, den, W, kk = exact_pool_pvalue(q, s)
    # contrast: same magnitudes, coherent alignment -> the floor
    numc, denc, Wc, _ = exact_pool_pvalue([E] * 12, [1] * 12)
    collapses = (W == 0 and num == den)          # perfectly balanced -> p = 1
    print(f"\n=== (3b) PC-ANTI  (anti-coherent plant MUST collapse) ===")
    print(f"  q_p=chi4(p)*{E}, A0=+1 -> W={W}  p = {num}/{den} = {Fraction(num,den)}")
    print(f"  contrast (same |q_p|, coherent) -> W={Wc}  p = {numc}/{denc}  "
          f"(the floor)")
    print(f"  INV operating: identical magnitudes, p moves {numc}/{denc} -> "
          f"{num}/{den}.  {'COLLAPSES' if collapses else 'FAIL->VOID'}")
    return collapses


def gate_null_vs_null(reps=20000, k=12, seed=20260823):
    """NULL-vs-NULL calibration: synthetic fair-coin scores (symmetric, zero-mean
       integer draws), pool under A0.  The exact p-value must be ~Uniform and the
       sign split ~50/50.  A forced directional bias would make it fire.
       (Synthetic stand-in for 'MN-mu6 replicate as pseudo-char'.)"""
    import random
    rng = random.Random(seed)
    # symmetric integer score: uniform on {-3..-1,1..3} (never 0 -> all unforced)
    vals = [-3, -2, -1, 1, 2, 3]
    fire05 = 0
    neg_signs = 0
    tot_signs = 0
    for _ in range(reps):
        q = [rng.choice(vals) for _ in range(k)]
        s = [1] * k
        num, den, W, kk = exact_pool_pvalue(q, s)
        if num * 20 < den:          # exact:  p < 0.05  <=>  20*num < den
            fire05 += 1
        for qp in q:
            tot_signs += 1
            if qp < 0:
                neg_signs += 1
    print(f"\n=== (3c) NULL-vs-NULL  (must be ~50/50, p~Uniform, must NOT fire) ===")
    print(f"  {reps} synthetic fair-coin pools:  fire@0.05 = {fire05}/{reps} "
          f"~ {Fraction(fire05, reps)} (expect ~1/20)")
    print(f"  sign split neg = {neg_signs}/{tot_signs} "
          f"~ {Fraction(neg_signs, tot_signs)} (expect ~1/2)")
    # calibration OK if fire rate within a loose band of 0.05 and signs ~0.5
    fr = Fraction(fire05, reps)
    ss = Fraction(neg_signs, tot_signs)
    good = (Fraction(2, 100) < fr < Fraction(9, 100)) and \
           (Fraction(47, 100) < ss < Fraction(53, 100))
    print(f"  calibration {'OK (does not fire; ~50/50)' if good else 'CHECK'}")
    return good


# ---------------------------------------------------------------------------
# Stage-B/C hook (spec only; not exercised here)
# ---------------------------------------------------------------------------
def q_from_rowbudget_totals(char_total, null_total_sum, R):
    """Stage B: exact integer per-prime score from the row-budget instrument.
       char_total  = tot['char']            (sum_f N_LOW_char, INTEGER)
       null_total_sum = tot['mu6'].sum()    (sum_f sum_r N_LOW_mu6(r), INTEGER)
       q_p = R*char_total - null_total_sum  in Z ;  sign(q_p) = sign(z_p).
       NOTE: row_budget_run_v1.py currently emits Nbar (float = tot/m); Stage B
       must have it also emit the raw INTEGER tot['char'] and int(tot['mu6'].sum())
       so the pool stays exact-integer (do not reconstruct from the float Nbar)."""
    return R * int(char_total) - int(null_total_sum)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", choices=["validate"], default="validate")
    ap.parse_args()
    print("P0' coherent-pool driver -- STAGE A instrument validation (synthetic, "
          "no real data)\n")
    r1 = reproduce_floors()
    r2 = power_table()
    r3a = gate_pc_coh()
    r3b = gate_pc_anti()
    r3c = gate_null_vs_null()
    print("\n=== SUMMARY ===")
    print(f"  (1) exact floors reproduced      : {'PASS' if r1 else 'FAIL'}")
    print(f"  (2) power table (exact Fraction) : {'PASS' if r2 else 'FAIL'}")
    print(f"  (3a) PC-COH fires at floor       : {'PASS' if r3a else 'FAIL'}")
    print(f"  (3b) PC-ANTI collapses (INV>0)   : {'PASS' if r3b else 'FAIL'}")
    print(f"  (3c) NULL-vs-NULL calibrated     : {'PASS' if r3c else 'FAIL'}")
    allpass = all([r1, r2, r3a, r3b, r3c])
    print(f"\n  STAGE A pooling instrument: {'VALIDATED' if allpass else 'NOT VALIDATED'}")
    print("  (real-data q_p = Stage B/C; held-out S needs a reconstructed frozen "
          "freq-list -- generator not on disk)")


if __name__ == "__main__":
    main()
