#!/usr/bin/env python3
"""
Brick E run pipeline (per PREREG_brick_e_cd_degree_v2.md, frozen e3fe35d0, frame-gate CLEARED R2).
THIS FILE builds the NULL side only + the calibration control (iii) + the engine control (i).
It does NOT read the real c+(d) arm — that read is gated on ALL FOUR controls firing, and controls
(ii) [mu3-covariant low-degree plant] and (iv) [rho-identity, needs Sage F_{p^2}] are not yet built.

Exact integer arithmetic; no float in the signal path (permutation p-values are integer ratios).
"""
import random
from brick_e_degree_fitter_v1 import min_degree_fit, invert_fit, factorize

# ---- p=43 frozen parameters (from lbe_dlog.sage + brick_e_anew_Lpoly_v1.sage) ----
P = 43
N = 31                      # |E(F_43)| = n
M = 1893                    # |A_new(F_p)| = 3*631
LARGE = 631                 # large prime factor: the Q-values are distinct mod 631
KAPPA = 1849                # c+(lambda d) = kappa * c+(d),  kappa^3 == 1 mod 1893
LAM = 25                    # GLV scalar mod n (c+(25 d)=kappa c+(d))

# mu3-orbit representatives of the QR-half Q (reps=5), each orbit {r, 25r, 5r} mod 31
REPS = [3, 4, 6, 12, 17]
def orbit(r):
    return [r % N, (LAM*r) % N, (LAM*LAM*r) % N]   # [r, 25r, 5r]
ORBITS = {r: orbit(r) for r in REPS}
Q = sorted(d for r in REPS for d in ORBITS[r])      # the 15 QR-half indices

# sanity: kappa is a nontrivial cube root of 1 mod M
assert pow(KAPPA, 3, M) == 1 and KAPPA % M != 1, "kappa not a nontrivial cube root of 1 mod M"

def make_mu3_covariant(rep_values):
    """Given {rep: value in Z/M}, build the full mu3-covariant map c: Q -> Z/M by
    c(25 r)=kappa*c(r), c(5 r)=kappa^2*c(r)."""
    c = {}
    for r, base in rep_values.items():
        d0, d1, d2 = orbit(r)            # r, 25r, 5r
        c[d0] = base % M
        c[d1] = (KAPPA * base) % M
        c[d2] = (KAPPA * KAPPA * base) % M
    return c

def degree_stat(cmap, mod):
    """Headline D = min-degree fit over the LARGE factor (per DEVIATIONS D1)."""
    pts = {d: cmap[d] % mod for d in cmap}
    D, coeffs = min_degree_fit(pts, mod)
    return D, coeffs

def draw_null(rng):
    return make_mu3_covariant({r: rng.randrange(M) for r in REPS})

def null_histogram(n_draws, seed):
    rng = random.Random(seed)
    Ds = []
    for _ in range(n_draws):
        D, _ = degree_stat(draw_null(rng), LARGE)
        Ds.append(D if D is not None else 10**9)
    return Ds

def pval(D_obs, null_Ds):
    # one-sided: fraction of null draws with D' <= D_obs  (low D = evidence)
    le = sum(1 for d in null_Ds if d <= D_obs)
    return le, len(null_Ds)           # integer numerator/denominator (exact)

if __name__ == "__main__":
    print(f"p={P}  Q(|{len(Q)}|)={Q}")
    print(f"mu3 orbits: {ORBITS}")

    # ---- CONTROL (i): engine (already unit-tested in brick_e_degree_fitter_v1) ----
    # quick re-affirm: a planted degree-2 (non-covariant) recovers D=2
    plant2 = {d: (777*d*d + 123) % LARGE for d in Q}
    D2, _ = min_degree_fit(plant2, LARGE)
    print(f"\n[ctrl i  engine ] planted deg-2 over Q mod {LARGE}: D={D2} (expect 2): {'FIRE' if D2==2 else 'FAIL'}")

    # ---- NULL HISTOGRAM (the calibrated reference; NOT the real arm) ----
    NDRAWS = 4000
    null_Ds = null_histogram(NDRAWS, seed=20260821)
    finite = [d for d in null_Ds if d < 10**9]
    none_ct = len(null_Ds) - len(finite)
    from collections import Counter
    hist = Counter(null_Ds)
    print(f"\n[null hist] {NDRAWS} mu3-covariant draws, D over mod {LARGE}:")
    for d in sorted(hist):
        tag = "(no fit)" if d >= 10**9 else ""
        print(f"    D={d if d<10**9 else 'None'}: {hist[d]:5d}  {tag}")
    if finite:
        finite.sort()
        print(f"    finite D: min={finite[0]} median={finite[len(finite)//2]} max={finite[-1]}  None={none_ct}")

    # ---- CONTROL (iii): CALIBRATION -- CORRECTED (DEVIATIONS D3) ----
    # APPLICABILITY GATE FIRST: pi ~ Uniform is only sensible when the null-D statistic has spread.
    # If D takes <=2 distinct values, its p-value is discrete and piles up at 1.0 -> CANNOT be Uniform;
    # control (iii) is INAPPLICABLE at such a degenerate rung (true at p=43: D in {13,14}).
    distinct_D = sorted(set(null_Ds))
    if len(distinct_D) <= 2:
        print(f"\n[ctrl iii calib] INAPPLICABLE at this rung: null D is degenerate (values {distinct_D}).")
        print("    A two-valued statistic has a discrete p-value that cannot be Uniform. Skip; this")
        print("    control becomes meaningful only where the null D-histogram has spread (p>=163).")
    else:
        rng = random.Random(999)
        K = 500
        ps = []
        for _ in range(K):
            D, _ = degree_stat(draw_null(rng), LARGE)
            Dv = D if D is not None else 10**9
            le, tot = pval(Dv, null_Ds)
            ps.append(le / tot)          # display float only; verdict below is a bound, not float-decided
        ps.sort()
        # CORRECT KS: max over k of max(|k/K - p_(k)|, |(k-1)/K - p_(k)|)
        ks = 0.0
        for k, p in enumerate(ps, start=1):
            ks = max(ks, abs(k / K - p), abs((k - 1) / K - p))
        print(f"\n[ctrl iii calib] {K} null draws, empirical p ~ Uniform?  KS = {ks:.3f}  "
              f"{'CALIBRATED (<0.10)' if ks < 0.10 else 'FAIL (miscalibrated)'}")

    print("\nNOTE: real c+(d) arm NOT read. Blocked on controls (ii) mu3-covariant low-degree plant")
    print("      and (iv) rho-identity (Sage/F_{p^2}). See PREREG v2 §5.")
