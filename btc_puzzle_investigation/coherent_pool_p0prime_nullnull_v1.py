#!/usr/bin/env python3
"""
coherent_pool_p0prime_nullnull_v1.py -- the real-data NULL-vs-NULL gate of
PREREG_coherent_pool_P0prime_v1.md section 3.

The Stage-B discovery pool fired at the floor (all q_p > 0).  Before that can be
read even as an EXPLORATORY candidate, the prereg requires the NULL-vs-NULL gate:
replace the real char by a MN-mu6 replicate-as-pseudo-char and recompute q'_p;
its sign must be ~50/50, p ~ Uniform.  If it fires, the all-positive real pattern
is a FORCED construction bias of the pool -> VOID.

Mechanism: for each frequency the null draws R independent MN-mu6 relabels; the
char is the identity row.  For NULL-vs-NULL we draw (B + R) relabels per
frequency, designate B of them as pseudo-chars and R as the null, and form
q'_b = R*pseudochar_total_b - sum_r null_total_r  for each of the B pseudo-chars.
By exchangeability of the R+B iid relabel totals, sign(q'_b) must be ~50/50.
This CONFIRMS empirically (not by assertion) that q_p>0 for the real char is a
genuine char-vs-null effect, not an artifact of how the pool is built.

Exact integers throughout (N_LOW counts); the pre-existing FFT float is the
sanctioned carve-out.  check_no_float.py must pass.
"""
import argparse
import numpy as np
from row_budget_run_v1 import (load_freqs, mu6_orbits, Permuter, nlow_batch,
                               SPEC_N, SPEC_BETA)
from row_budget_core_v1 import curve_orbit


def nullnull_for_prime(p, freqs, R, B, rng):
    r = curve_orbit(p)
    X, Y, n = r
    assert n == SPEC_N[p]
    beta = SPEC_BETA[p]
    xb = beta * X[1] % p
    lam = int(np.nonzero((X == xb) & (Y == Y[1]))[0][0])
    reps6, orb6, unit6, pw6 = mu6_orbits(n, lam)
    P6 = Permuter(n, reps6, orb6, unit6, pw6)

    tab = np.exp(2j * np.pi * np.arange(p) / p)                # noqa: float (carve-out)
    F = freqs[p]

    pc_tot = [0] * B          # exact int pseudo-char totals
    null_tot = [0] * R        # exact int null totals
    for (b, c) in F:
        e = (b * X + c * Y) % p                                # exact integer exponent
        s = tab[e]; s[0] = 0.0                                 # noqa: float (carve-out)
        rows = [s[P6.draw(rng)] for _ in range(B + R)]         # all MN-mu6 relabels
        NL, _, _ = nlow_batch(np.array(rows), n)
        for i in range(B):
            pc_tot[i] += int(NL[i])
        for j in range(R):
            null_tot[j] += int(NL[B + j])

    null_sum = sum(null_tot)
    qs = [R * pc_tot[i] - null_sum for i in range(B)]          # exact int
    pos = sum(1 for q in qs if q > 0)
    neg = sum(1 for q in qs if q < 0)
    zero = B - pos - neg
    return dict(p=p, n=int(n), B=B, pos=pos, neg=neg, zero=zero)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", default="163,211,349")
    ap.add_argument("--R", type=int, default=64)
    ap.add_argument("--B", type=int, default=200)
    ap.add_argument("--seed", type=int, default=20260824)
    a = ap.parse_args()
    freqs, h = load_freqs()
    print(f"NULL-vs-NULL gate  freq sha {h[:16]}...  R={a.R} B={a.B} seed={a.seed}")
    rng = np.random.default_rng(a.seed)
    tot_pos = tot = 0
    for p in [int(t) for t in a.primes.split(",")]:
        o = nullnull_for_prime(p, freqs, a.R, a.B, rng)
        tot_pos += o["pos"]; tot += o["pos"] + o["neg"]
        print(f"  p={o['p']:>5} n={o['n']:>5}  pseudo-char q'>0: {o['pos']:>3}/"
              f"{o['B']}  (<0: {o['neg']}, =0: {o['zero']})")
    print(f"\n  pooled pseudo-char sign split: {tot_pos}/{tot} positive "
          f"(expect ~50%).  Real char was 10/10 positive.")
    # exact two-sided binomial-ish read via integer comparison: is it near half?
    lo = tot * 40 // 100
    hi = tot * 60 // 100
    ok = lo <= tot_pos <= hi
    print(f"  within [40%,60%] = [{lo},{hi}]? {'YES -> ~50/50, gate PASSES' if ok else 'NO -> forced bias, VOID'}")


if __name__ == "__main__":
    main()
