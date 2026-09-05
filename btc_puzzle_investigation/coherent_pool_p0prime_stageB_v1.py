#!/usr/bin/env python3
"""
coherent_pool_p0prime_stageB_v1.py -- Stage B of PREREG_coherent_pool_P0prime_v1.md.

REAL-DATA discovery arm: compute the EXACT-INTEGER per-prime signed score
    q_p = R*charTotal_p - nullTotal_p          (in Z; sign(q_p) = sign(z_p))
on the 10 frozen discovery primes, then pool with coherent_pool_p0prime_v1's
exact sign-permutation p-value.  Discovery = may-be-SEEN => EXPLORATORY only
(characterization, never a named result; the FROZEN firing decision is A0 on the
held-out stratum S, which is Stage C and needs a reconstructed frozen freq-list).

Reuses the FROZEN null machinery from row_budget_run_v1 UNMODIFIED (load_freqs,
mu6_orbits, Permuter, nlow_batch, SPEC_*), but re-does the per-frequency
accumulation keeping tot as EXACT PYTHON INT -- because run_prime returns only
the float Nbar, and reconstructing q_p from a float would delete low bits
(btc CLAUDE.md NO-FLOAT).  N_LOW is an integer count, so every total here is int.

Only charTotal (real) and the mu6 null replicates are needed for q_p; neg/free
arms are not pooled and are skipped for speed.

EXACTNESS: q_p, s_p, W, and the p-value are int end to end.  The pre-existing
row-budget FFT float (|U|^2, the <THRESH count) is the sanctioned carve-out,
counted-not-keyed, identical to the frozen instrument.  Z=W/sqrt(k) is display.
"""
import argparse, time
import numpy as np
from row_budget_run_v1 import (load_freqs, mu6_orbits, Permuter, nlow_batch,
                               SPEC_N, SPEC_BETA, R_DEFAULT)
from row_budget_core_v1 import curve_orbit
from coherent_pool_p0prime_v1 import exact_pool_pvalue

DISCOVERY = [163, 211, 349, 433, 577, 991, 2089, 4159, 9319, 19231]


def q_for_prime(p, freqs, R, rng):
    """Exact-integer q_p = R*charTotal - nullTotal (mu6 arm), and sign diagnostics."""
    r = curve_orbit(p)
    assert r is not None, f"p={p} no prime-order curve"
    X, Y, n = r
    assert n == SPEC_N[p], f"n mismatch {n} vs {SPEC_N[p]}"
    beta = SPEC_BETA[p]
    assert pow(beta, 3, p) == 1 and beta != 1

    xb = beta * X[1] % p
    lam = int(np.nonzero((X == xb) & (Y == Y[1]))[0][0])
    idx = (lam * np.arange(n)) % n
    ceq = int(np.max((X[idx] - beta * X) % p))
    assert ceq == 0, f"C-EQ-int FAILED p={p}: {ceq}"

    reps6, orb6, unit6, pw6 = mu6_orbits(n, lam)
    P6 = Permuter(n, reps6, orb6, unit6, pw6)
    assert len(reps6) == (n - 1) // 6

    tab = np.exp(2j * np.pi * np.arange(p) / p)                 # noqa: float (carve-out)
    F = freqs[p]; m = len(F)

    char_total = 0          # exact int: sum_f N_LOW_char
    null_total = 0          # exact int: sum_f sum_{r=1..R} N_LOW_mu6(r)
    for (b, c) in F:
        e = (b * X + c * Y) % p                                 # exact integer exponent
        s = tab[e]; s[0] = 0.0                                  # noqa: float (carve-out)
        rows = [s] + [s[P6.draw(rng)] for _ in range(R)]
        NL, _, _ = nlow_batch(np.array(rows), n)                # integer counts
        char_total += int(NL[0])
        null_total += int(NL[1:1 + R].sum())

    q = R * char_total - null_total                            # exact int
    return dict(p=p, n=int(n), m=m, char_total=char_total, null_total=null_total,
                R=R, q=q, sign=(1 if q > 0 else -1 if q < 0 else 0))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", default=",".join(str(x) for x in DISCOVERY))
    ap.add_argument("--R", type=int, default=R_DEFAULT)
    ap.add_argument("--seed", type=int, default=20260823)
    a = ap.parse_args()
    primes = [int(t) for t in a.primes.split(",")]
    freqs, h = load_freqs()
    print(f"frozen freq-list sha256 {h[:24]}...  R={a.R}  seed={a.seed}")
    rng = np.random.default_rng(a.seed)

    rows = []
    for p in primes:
        t0 = time.time()
        o = q_for_prime(p, freqs, a.R, rng)
        o["secs"] = int(time.time() - t0)
        rows.append(o)
        print(f"  p={p:>6} n={o['n']:>6} m={o['m']:>6}  "
              f"charTot={o['char_total']:>10} nullTot={o['null_total']:>12}  "
              f"q={o['q']:>+13}  sign={o['sign']:+d}  [{o['secs']}s]")

    q = [o["q"] for o in rows]
    s = [1] * len(q)                                           # A0 monolithic
    num, den, W, k = exact_pool_pvalue(q, s)
    naligned = sum(1 for qp in q if qp > 0)
    print(f"\n=== EXPLORATORY discovery pool (A0 monolithic; NOT a named result) ===")
    print(f"  k(unforced) = {k}   aligned(+) = {naligned}/{len(q)}   W = {W:+d}")
    print(f"  exact sign-permutation p = {num}/{den}  "
          f"~ {num/den:.4g}" )                                 # noqa: float (display)
    # leave-one-out (drop largest |q_p|): verdict must persist (prereg section 5)
    if k >= 2:
        jmax = max(range(len(q)), key=lambda i: abs(q[i]))
        qloo = [q[i] for i in range(len(q)) if i != jmax]
        nl, dl, Wl, kl = exact_pool_pvalue(qloo, [1] * len(qloo))
        print(f"  leave-one-out (drop p={rows[jmax]['p']}, |q|={abs(q[jmax])}): "
              f"p = {nl}/{dl} ~ {nl/dl:.4g}")                   # noqa: float (display)
    print("\n  (discovery is EXPLORATORY; the frozen firing decision is A0 on the "
          "held-out stratum S = Stage C.)")


if __name__ == "__main__":
    main()
