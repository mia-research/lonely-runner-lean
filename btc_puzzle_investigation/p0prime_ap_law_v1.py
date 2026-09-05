#!/usr/bin/env python3
"""
p0prime_ap_law_v1.py -- does the ~7% low-mode excess read out the Frobenius trace?

Pre-committed (motivated by the a_p=37 twin p=349,433 having matching excess):
  PRIMARY   : excess vs a_p            (signed trace of Frobenius, a_p = p+1-#E)
  EXPLORATORY (Holm m=3): excess vs |a_p|, vs a_p/(2 sqrt p) = cos(theta_ST)
Reported as Spearman rank correlation over all 21 primes (10 discovery + 11 S;
p=991 is in both -> an internal consistency check: same curve, two different
frozen freq-lists, excess should agree if it is a real curve invariant).

char_low is DETERMINISTIC, so for the S primes we only compute charTotal (no null
replicates) and recover nullTotal = R*charTotal - q_p from the frozen Stage-C q_p.
Discovery charTotal/nullTotal are the exact integers from the Stage-B run.

Exploratory characterization (a correlation over already-measured excesses); the
float stats are reported, not a threshold on keyed data.  Excess ratios are exact
Fractions; only the rank-correlation display is float.
"""
import argparse
from fractions import Fraction as Fr
import numpy as np
from row_budget_run_v1 import mu6_orbits, Permuter  # noqa (Permuter unused; parity w/ setup)
from row_budget_core_v1 import curve_orbit
from coherent_pool_p0prime_stageC_run_v1 import load_S

THRESH = 0.01   # noqa: float
R = 64

# discovery: (p, n, charTotal, nullTotal) exact ints from Stage-B log
DISC = [
    (163, 139, 3202, 190608), (211, 199, 7830, 460923),
    (349, 313, 33301, 1998196), (433, 397, 65289, 3915444),
    (577, 613, 169693, 10174198), (991, 1009, 170940, 10177892),
    (2089, 2143, 170656, 10180755), (4159, 4243, 171146, 10179120),
    (9319, 9127, 170493, 10180256), (19231, 19501, 170917, 10180601),
]
# S: q_p from Stage-C log (frozen firing run)
S_Q = {823: 729485, 907: 745488, 967: 698757, 991: 719495, 1051: 707778,
       1303: 712615, 1831: 716469, 2143: 708765, 2251: 708951, 2503: 698719,
       2647: 755466, 2731: 759433}


def char_total_S(p, n, F):
    X, Y, nn = curve_orbit(p); assert nn == n
    tab = np.exp(2j * np.pi * np.arange(p) / p)         # noqa: float
    tot = 0
    for (b, c) in F:
        e = (b * X + c * Y) % p
        s = tab[e]; s[0] = 0.0                           # noqa: float
        U2 = np.abs(np.fft.fft(s)) ** 2                  # noqa: float
        rho = U2 / (n - 1)                               # noqa: float
        tot += int((rho[1:] < THRESH).sum())
    return tot


def spearman(x, y):
    rx = np.argsort(np.argsort(x)); ry = np.argsort(np.argsort(y))
    return float(np.corrcoef(rx, ry)[0, 1])              # noqa: float


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--freqs", default="coherent_pool_p0prime_stageC_S_FREQS.txt")
    a = ap.parse_args()
    params, freqs, sha = load_S(a.freqs)
    print(f"a_p law test  S-freq sha {sha[:16]}...  R={R}\n")

    rows = []  # (p, n, a_p, excess_pct, tag)
    for p, n, ch, nu in DISC:
        exc = Fr(R * ch, nu) - 1
        rows.append((p, n, p + 1 - n, exc, "disc"))
    for p in sorted(S_Q):
        n, beta, lam = params[p]
        ch = char_total_S(p, n, freqs[p])
        nu = R * ch - S_Q[p]                             # nullTotal = R*char - q
        exc = Fr(R * ch, nu) - 1
        rows.append((p, n, p + 1 - n, exc, "S"))

    rows.sort(key=lambda r: (abs(r[2]), r[0]))
    print(f"  {'p':>6} {'n':>6} {'a_p':>5} {'|a_p|':>5} {'a_p/2√p':>8} {'excess%':>8}  set")
    for p, n, apv, exc, tag in rows:
        cos = apv / (2 * (p ** 0.5))                     # noqa: float (display)
        print(f"  {p:>6} {n:>6} {apv:>5} {abs(apv):>5} {cos:>+8.3f} "
              f"{float(exc)*100:>7.3f}%  {tag}")          # noqa: float (display)

    # 991 consistency check (in both sets)
    e991 = [float(r[3]) for r in rows if r[0] == 991]   # noqa: float
    print(f"\n  p=991 in BOTH sets (diff freq-lists): excess = "
          f"{[round(x*100,3) for x in e991]}%  (agreement => real curve invariant)")   # noqa: float

    P = np.array([r[0] for r in rows], dtype=float)      # noqa: float
    AP = np.array([r[2] for r in rows], dtype=float)     # noqa: float
    EX = np.array([float(r[3]) for r in rows])           # noqa: float
    COS = AP / (2 * np.sqrt(P))                          # noqa: float
    print("\n  Spearman rank correlations (n=21):")
    print(f"    PRIMARY   excess vs a_p        : {spearman(EX, AP):+.3f}")
    print(f"    exploratory excess vs |a_p|    : {spearman(EX, np.abs(AP)):+.3f}")
    print(f"    exploratory excess vs a_p/2√p  : {spearman(EX, COS):+.3f}")
    print(f"    confound  excess vs p          : {spearman(EX, P):+.3f}  (watch: p & a_p not independent)")
    print(f"    confound  excess vs |a_p| | small-p only (p<600): "
          f"{spearman(EX[P<600], np.abs(AP)[P<600]):+.3f}")


if __name__ == "__main__":
    main()
