#!/usr/bin/env python3
"""
formal_log_order2_shadow_v1.py -- the SECOND-ORDER formal-group shadow probe.

PROPOSAL UNDER TEST (external note, 2026-07-19):
  step 1  R^(1)_d = x_d / y_d
  step 2  R^(2)_d = (x_d/y_d) * (1 + 3 x_d^6 / (x_d^3+7)^3)
  "If step 1 leaks 0.40 and step 2 pushes it to 0.60+, the formal group logarithm is the
   exact mechanism of the leak -- an escalating polynomial path toward the discrete log."

EXACT ALGEBRA FIRST (formal_group_note_algebra_v1.py, C1; re-asserted as control X0 below):
  y^2 = x^3+7  =>  (x^3+7)^3 = y^6  =>  3x^6/(x^3+7)^3 = 3T^6  with T = -x/y.
  Hence  R^(2) = T + 3T^7 = f(R^(1))  EXACTLY over F_p: a POLYNOMIAL IN R^(1) ALONE.
  CONSEQUENCE, PROVED: sigma(R^(2)) subseteq sigma(R^(1)), so by the data-processing
  inequality NO information measure of d given the readout can rise from step 1 to step 2.
  NOT covered by that argument: a specific CORRELATION statistic. A nonlinear reweighting
  of a readout CAN raise a correlation with a fixed character. That is what this script
  measures. This is the reading under which the proposal is not already decided.

STATISTIC (identical to formal_log_xovery_readout_v1, so the numbers are comparable):
    Corr_F(a) = (1/n) sum_d F(P_d) e_n(-a d) ;  C(F) = max_{a!=0}|Corr_F(a)| / ||F||_2
    reported as C/floor with floor = sqrt(ln n / n)  (the generic max-over-a scale).
  On-record scale: cheap readouts 1.05-1.4 ; planted aligned control 6.10 -> 18.04 (p 211->2503).

ARMS (each as raw-integer value AND as additive character e_p(.), since the note does not say):
    L1 = T                              (order 1; on record, 1.06-1.33 raw)
    L2 = T + 3T^7                       (order 2; THE PROPOSAL)
    L3 = T + 3T^7 + (735/13) T^13       (order 3; the term the note says "shatters" the signal)
    L4 = L3 + (28812/19) T^19           (order 4; is there any monotone trend at all?)
  Ratio-normalized variants L_k(P_d)/L_k(G) are also reported: that is the form in which the
  note's "d ~ L(P_d)/L(G)" reading is meant.

CONTROLS (must fire, else the run is uninformative):
    X0  identity check   R^(2) == T+3T^7 pointwise, exactly           -> deviation must be 0
    X1  PLANTED aligned  F = e_n(a0 d)                                -> must grow with p
    X2  matched null     same values, d->P_d assignment shuffled      -> ~1.0
    X3  reference cheap  e_p(x*y) (best cheap on record)              -> ~1.3

PRE-COMMITTED DECISION RULE (see PREREG_formal_group_shadow_order2_v1.md):
  The note's claim is an ESCALATION: C(L2) materially above C(L1). Counting a rise requires
  L2 > L1 in the SAME direction on a majority of primes AND L2 above the shuffled null's
  spread. A single-prime excursion is not a rise. Absence of a rise is reported as a bounded
  magnitude with its power and scope -- NOT as a closure of the formal-group avenue.

SCOPE: enumerable p (<= ~3000). Zero power at p ~ 2^256. Says nothing about readouts outside
  this truncation family, nor about the aligned (DLP-requiring) joint readout.

FLOAT CARVE-OUT: signal path (curve, T, truncations) is exact modular integer arithmetic.
Float only in the character-sum magnitudes -- the analytic-size carve-out named in
btc_puzzle_investigation/CLAUDE.md -- never as a threshold on data.
"""
import cmath
import math
import sys

from sympy import isprime

from formal_log_xovery_readout_v1 import curve_points_in_order, corr_over_floor

B = 7
# formal-group log coefficients: L(T) = sum_k 7^k C(3k,k)/(6k+1) T^(6k+1)
# k=0:1/1 ; k=1: 7*3/7=3 ; k=2: 49*15/13=735/13 ; k=3: 343*84/19=28812/19
COEFFS = [(1, 1, 1), (3, 1, 7), (735, 13, 13), (28812, 19, 19)]   # (num, den, exponent)


def truncations(T, p, order):
    """L_order(T) mod p, exact modular arithmetic (den is a unit mod p)."""
    s = 0
    for num, den, e in COEFFS[:order]:
        s = (s + num * pow(den, -1, p) * pow(T, e, p)) % p
    return s


def run(p):
    got = curve_points_in_order(p)
    if got is None:
        return None
    G, pts, n = got
    if not isprime(n):
        return None
    ep = lambda t: cmath.exp(2j * math.pi * (t % p) / p)
    inv = lambda t: pow(t, p - 2, p)

    T = [(-x * inv(y)) % p for (x, y) in pts]

    # ---- X0: the exact-algebra control, on THIS curve, in the note's own written form ----
    dev = 0
    for (x, y), t in zip(pts, T):
        lhs = t * (1 + 3 * pow(x, 6, p) * pow((pow(x, 3, p) + B) % p, -3, p)) % p
        rhs = (t + 3 * pow(t, 7, p)) % p
        dev = max(dev, (lhs - rhs) % p)

    out = {'p': p, 'n': n, 'X0_dev': dev}
    for order in (1, 2, 3, 4):
        L = [truncations(t, p, order) for t in T]
        LG = truncations((-G[0] * inv(G[1])) % p, p, order)
        out[f'L{order}_raw'] = corr_over_floor([complex(v) for v in L], n)
        out[f'L{order}_ep'] = corr_over_floor([ep(v) for v in L], n)
        if LG % p != 0:
            Rn = [v * inv(LG) % p for v in L]
            out[f'L{order}_ratio'] = corr_over_floor([complex(v) for v in Rn], n)
        else:
            out[f'L{order}_ratio'] = float('nan')

    # ---- controls ----
    out['X1_PLANTED'] = corr_over_floor(
        [cmath.exp(2j * math.pi * d / n) for d in range(1, n)], n)
    out['X3_ep_xy'] = corr_over_floor([ep(x * y % p) for (x, y) in pts], n)
    import random
    rng = random.Random(20260719 + p)
    sh = [ep(v) for v in [truncations(t, p, 2) for t in T]]
    rng.shuffle(sh)
    out['X2_shuf'] = corr_over_floor(sh, n)
    return out


def main():
    ps = [int(a) for a in sys.argv[1:]] or [211, 433, 733, 1051, 1669, 2503]
    print("C/floor -- cheap readouts sit ~1.0-1.5 ; X1 planted control must grow with p")
    print("L1=T  L2=T+3T^7 (THE PROPOSAL)  L3=+735/13 T^13  L4=+28812/19 T^19")
    hdr = (f"{'p':>6} {'n':>6} {'X0':>3} | {'L1raw':>6} {'L2raw':>6} {'L3raw':>6} {'L4raw':>6} | "
           f"{'L1ep':>6} {'L2ep':>6} {'L3ep':>6} {'L4ep':>6} | {'L2rat':>6} | "
           f"{'X1plant':>7} {'X2shuf':>6} {'X3xy':>5}")
    print(hdr)
    rows = []
    for p in ps:
        if p % 6 != 1 or not isprime(p):
            continue
        r = run(p)
        if r is None:
            print(f"{p:>6}   -- n composite / no generator")
            continue
        rows.append(r)
        print(f"{r['p']:>6} {r['n']:>6} {r['X0_dev']:>3} | "
              f"{r['L1_raw']:>6.3f} {r['L2_raw']:>6.3f} {r['L3_raw']:>6.3f} {r['L4_raw']:>6.3f} | "
              f"{r['L1_ep']:>6.3f} {r['L2_ep']:>6.3f} {r['L3_ep']:>6.3f} {r['L4_ep']:>6.3f} | "
              f"{r['L2_ratio']:>6.3f} | "
              f"{r['X1_PLANTED']:>7.2f} {r['X2_shuf']:>6.3f} {r['X3_ep_xy']:>5.2f}")

    if rows:
        print("\n--- pre-committed decision rule: does L2 rise above L1? ---")
        for tag in ('raw', 'ep', 'ratio'):
            up = sum(1 for r in rows if r[f'L2_{tag}'] > r[f'L1_{tag}'])
            d = [r[f'L2_{tag}'] - r[f'L1_{tag}'] for r in rows]
            mu = sum(d) / len(d)
            sd = math.sqrt(sum((z - mu) ** 2 for z in d) / max(1, len(d) - 1))
            print(f"  {tag:>5}: L2>L1 on {up}/{len(rows)} primes;  mean delta {mu:+.3f} "
                  f"(sd {sd:.3f});  mean L1 {sum(r[f'L1_{tag}'] for r in rows)/len(rows):.3f} "
                  f"-> mean L2 {sum(r[f'L2_{tag}'] for r in rows)/len(rows):.3f}")
        print(f"  X0 max deviation over all primes: {max(r['X0_dev'] for r in rows)} "
              f"(must be 0: R^(2) IS T+3T^7)")


if __name__ == '__main__':
    main()
