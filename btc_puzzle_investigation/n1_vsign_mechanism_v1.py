#!/usr/bin/env python3
"""
n1_vsign_mechanism_v1.py -- WHAT IS GOING ON at the v > 0 classes.

The counterexamples (RESULT_n1_v_sign_route_refuted_v1.md) settle that `v <= 0` is false.
They explain nothing.  This script characterizes the exceptional set.

The framing question: v = (product of the two half-traces).  If the two Frobenius angles were
independent, sign(v) would be a coin flip and ~50% of classes would have v > 0.  Measured: ~5%.
So something SUPPRESSES v > 0 hard, and the exceptional classes are where that mechanism weakens.
Naming the mechanism is the object here.

Per class (mu6-coset rep c), with e1 = -V1 and e2 = (V1^2+V2)/2:

  SIN (p=3 mod 4):  pairs multiply to -p ;  half-trace s_i = sin(theta_i)
                    e1 = 2i sqrt(p) u,  u = s1+s2 ;  e2 = -2p - 4p v,  v = s1 s2
  COS (p=1 mod 4):  pairs multiply to +p ;  half-trace c_i = cos(theta_i)
                    e1 = 2 sqrt(p) u,   u = c1+c2 ;  e2 = +2p + 4p v,  v = c1 c2

Forced (Weil, weight 1): |u| <= 2, u^2 >= 4v, |u| <= 1+v.  v > 0 forces the two half-traces to
share a sign, hence |u| = |s1|+|s2| >= 2 sqrt(v).  So a v > 0 class MUST carry an atypically
large |u|.  That is the hypothesis this script tests.

EXACTNESS.  The v > 0 COUNT is exact and float-free elsewhere (n1_vsign_decide_v1.py, Descartes with
a total-reality self-certificate).  Nothing here decides a verdict; this is CHARACTERIZATION, computed
from exact integer coefficient vectors at 60 decimal digits via mpmath.  Every number below is
descriptive.
"""
import sys
from mpmath import mp, mpf, cos, sin, sqrt, mpc, exp, pi

mp.dps = 60

sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from audit_n1_vsign_v2_core import is_prime, curve_order, dlog_table, hist_k1, hist_k2
from n1_forced_identity_v1 import mulF, red
from n1_vsign_decide_v1 import coset_reps

B = 7


def eval_vec(A, c, n):
    """evaluate sum_i A_i zeta_n^{i c} at 60 dps."""
    tot = mpc(0)
    for i, ai in enumerate(A):
        if ai:
            ang = 2 * pi * ((i * c) % n) / n
            tot += ai * mpc(cos(ang), sin(ang))
    return tot


def analyse(p):
    n = curve_order(p, B)
    assert is_prime(n)
    sin_str = (p % 4 == 3)
    dl = dlog_table(p, n, B)
    V1 = red(hist_k1(p, n, dl, B), n)
    V2 = red(hist_k2(p, n, dl, B), n)
    W = [a + b for a, b in zip(mulF(V1, V1, n), V2)]
    e2v = [x // 2 for x in W]
    reps, _ = coset_reps(n)
    rp = sqrt(mpf(p))

    rows = []
    for c in reps:
        e1 = -eval_vec(V1, c, n)
        e2 = eval_vec(e2v, c, n)
        if sin_str:
            u = (e1 / (2j * rp)).real          # e1 is purely imaginary here
            v = -(e2.real + 2 * p) / (4 * p)
        else:
            u = (e1 / (2 * rp)).real
            v = (e2.real - 2 * p) / (4 * p)
        rows.append((c, u, v))
    return p, n, sin_str, rows


def report(p):
    p, n, sin_str, rows = analyse(p)
    d = len(rows)
    pos = [r for r in rows if r[2] > 0]
    neg = [r for r in rows if r[2] <= 0]
    au = lambda rs: (sum(abs(r[1]) for r in rs) / len(rs)) if rs else mpf('nan')
    mx = lambda rs, f: max((f(r) for r in rs), default=mpf('nan'))

    print(f"p={p:>5}  n={n:<5} d={d:<4} {'SIN' if sin_str else 'COS'}   "
          f"v>0 : {len(pos):>2}/{d}  ({100.0*len(pos)/d:.1f}%)")
    print(f"        mean|u|  all {float(au(rows)):.4f}   v<=0 {float(au(neg)):.4f}   "
          f"v>0 {float(au(pos)):.4f}"
          + (f"   RATIO {float(au(pos)/au(neg)):.2f}x" if neg and pos else ""))
    print(f"        max |u| overall {float(mx(rows, lambda r: abs(r[1]))):.4f}   "
          f"max v {float(mx(rows, lambda r: r[2])):+.4f}   "
          f"min v {float(min(r[2] for r in rows)):+.4f}")
    # is every v>0 class among the largest |u| ?
    order = sorted(rows, key=lambda r: -abs(r[1]))
    ranks = [order.index(r) + 1 for r in pos]
    if pos:
        print(f"        |u|-rank of the v>0 classes (1 = largest |u| of {d}): {sorted(ranks)}")
        print(f"        min |u| among v>0 : {float(min(abs(r[1]) for r in pos)):.4f}   "
              f"vs 2*sqrt(v) bound {float(max(2*sqrt(r[2]) for r in pos)):.4f}")
    # the forced inequalities, as a sanity check on the characterization arithmetic
    bad = [r for r in rows if not (r[1] ** 2 >= 4 * r[2] - mpf('1e-40')
                                   and abs(r[1]) <= 1 + r[2] + mpf('1e-40'))]
    print(f"        forced u^2>=4v and |u|<=1+v hold at {d - len(bad)}/{d} classes")
    return rows, pos, neg, sin_str


if __name__ == "__main__":
    allpos, allneg = [], []
    for p in [int(t) for t in sys.argv[1:]]:
        rows, pos, neg, s = report(p)
        allpos += [r[1] for r in pos]
        allneg += [r[1] for r in neg]
        print()
    if allpos:
        mp_ = sum(abs(x) for x in allpos) / len(allpos)
        mn_ = sum(abs(x) for x in allneg) / len(allneg)
        print("=" * 70)
        print(f"POOLED over all primes:  mean|u| at v>0 classes = {float(mp_):.4f}   "
              f"at v<=0 classes = {float(mn_):.4f}   ratio {float(mp_/mn_):.2f}x")
        print(f"  n(v>0) = {len(allpos)}   n(v<=0) = {len(allneg)}")
