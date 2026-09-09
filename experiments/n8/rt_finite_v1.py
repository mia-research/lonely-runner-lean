r"""
rt_finite_v1 -- the FINITE side of the reduction in reports/n8_o_rate.md.

Theorem 4(a): if the resonances of sup-norm height <= R already span a rank-3 lattice,
then e is proportional to the vector of 3x3 minors of three of them, so by Hadamard

        max_rho e_rho  <=  3 sqrt(3) R^3        ( = 41.6 at R=2, 140.3 at R=3 ).

So every tuple NOT covered by the tail bound at height R lives in a finite box.  This
script checks that box exhaustively, in exact arithmetic, and reports the required
near-miss profile and boundary audit.

usage:  python3 rt_finite_v1.py [SMAX]
"""
import sys, itertools
from fractions import Fraction as F
from math import gcd, lcm
from functools import reduce

from ob_fast_v1 import o_fast, audit
from ob_core_v1 import o_x

RHO = (1, 3, 5, 7)
THIRD = F(1, 3)
EXC = {(1, 3, 5, 7), (1, 11, 5, 7)}
DELTAS = [F(0), F(1, 100), F(1, 50), F(1, 30), F(1, 20), F(1, 12)]
SMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 200


def guard(e):
    D = 4 * reduce(lcm, e)
    return max(4 * x for x in e) * D < 2 ** 63


def gen(smax):
    Qs = [range((smax - r) // 8 + 1) for r in RHO]
    for qs in itertools.product(*Qs):
        e = tuple(8 * q + r for q, r in zip(qs, RHO))
        if len(set(e)) != 4:
            continue
        if reduce(gcd, e) != 1:
            continue
        yield e


if __name__ == "__main__":
    print(f"rt_finite_v1: EXHAUSTIVE over primitive unit 4-tuples with max speed <= {SMAX}")
    print("Hadamard box: R=2 needs <= 41, R=3 needs <= 140, R=4 needs <= 332")
    n = 0
    over = []
    best = []
    tripped = 0
    for e in gen(SMAX):
        n += 1
        if not guard(e):
            tripped += 1
            continue
        o = o_fast(e)
        p, q = o.numerator, o.denominator
        assert (3 * p > q) == (o > THIRD)
        if o > THIRD and e not in EXC:
            over.append((o, e))
        best.append((o, e))
        if n % 100000 == 0:
            print(f"   ... {n} tuples", flush=True)
    best.sort(reverse=True)
    print(f"\n  primitive unit 4-tuples with max speed <= {SMAX}: {n}")
    print(f"  overflow-guard trips: {tripped}")
    print(f"  N_exc (o > 1/3 outside the two known exceptions): {len(over)}")
    for o, e in over:
        print(f"     *** {e}  o = {o} = {float(o):.8f}")
    print(f"\n  top 15 by o:")
    for o, e in best[:15]:
        print(f"     {str(e):>22}  o = {str(o):>20} = {float(o):.8f}"
              f"{'   (known exception)' if e in EXC else ''}")
    print(f"\n  near-miss counts #{{o >= 1/3 - d}} for "
          f"d = 0, 1/100, 1/50, 1/30, 1/20, 1/12:")
    print("     ", [sum(1 for o, e in best if o >= THIRD - d) for d in DELTAS])
    print("\n  boundary audit (cells, interior breakpoints, entry != exit) on the top 20:")
    bad = 0
    for o, e in best[:20]:
        c, ni, nm = audit(e)
        bad += (ni != 0) + (nm != 0)
        if ni or nm:
            print(f"     FAILURE {e}: {(c, ni, nm)}")
    print(f"     failures: {bad}")
    print("\n  independent re-verification by ob_core_v1.o_x on the top 10:")
    ok = sum(1 for o, e in best[:10] if o_x(e) == o)
    print(f"     {ok} of 10 agree exactly")
