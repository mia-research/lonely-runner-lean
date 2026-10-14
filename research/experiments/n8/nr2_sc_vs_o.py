r"""
nr2_sc_vs_o  --  how |S^c| compares with o = |O| (four unit runners cover all odds).

Motivation.  The PARITY REDUCTION plus the reflection x -> 1-x (which maps O to V and
swaps the two halves of the rho0 partition) gives, in the limit of large e_rho0,
|S^c| -> o.  This script measures the finite-e_rho0 excess

        exc  =  |S^c| - o

exactly, over a sweep, and reports where it is largest.  A uniform bound
exc <= 1/2 - max(o) would close the leaf.

Usage:  python3 nr2_sc_vs_o.py QMAX
"""
import itertools, sys
from math import gcd
from fractions import Fraction as F
from nr2_core import safe_measure, o_measure, u_measure

QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6
rows = []
for rho0 in (2, 4, 6):
    rhos = (1, 3, 5, 7, rho0)
    worst_exc = None
    worst_sc = None
    n = 0
    n_exceed = 0
    for qs in itertools.product(range(QMAX + 1), repeat=5):
        sp = tuple(8 * q + r for q, r in zip(qs, rhos))
        if len(set(sp)) != 5:
            continue
        g = 0
        for e in sp:
            g = gcd(g, e)
        if g != 1:
            continue                      # non-primitive: closed by the Reduction
        n += 1
        S = safe_measure(sp, rhos)
        sc = 1 - S
        o = o_measure(sp[:4])
        exc = sc - o
        if exc > 0:
            n_exceed += 1
        if worst_exc is None or exc > worst_exc[0]:
            worst_exc = (exc, sp, sc, o)
        if worst_sc is None or sc > worst_sc[0]:
            worst_sc = (sc, sp, o)
    print(f"rho0={rho0}  q<= {QMAX}  primitive tuples = {n}")
    print(f"   max |S^c| = {worst_sc[0]} = {float(worst_sc[0]):.6f} at {worst_sc[1]}  (o = {worst_sc[2]})")
    print(f"   tuples with |S^c| > o : {n_exceed}")
    print(f"   max excess |S^c| - o = {worst_exc[0]} = {float(worst_exc[0]):.6f}"
          f" at {worst_exc[1]}  (|S^c|={worst_exc[2]}, o={worst_exc[3]})")
    sys.stdout.flush()
