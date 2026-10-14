"""ok_dmin_rule_test_v1 -- does the d_min rule survive three movers and a non-AP base?

The rule under test (from TWO_MOVER_PREDICTION_v1 sec 4, exact on 42,092 two-mover
cases): a runner's first isolation is at

        t*  =  1 / (8 * d_min)

where d_min is that runner's smallest speed difference to any other runner.

The BOUND t* >= 1/(8*d_min) is forced for every runner and every configuration:
the runner starts at gap 0 from its nearest neighbour and needs ||d_min * t|| >= 1/8.
What is at issue is ATTAINMENT.

Two things the two-mover result leaned on, both true of the AP and neither true in
general: every runner has d_min = 1, and the base is a grid.  This tests both.
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from ok_full_transit_sweep_v1 import runner_row

def dmin(V, i):
    return min(abs(V[i] - V[j]) for j in range(len(V)) if j != i)

def check(V):
    """Per runner: does the moment attain 1/(8*d_min)?"""
    out = []
    for i in range(8):
        r = runner_row(V, i)
        if not r["windows"]: out.append(None); continue
        t = r["windows"][0][0]
        d = dmin(V, i)
        out.append((t == F(1, 8) / d, t, F(1, 8) / d, d))
    return out

def frange(lo, hi, step):
    v, out = F(lo) + step, []
    while v < F(hi):
        if v > 0: out.append(v)
        v += step
    return out
