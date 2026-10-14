"""Step 5 read as an assignment of laps -- entry and exit, no complement taken.

Runner j on lap n_j reads mid-lap from its ENTRY  E_j = (n_j + 1/8)/d_j
                                 to its EXIT   X_j = (n_j + 7/8)/d_j.

    the moment exists  <=>  some assignment (n_1..n_7) has  max_j E_j <= min_j X_j.

The runner with d = d_min on lap 0 IS the window, so the window needs no separate test.
Named assignments:
    n == 0                       every runner still on its first lap
    n_j = lap at the reference,  the phase rounded into mid-lap
"""
from fractions import Fraction as F

def entry_exit(ds, ns):
    lo = max(F(8*n + 1, 8*d) for n, d in zip(ns, ds))
    hi = min(F(8*n + 7, 8*d) for n, d in zip(ns, ds))
    return (lo, hi) if lo <= hi else None

def first_lap(ds):
    return [0]*len(ds)

def reference_assignment(ds):
    """Lap counts at the reference instant t = 1/(8 d_min), phase rounded into mid-lap."""
    m = min(ds); ns = []
    for d in ds:
        x = F(d, 8*m)
        n = x.numerator // x.denominator
        if x - n > F(7, 8):
            n += 1
        ns.append(n)
    return ns
