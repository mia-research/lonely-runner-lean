"""twin3_window.py -- the window engine.

Safe(E) = union over base windows W_V of  W_V \\ ( A(e', J_V)  u  B_m ),
where  J_V = { j in Z/8 : V subset of bad(rho', j) }.

This is an identity, not an approximation: the five base runners are constant on
W_V, the twin kills W_V-points exactly on A(e',J_V), and 8m kills exactly B_m.
`check_identity` verifies it against the brute-force cell decomposition.
"""
from fractions import Fraction as F
from twin3_core import (uncovered_cells, measure, bad, FULL, A_intervals,
                        B_intervals, subtract, merge, total, J_set)

def base_windows(rho0):
    return [(a,b,V) for a,b,V in uncovered_cells([1,3,5,7,rho0]) if V]

_BW = {r: base_windows(r) for r in (2,4,6)}

def safe_intervals(rho0, rho2, q, m):
    e2 = 8*q + rho2
    Bm = B_intervals(m)
    out = []
    for a,b,V in _BW[rho0]:
        J = J_set(rho2, V)
        kill = merge(A_intervals(e2, J) + Bm)
        out.extend(subtract([(a,b)], kill))
    return merge(out)

def safe_measure(rho0, rho2, q, m):
    return total(safe_intervals(rho0, rho2, q, m))

def check_identity(rho0, rho2, q, m):
    e2 = 8*q+rho2
    E = sorted({1,3,5,7,rho0,e2,8*m})
    if len(E)!=7: return None
    brute = measure(uncovered_cells(E))
    fast  = safe_measure(rho0,rho2,q,m)
    return brute, fast, brute==fast
