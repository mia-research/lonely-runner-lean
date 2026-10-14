"""twin3_core.py -- exact rational core for the n=8 UNIT-COMPLETE twin case.

Everything here is Fraction / int arithmetic.  No floats enter any decision.

Objects
-------
bad(e,t)      : subset of Z/8 killed by runner e when floor(e x) = t
U_base(rho0)  : the exact interval decomposition of the uncovered set of the
                five base runners {1,3,5,7,rho0} (representative speeds)
A(c,K)        : {x in [0,1) : floor(c x) mod 8 in K}, as exact intervals
B(m)          : {x : ||m x|| < 1/8}, as exact intervals
"""
from fractions import Fraction as F

FULL = frozenset(range(8))

def bad(e, t):
    return frozenset(r for r in range(8) if (e * r + t) % 8 in (0, 7))

def breakpoints(speeds):
    pts = {F(0), F(1)}
    for e in speeds:
        for j in range(1, e + 1):
            q = F(j, e)
            if 0 < q < 1:
                pts.add(q)
    return sorted(pts)

def uncovered_cells(speeds):
    """Return list of (a, b, U) with U = Z/8 minus union of bad, constant on [a,b)."""
    p = breakpoints(speeds)
    out = []
    for a, b in zip(p, p[1:]):
        x = (a + b) / 2
        cov = set()
        for e in speeds:
            cov |= bad(e, int(e * x))          # int() of a Fraction floors for x>0
        out.append((a, b, frozenset(FULL - cov)))
    # merge adjacent cells with equal U
    merged = []
    for a, b, U in out:
        if merged and merged[-1][2] == U and merged[-1][1] == a:
            merged[-1] = (merged[-1][0], b, U)
        else:
            merged.append((a, b, U))
    return merged

def measure(cells):
    return sum(b - a for a, b, U in cells if U)

def A_intervals(c, K):
    """{x in [0,1): floor(c x) mod 8 in K} as a sorted list of [a,b) with a,b rational."""
    out = []
    for t in range(c):
        if t % 8 in K:
            out.append((F(t, c), F(t + 1, c)))
    return merge(out)

def B_intervals(m):
    """{x in [0,1) : ||m x|| < 1/8}: length 1/(4m) centred at j/m, wrapped."""
    out = []
    for j in range(m + 1):
        a = F(j, m) - F(1, 8 * m)
        b = F(j, m) + F(1, 8 * m)
        a = max(a, F(0)); b = min(b, F(1))
        if a < b:
            out.append((a, b))
    return merge(out)

def merge(iv):
    iv = sorted(iv)
    out = []
    for a, b in iv:
        if out and a <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], b))
        else:
            out.append((a, b))
    return out

def total(iv):
    return sum(b - a for a, b in iv)

def subtract(base, kill):
    """base, kill: lists of half-open intervals. Return base \\ kill."""
    kill = merge(kill)
    out = []
    for a, b in base:
        cur = [(a, b)]
        for ka, kb in kill:
            nxt = []
            for ca, cb in cur:
                if kb <= ca or ka >= cb:
                    nxt.append((ca, cb)); continue
                if ca < ka:
                    nxt.append((ca, min(cb, ka)))
                if kb < cb:
                    nxt.append((max(ca, kb), cb))
            cur = nxt
        out.extend(cur)
    return [(a, b) for a, b in out if a < b]

def J_set(rho, V):
    """{ j in Z/8 : V subset of bad(rho, j) }  -- the twin residues that kill V."""
    return frozenset(j for j in range(8) if V <= bad(rho, j))
