"""Shared exact routines for the redo (2026-09-25).  Frame rule, MANUSCRIPT_v21 section 1.1: the object
is an ARRANGEMENT of 8 distinct positive speeds (none zero); every runner is evaluated in its own
readings v_j - v_i; nothing is pinned.  AP / grid / mod 8 are read on the arrangement's reduced speeds
(section 4: reduce by g = gcd of differences; global isolation iff the reduced speeds form a complete
residue system mod 8).  All arithmetic exact (Fraction); the band test is closed at 1/8 (BSM rule).
"""
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce

def nd(x):
    x = x % 1
    return min(x, 1 - x)

def readings(V, k):
    """runner k's own readings: the distinct |v_j - v_k|, j != k"""
    return sorted({abs(v - V[k]) for j, v in enumerate(V) if j != k})

def cascade(ds):
    """the cascade map from the bound 1/(8 d_min): move to the largest next opening of the runners in
    the way; its fixed point is the isolation event.  Returns (instant, moves)."""
    t = F(1, 8 * min(ds)); moves = 0
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way:
            return t, moves
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way)
        moves += 1

def g_of(V):
    return reduce(gcd, [abs(a - b) for a in V for b in V if a != b])

def reduced_residues(V):
    """the arrangement's reduced speeds mod 8, relative to its slowest runner (a common shift changes no difference)"""
    g = g_of(V); m = min(V)
    return sorted(((v - m) // g) % 8 for v in V)

def is_grid(V):
    return len(set(reduced_residues(V))) == 8

def tier(V, k):
    """which tier clears runner k first, on the arrangement's own scales: AP at g, grid at d_min(k), else enlarged"""
    ds = readings(V, k); g = g_of(V); dmin = min(ds)
    def clears(D):
        return any(all(nd(d * F(p, 8 * D)) >= F(1, 8) for d in ds) for p in (1, 3, 5, 7))
    if clears(g): return "AP"
    if clears(dmin): return "grid"
    return "enlarged"
