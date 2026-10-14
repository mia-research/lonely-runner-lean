"""Exact core for the case-B covering study (spread in (9, 24]).

Every decision uses fractions.Fraction.  A reading s is CLEAR at R > 0 iff
(s*R) mod 8 lies in [1, 7]; a set is LONELY at R iff every reading is clear.
"""
from fractions import Fraction as F
from math import floor, ceil

EIGHT = F(8)


def frac_mod8(x):
    """x mod 8 as an exact Fraction in [0, 8)."""
    return x - 8 * (x.numerator // (8 * x.denominator))


def clear(s, R):
    r = frac_mod8(s * R)
    return 1 <= r <= 7


def lonely_at(readings, R):
    return all(clear(s, R) for s in readings)


def lap_of(s, R):
    """Lap index k with s*R in [8k+1, 8k+7], or None if blocked."""
    x = s * R
    k = x.numerator // (8 * x.denominator)
    r = x - 8 * k
    if r < 1:
        return None
    if r > 7:
        return None
    return k


def next_clear_start(s, R):
    """Least R' >= R at which s is clear (R itself if clear)."""
    x = s * R
    k = x.numerator // (8 * x.denominator)
    r = x - 8 * k
    if r < 1:
        return F(8 * k + 1) / s
    if r <= 7:
        return R
    return F(8 * k + 9) / s


def clear_end(s, R):
    """For s clear at R: right end of its current clear interval."""
    k = lap_of(s, R)
    assert k is not None
    return F(8 * k + 7) / s


def first_lonely(readings, R0=F(1), Rmax=None, max_steps=10**6):
    """Least R >= R0 at which the set is lonely (greedy escape iteration).

    Returns (R, steps) where steps counts the escape moves.  Exact: the
    lonely set is a finite union of closed intervals, each reading's clear
    set is a union of closed intervals, and R <- max_s next_clear_start(s, R)
    never passes a lonely point.
    """
    R = F(R0)
    steps = 0
    while True:
        nxt = max(next_clear_start(s, R) for s in readings)
        if nxt == R:
            return R, steps
        R = nxt
        steps += 1
        if Rmax is not None and R > Rmax:
            return None, steps
        if steps > max_steps:
            raise RuntimeError("no convergence")


def normalise(ds):
    ds = sorted(ds)
    m = ds[0]
    return [F(d, 1) / m for d in ds]


def largest_gap(readings):
    """(index i, ratio g) of the largest consecutive ratio s_{i+1}/s_i.
    Ties broken towards the lowest index."""
    best = None
    for i in range(len(readings) - 1):
        g = readings[i + 1] / readings[i]
        if best is None or g > best[1]:
            best = (i, g)
    return best
