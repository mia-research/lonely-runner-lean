#!/usr/bin/env python3
"""Lonely intervals of a tuple, with the speed pair defining each endpoint.

Endpoints are a=(m+1/(k+1))/v_i and b=(m'-1/(k+1))/v_j, so
    b - a = [ (k+1)(v_i m' - v_j m) - (v_i + v_j) ] / [ (k+1) v_i v_j ]
with integer numerator >= 1.  Hence width >= 1/((k+1) v_i v_j), and since the grid
{j/N}, N=(k+1)p, must hit any interval of width >= 1/N, the tuple is DEAD once
p >= v_i v_j.  So  kill(T) := min over lonely intervals of v_i*v_j  is the p beyond
which T can no longer obstruct."""
from fractions import Fraction as F

def lonely_intervals(T, k):
    b = F(1, k+1)
    pts = {F(0), F(1,2)}
    src = {}
    for v in T:
        m = 0
        while F(m-1)/v <= F(1,2)+1:
            for e in (F(m)-b, F(m)+b):
                x = e/v
                if 0 <= x <= F(1,2):
                    pts.add(x); src.setdefault(x, set()).add(v)
            m += 1
            if m > 40: break
    pts = sorted(pts)
    def ok(x): return all(min((x*v) % 1, 1-(x*v) % 1) >= b for v in T)
    out = []
    for a, c in zip(pts, pts[1:]):
        if ok((a+c)/2):
            vi = min(src.get(a, {max(T)}))
            vj = min(src.get(c, {max(T)}))
            out.append((a, c, c-a, vi, vj, vi*vj))
    return out

def kill_threshold(T, k):
    iv = lonely_intervals(T, k)
    return min((p for *_, p in iv), default=None), iv
