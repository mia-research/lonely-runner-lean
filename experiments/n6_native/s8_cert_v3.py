#!/usr/bin/env python3
"""Exact cell certificate for §8, v3: as v2, with the window statements tested in window_two's own form (base and
residue conditions, as `block3_window_laps` / `lonely_of_window` use), made exact over a cell:
  base: 1/(3 a_lo) + 1/(3 b_lo) <= l_min;  residue: every integer m >= 0 with m < 1/3 + b_hi/(3 a_lo) has
  (m + 1/3)/b_lo <= l_min;  l_min = min_i (m_i + 5/6)/hi_i - max_i (m_i + 1/6)/lo_i,  a = x4, b = x5.
(For the unbounded x5 cell the residue set is infinite; there the closed form 1/(3a) + 2/(3b) is used, which implies it.)
Usage: X depth."""
import sys, math
from fractions import Fraction as F
from collections import Counter
src = open("s8_cert_v2.py").read()
exec(src.split("start_cells = []")[0])
def ok_w3(c, m):
    U = min(F(6 * m[i] + 5, 6) / hi(c, i) for i in range(3)); L = max(F(6 * m[i] + 1, 6) / lo(c, i) for i in range(3))
    l = U - L
    a_lo, a_hi = c[2]; b_lo, b_hi = c[3]
    if b_hi is None: return l >= F(1, 3) / a_lo + F(2, 3) / b_lo
    if l < F(1, 3) / a_lo + F(1, 3) / b_lo: return False
    mmax = math.ceil(F(1, 3) + b_hi / (3 * a_lo))
    return all(F(3 * mm + 1, 3) / b_lo <= l for mm in range(0, mmax + 1) if mm < F(1, 3) + b_hi / (3 * a_lo))
exec("start_cells = []" + src.split("start_cells = []")[1])
