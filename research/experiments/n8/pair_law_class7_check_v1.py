"""Exact check of the class-7 exception to the record's pair-law interval (Fresh/PairLaw.lean, cxD).  Fractions only.
c = 1, d_1 = 1 - r, d_2 = 2 + r, d_j = j otherwise (j = 3..7); hypothesis |d_j - j| <= r.  Class a = 7 (mirror 1)."""
from fractions import Fraction as F
from math import floor
def clear(d, t):
    x = d*t; return abs(x - floor(x + F(1,2))) >= F(1,8)
for r in (F(1,22), F(1,20), F(1,16), F(1,10)):
    d = {1: 1 - r, 2: 2 + r, **{j: F(j) for j in range(3, 8)}}
    assert all(abs(d[j] - j) <= r for j in d)
    u = F(49) / (8*d[7]); w_rec = F(7) / (8*d[1])       # record's interval [a^2/(8 d_a), a(8-a)/(8 d_{8-a})]
    cell_end = F(15) / (8*(2 + r))                       # runner 2's entry (15/8)/d_2
    lonely = lambda t: all(clear(x, t) for x in d.values())
    print("r =", r, " u =", u, " record right end =", w_rec, " lonely at u:", lonely(u),
          " lonely at record right end:", lonely(w_rec), " runner-2 entry =", cell_end, " lonely there:", lonely(cell_end),
          " entry < record right end:", cell_end < w_rec)
