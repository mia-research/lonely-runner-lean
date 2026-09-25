"""Every lonely cell contains the mirror meeting of its two boundary flanks.

A cell [L, R] is opened by eL at lap jL (eL reads 1/8 at L) and closed by eR at lap kR (eR reads 7/8
at R).  Inside the cell neither passes 0, so their readings u, v rise continuously; u + v - 1 is
<= 0 at L and >= 0 at R, hence u + v = 1 somewhere: the two flanks at x and 1 - x.  In closed form
t_m = (jL + kR)/(eL + eR).  So every lonely instant lies in a cell whose centre is a lonely mirror
meeting K/(d + d'): the global-isolation event of the pair, thickened.  Checked exactly here.
"""
import itertools, random
from fractions import Fraction as Fr
__file__ = __file__.replace('mirror_centre_v1.py', 'player_census_v1.py')
src = open(__file__).read()
exec(src[:src.index("R40 = [S")])
R40 = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
random.seed(15)
bad = n = 0
for S in random.sample(R40, 3000):
    for c in cells_full(S):
        n += 1
        tm = Fr(c['jL'] + c['kR'], c['eL'] + c['eR'])
        u = (c['eL'] * tm) % 1; v = (c['eR'] * tm) % 1
        inside = c['L'] <= tm <= c['R']
        lonely = all(Fr(1, 8) <= (d * tm) % 1 <= Fr(7, 8) for d in S)
        if not (inside and u + v == 1 and lonely): bad += 1
print(f"3000 residual sets of [1,40], {n} cells: t_m = (jL + kR)/(eL + eR) inside the cell, eL and eR at x and 1 - x, and lonely: fails for {bad}")
