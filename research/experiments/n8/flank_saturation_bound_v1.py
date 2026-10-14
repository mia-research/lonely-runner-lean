"""The forced-overlap counting bound.

At a flank e, ratio rho blocks the openings k with circDist(rho(k+1/8)) < 1/8. Every ratio rho < 1
blocks k = 0 automatically (phase rho/8 < 1/8) -- the framework's own observation. So if m of the
blocking sets contain 0, their union misses at least (m-1) of the budget:

    |union| <= sum |S_j| - (m - 1)

and shadowing needs |union| = c (the period). Hence a NECESSARY condition for a shadow:

    sum_j |S_j|  >=  c + m - 1.

Check it on the minimal covers found, and see how tight it is.
"""
from fractions import Fraction as F
TH = F(1,8)
def cd(x):
    f = x % 1; return min(f,1-f)
def blocked(rho, c):
    return set(k for k in range(c) if cd(rho*(k+TH)) < TH)
covers = {
 8:  [F(1,8),F(3,8),F(1,2),F(5,8),F(7,8)],
 10: [F(1,10),F(1,5),F(3,10),F(1,2),F(7,10)],
 12: [F(1,12),F(1,4),F(1,3),F(5,12),F(7,12)],
 16: [F(1,16),F(3,16),F(1,4),F(5,16),F(7,16)],
 20: [F(1,10),F(1,5),F(3,10),F(1,2),F(7,10)],
 30: [F(1,30),F(7,10),F(11,15),F(23,30),F(4,5)],
 40: [F(1,40),F(11,40),F(1,2),F(21,40),F(31,40)],
}
print(" c   sum|S_j|   c+m-1   slack   union   saturated?")
for c, cov in covers.items():
    S = [blocked(r,c) for r in cov]
    m = sum(1 for s in S if 0 in s)
    tot = sum(len(s) for s in S)
    union = set().union(*S)
    need = c + m - 1
    print(f"{c:3}   {tot:6}    {need:5}   {tot-need:5}   {len(union):5}   {'EXACTLY TIGHT' if tot==need else 'slack '+str(tot-need)}")
