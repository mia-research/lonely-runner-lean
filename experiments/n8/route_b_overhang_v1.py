"""Route B test: does shadowing the largest flank BOUND the overhang?

A cover of the largest flank uses at most 6 ratios (the 6 non-flank differences), each < 1.
If a shadowing cover exists with a ratio 1/c, then d_min/d_max = 1/c, i.e. S = d_max/d_min = c.
So: for which c does a shadowing cover of size <= 6 exist? If for arbitrarily large c, the
overhang is UNBOUNDED and Route B's premise fails.

Exact set cover by branch and bound on residues mod c.
"""
from fractions import Fraction as F
TH = F(1,8)
def cd(x):
    f = x % 1; return min(f,1-f)
def blocked_set(a, c):
    r = F(a,c)
    return frozenset(k for k in range(c) if cd(r*(k+TH)) < TH)
def min_cover(c, cap=6):
    sets = []
    for a in range(1, c):
        s = blocked_set(a,c)
        if s: sets.append((F(a,c), s))
    universe = set(range(c))
    best = [None]
    def rec(unc, chosen):
        if best[0] is not None and len(chosen) >= best[0][0]: return
        if not unc:
            best[0] = (len(chosen), list(chosen)); return
        if len(chosen) >= cap: return
        e = min(unc)                       # branch on a fixed uncovered element
        for rat, s in sets:
            if e in s:
                rec(unc - s, chosen + [rat])
    rec(universe, [])
    return best[0]
print("smallest shadowing cover of the largest flank, by ratios a/c   (cap: 6 ratios)")
print("a cover with a ratio 1/c means S = d_max/d_min = c\n")
print("  c   min cover size   example")
found_c = []
for c in range(4, 41):
    r = min_cover(c)
    if r is None:
        print(f"  {c:3}   none of size <= 6")
    else:
        sz, cov = r
        found_c.append(c)
        ex = ",".join(str(x) for x in sorted(cov))
        print(f"  {c:3}   {sz}                {ex}")
print()
print(f"denominators admitting a cover of size <= 6: {found_c}")
if found_c:
    print(f"largest tested: c = {max(found_c)}  ->  S = d_max/d_min reaches at least {max(found_c)}")
