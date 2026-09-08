r"""
nr2_boundary_exact  --  DISCIPLINE REQUIREMENT (i): boundary exactness.

For every cell [a,b) of the breakpoint partition and every speed e in the tuple:

  (1) COMPLETENESS.  There is NO integer k with  a < k/e < b.   Tested as the exact
      integer comparison  a*e < k*D < b*e  (a,b are numerators over D = lcm), never by
      sampling and never at a midpoint.

  (2) ENTRY = EXIT.  floor(e*a)  ==  lim_{x->b^-} floor(e*x)  =  floor(e*b) - [e*b in Z].

  (3) The blocked/safe verdict computed from the ENTRY state equals the one computed
      from the EXIT state, cell by cell, and the two resulting measures agree.

Also reported: the number of cells whose closing endpoint b is an EXACT hit e*b in Z
for some e (the phenomenon that a midpoint evaluation hides -- at n = 8 the standard
examples are 5*(3/5) = 3 and 7*(5/7) = 5).

Requirement (ii) (track EVERY uncovered residue) is structural here: every verdict is
taken from the full 8-bit union mask, never from a single residue.

Usage: python3 nr2_boundary_exact.py QMAX
"""
import itertools, sys
from math import lcm, gcd
from fractions import Fraction as F
from nr2_core import MASK, ALL, cell_table, safe_measure

QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 4

tot_cells = tot_interior = tot_mismatch = tot_exact_hits = 0
tot_verdict_mismatch = 0
tot_measure_mismatch = 0
n_tuples = 0

def audit(speeds, rhos):
    global tot_cells, tot_interior, tot_mismatch, tot_exact_hits
    global tot_verdict_mismatch, tot_measure_mismatch
    D, p = cell_table(speeds)
    m_entry = 0
    m_exit = 0
    for i in range(len(p) - 1):
        a, b = p[i], p[i + 1]
        tot_cells += 1
        cov_in = 0
        cov_out = 0
        hit = False
        for e, rho in zip(speeds, rhos):
            lo = (a * e) // D
            hi = (b * e) // D
            for k in range(lo + 1, hi + 1):
                if a * e < k * D < b * e:
                    tot_interior += 1
            entry = (a * e) // D
            exact = ((b * e) % D == 0)
            exit_ = (b * e) // D - (1 if exact else 0)
            if exact:
                hit = True
            if entry != exit_:
                tot_mismatch += 1
            cov_in |= MASK[(rho, entry % 8)]
            cov_out |= MASK[(rho, exit_ % 8)]
        if hit:
            tot_exact_hits += 1
        if (cov_in == ALL) != (cov_out == ALL):
            tot_verdict_mismatch += 1
        if cov_in != ALL:
            m_entry += b - a
        if cov_out != ALL:
            m_exit += b - a
    if m_entry != m_exit:
        tot_measure_mismatch += 1
    return F(m_entry, D)


print(f"boundary-exactness audit, q <= {QMAX}")
for rho0 in (2, 4, 6):
    rhos = (1, 3, 5, 7, rho0)
    for qs in itertools.product(range(QMAX + 1), repeat=5):
        sp = tuple(8 * q + r for q, r in zip(qs, rhos))
        if len(set(sp)) != 5:
            continue
        n_tuples += 1
        m = audit(sp, rhos)
        assert m == safe_measure(sp, rhos)
print(f"   tuples audited            : {n_tuples}")
print(f"   cells audited             : {tot_cells}")
print(f"   INTERIOR breakpoints      : {tot_interior}      (must be 0)")
print(f"   entry/exit floor mismatches: {tot_mismatch}      (must be 0)")
print(f"   cells whose closing endpoint is an EXACT hit e*b in Z : {tot_exact_hits}")
print(f"   entry-vs-exit VERDICT mismatches : {tot_verdict_mismatch}   (must be 0)")
print(f"   tuples where |S| differs entry vs exit : {tot_measure_mismatch}   (must be 0)")

# the two named exact hits at n = 8, exhibited
print("\n   named exact endpoint hits, exhibited:")
for e, x in ((5, F(3, 5)), (7, F(5, 7))):
    print(f"      e = {e}, x = {x}:  e*x = {e*x} is an integer;"
          f"  floor at entry = {int(e*x)},  limit from the left = {int(e*x) - 1}")

# B_m two ways (the divisible runners), exact
print("\n   B_m from the floor definition vs the closed form, m = 1..12:")
bad_m = []
for m in range(1, 13):
    e = 8 * m
    fromfloor = []
    for j in range(e):
        if j % 8 in (0, 7):
            fromfloor.append((F(j, e), F(j + 1, e)))
    # closed form  U_j [ j/m - 1/(8m), j/m + 1/(8m) )  intersected with [0,1)
    closed = []
    for j in range(m + 1):
        lo, hi = F(j, m) - F(1, 8 * m), F(j, m) + F(1, 8 * m)
        lo = max(lo, F(0)); hi = min(hi, F(1))
        if lo < hi:
            closed.append((lo, hi))
    def norm(ivs):
        ivs = sorted([list(v) for v in ivs]); out = []
        for a, b in ivs:
            if out and a <= out[-1][1]: out[-1][1] = max(out[-1][1], b)
            else: out.append([a, b])
        return [tuple(v) for v in out]
    a, b = norm(fromfloor), norm(closed)
    ma = sum(y - x for x, y in a)
    if a != b or ma != F(1, 4):
        bad_m.append(m)
print(f"      identical as interval sets and measure exactly 1/4 for every m in 1..12:"
      f" {'YES' if not bad_m else 'NO, failures at ' + str(bad_m)}")
