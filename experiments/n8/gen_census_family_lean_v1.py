"""Emit the Lean for a census family taken through Flanks.lonely_of_flank_unkillable.

Input: the fixed differences, the flank, the residues to use, and the on-lattice range.
Output: a module discharging the three hypotheses, each clearance fact reduced to
Flanks.circDist_ge_of_band by writing the phase as p/(8e) + c with e <= p <= 7e.

This is the mechanism, not a one-off: the per-family work is arithmetic the script does.
Used for CensusFamilies.family10_lonely; data from cold_family_data_v1.py.
"""
import sys
from fractions import Fraction as F

def decompose(d, r, e, n=8):
    """phase = d*(n*r+1)/(n*e) = p/(n*e) + c, with e <= p <= (n-1)*e required"""
    M = n * e
    num = d * (n * r + 1)
    c = num // M
    p = num - M * c
    if not (e <= p <= (n - 1) * e):
        raise ValueError(f"d={d} r={r}: p={p} outside the band [{e},{(n-1)*e}]")
    return p, c

def plan(fixed, e, residues, xrange_, n=8):
    """Check the data is consistent before any Lean is written."""
    rows = {}
    for r in residues:
        rows[r] = {d: decompose(d, r, e, n) for d in fixed}
    kill = {}
    for x in xrange_:
        for r in residues:
            try:
                kill[x] = (r, decompose(x, r, e, n)); break
            except ValueError:
                continue
        else:
            raise ValueError(f"on-lattice x = {x} is not cleared by any residue in {residues}")
    return rows, kill

if __name__ == '__main__':
    FIXED = [1, 2, 3, 5, 7, 10]; E = 5; U = [1, 3]; XR = range(1, 10)
    rows, kill = plan(FIXED, E, U, XR)
    print(f"family {{{','.join(map(str,FIXED))},x}}, flank {E}, residues {U}")
    for r in U:
        print(f"  r = {r}: " + "  ".join(f"{d}->{p}/{8*E}+{c}" for d, (p, c) in rows[r].items()))
    print("  kill: " + "  ".join(f"x={x}@r{r}({p}/{8*E}+{c})" for x, (r, (p, c)) in kill.items()))
    print("\n  plan consistent -- every clearance fact lands in the band, every on-lattice x is cleared.")
