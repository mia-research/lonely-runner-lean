"""E403 (2026-10-05), tight34_members_v1: the stored residual members (all 22 fields) of shape (3,4) whose
non-multiples are of type (o,o,o,o) or (o,o,t,t), read against three instants-of-τ families.  Exact (Fractions).
A tight pattern (cost exactly 8) is lonely at (τ + k)/8 for some k whenever τ is clear for the cofactors and either
 (R) τ is a reduction point of a non-multiple (odd w: τ = m/w; 2v: τ = (2m+1)/(2v)), or
 (Q) τ is a coincidence point of two non-multiples d1, d2 with d1 = ±d2 (mod 8): (d1 ∓ d2)/8 = h, τ = j/h
     (at every shift the two readings coincide or mirror, so they block the same shifts)
[PROVISIONAL: counting tool; supports: the free shift].  Each constructed instant is re-checked exactly.
At most CAP = 200000 points are tried per grid; a member is 'left' only if no tried point is clear.
Recorded per member: which family gives a clear τ, and the members left.
"""
import sys, math, collections, itertools
from fractions import Fraction as F
sys.path.insert(0, '.')
from members_reach_check_v1 import load, full_residual, cd, E8, lonely, cascade, typ

CAP = 200000
def clear_at(C, p, q):
    for c in C:
        r = (c * p) % q
        if 8 * r < q or 8 * (q - r) < q: return False
    return True
def first_clear(C, grids):
    """grids: list of (tag, q, numerators generator); returns (tag, F(p, q)) for the first point clear for C."""
    for tag, q, nums in grids:
        for i, p in enumerate(nums):
            if i >= CAP: break
            if clear_at(C, p, q): return (tag, F(p, q))
    return None
def reduction_grids(NM):
    g = []
    for d in NM:
        if d % 2: g.append((('R', d), d, iter(range(d))))
        elif d % 4 == 2: g.append((('R', d), d, (2 * m + 1 for m in range(d // 2))))
    return g
def coincidence_grids(NM):
    g = []
    for a, b in itertools.combinations(NM, 2):
        for s in (a - b, a + b):
            if s != 0 and s % 8 == 0:
                h = abs(s) // 8; g.append((('Q', a, b, h), h, iter(range(h))))
    return g

if __name__ == '__main__':
    out = open('tight34_members_v1.out', 'w'); out.write(__doc__ + "\n")
    for fn in ['../residual_members_C_list_v1.json', 'both_shadowed_members_v1.json']:
        sets = [S for S in dict.fromkeys(load(fn)) if full_residual(S)]
        c = collections.Counter(); left = []; fails = []
        for S in sets:
            M = [d for d in S if d % 8 == 0]; NM = [d for d in S if d % 8]
            if len(M) != 3 or typ(NM) not in ('oooo', 'oott'): continue
            C = [d // 8 for d in M]; ty = typ(NM)
            c[ty] += 1
            found = first_clear(C, reduction_grids(NM)) or first_clear(C, coincidence_grids(NM))
            if found:
                c[(ty, found[0][0])] += 1; out.write('  %s %s settled by %s at tau = %s\n' % (ty, tuple(sorted(S)), found[0], found[1]))
                if not any(lonely(S, (found[1] + k) / 8) for k in range(8)): fails.append((S, found))
            else:
                c[(ty, 'left')] += 1; left.append(S)
        out.write("\n%s: %d residual members; tight (3,4): %s\n" % (fn, len(sets), dict(c)))
        out.write("  constructed-instant failures: %d %s\n" % (len(fails), fails[:5]))
        for S in left: out.write("  left %s landing %s\n" % (tuple(sorted(S)), cascade(list(S))))
    out.close(); print(open('tight34_members_v1.out').read()[len(__doc__):])
