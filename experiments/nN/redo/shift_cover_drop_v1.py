"""E400 (2026-10-05), shift_cover_drop_v1: the drop check on the residue patterns that shift_cover_types_v1 leaves.

Exact, finite.  Achievable blocked sets of a non-multiple d at an offset (from the arc of length 2 at y = d*tau):
  d odd:        {x, x+d} (y not an integer) or {x} (y an integer), x any residue;
  d = 2 mod 4:  {c, c+4} or empty;
  d = 4 mod 8:  the evens, the odds, or empty.
(Derived from DescentMultiN.bad_step and ParityDescentN; an f-walker's set is a whole parity class or empty because
4k mod 8 takes only the values 0 and 4, each on a whole parity class; a t-walker's set is a whole class mod 4 or
empty likewise.)

DROP CHECK for a pattern P (residues of the non-multiples) and a nonempty part W of it, P' = P - W:
  suppose S' = S - W is lonely at t (it has at most six readings, so order seven gives such t, as
  lonely_eight_of_descent uses).  At tau = 8t shift 0 is clear for P', so each d in P' has an achievable
  blocked set NOT containing 0.  The check passes if, for every choice of such sets for P' and every choice of
  achievable (maximal) sets for W, some shift in Z/8 stays free.  Then S is lonely at t + k/8 for a free k
  (multiples of 8 keep their positions under k/8).  So a pattern passing the drop check for some W is settled
  whenever S - W is lonely, which holds for every set of at most six positive whole numbers.
Recorded: for every pattern coverable at type level (shift_cover_types_v1), the first W (smallest first) that
passes, or none.  Pass condition: derivation checks only - (1) a pattern non-coverable at type level passes with
any W (positive control, run on all of them); (2) spot checks on whole-number sets are in shift_cover_drop_check_v1.
"""
import itertools
from collections import Counter

def ach_sets(r):
    if r % 2:
        return [frozenset({x, (x + r) % 8}) for x in range(8)] + [frozenset({x}) for x in range(8)]
    if r % 4 == 2:
        return [frozenset({c, c + 4}) for c in range(4)] + [frozenset()]
    return [frozenset(range(0, 8, 2)), frozenset(range(1, 8, 2)), frozenset()]

def maximal_sets(r):
    if r % 2: return [frozenset({x, (x + r) % 8}) for x in range(8)]
    if r % 4 == 2: return [frozenset({c, c + 4}) for c in range(4)]
    return [frozenset(range(0, 8, 2)), frozenset(range(1, 8, 2))]

FULL = frozenset(range(8))

def drop_passes(P, W):
    Pp = list(P)
    for r in W: Pp.remove(r)
    opts_p = [[s for s in ach_sets(r) if 0 not in s] for r in Pp]
    # keep only maximal options among those avoiding 0 (supersets block more)
    def maxonly(L):
        return [s for s in L if not any(s < u for u in L)]
    opts_p = [maxonly(L) for L in opts_p]
    opts_w = [maximal_sets(r) for r in W]
    for cp in itertools.product(*opts_p):
        Fr = FULL - frozenset().union(*cp)
        for cw in itertools.product(*opts_w):
            if Fr <= frozenset().union(*cw):
                return False, (cp, cw)
    return True, None

def cost(r): return 2 if r % 2 or r % 4 == 2 else 4
def typ(p): return ''.join(sorted('o' if r % 2 else ('t' if r % 4 == 2 else 'f') for r in p))

def type_coverable(rs):
    for choice in itertools.product(*[maximal_sets(r) for r in rs]):
        if frozenset().union(*choice) == FULL: return True
    return False

if __name__ == '__main__':
    out = open('shift_cover_drop_v1.out', 'w'); out.write(__doc__ + "\n")
    ctrl_fail = 0
    for m in (1, 2, 3, 4):
        n = 7 - m
        pats = [p for p in itertools.combinations_with_replacement((1, 2, 3, 4, 5, 6, 7), n)
                if sum(1 for r in p if r % 2) >= 2 and sum(cost(r) for r in p) >= 8]
        left = Counter(); closed = Counter(); tot = Counter(); leftlist = []
        for p in pats:
            ty = typ(p); tot[ty] += 1
            if not type_coverable(p):
                ok, _ = drop_passes(p, (p[0],))
                if not ok: ctrl_fail += 1
                closed[ty] += 1; continue
            found = None
            for size in range(1, n + 1):
                for W in itertools.combinations(p, size):
                    ok, _ = drop_passes(p, W)
                    if ok: found = W; break
                if found: break
            if found: closed[ty] += 1
            else: left[ty] += 1; leftlist.append(p)
        out.write("\nshape (%d,%d): patterns %d; settled (type level or drop) %d; left %d\n" % (m, n, len(pats), sum(closed.values()), sum(left.values())))
        for ty in sorted(tot):
            out.write("  type %s: patterns %d, settled %d, left %d\n" % (ty, tot[ty], closed[ty], left[ty]))
        for p in leftlist[:200]:
            out.write("  LEFT %s\n" % (p,))
    out.write("\npositive control (type-level non-coverable patterns pass the drop check): %s\n" % ("PASS" if ctrl_fail == 0 else "FAIL %d" % ctrl_fail))
    out.close()
    print(open('shift_cover_drop_v1.out').read()[len(__doc__):][:5000])
