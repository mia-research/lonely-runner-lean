"""E400 (2026-10-05), shift_cover_types_v1: which residue patterns of the non-multiples of 8 can block all eight
shifts t = (tau + k)/8, k = 0..7, at some offset tau.  Exact, finite; no sampling.

Objects (DescentMultiN, ParityDescentN): at an offset tau the non-multiple d blocks the shift k iff
circDist((d*tau + d*k)/8) < 1/8.  Derived (by hand; ParityDescentN.odd_blocked_same_parity, even_blocked_parity,
DescentMultiN.card_bad_le): two blocked shifts k1, k2 of d satisfy d(k1-k2) = 8w + s with |s| <= 1, so
  d odd:          k1 - k2 = 0 or +-d (mod 8)   -> blocked set inside a pair {x, x+d} (x any residue);
  d = 2 mod 4:    d(k1-k2) = 0 mod 8            -> inside a class {c, c+4} mod 8;
  d = 4 mod 8:    k1 = k2 mod 2                 -> inside a parity class.
Every such maximal set is reached by some offset (y = d*tau mod 8 moves the open arc of length 2 freely).
A residue pattern is COVERABLE if some choice of one maximal set per non-multiple covers Z/8; otherwise every
offset leaves a free shift, and the set is lonely whenever its multiples' cofactors are lonely at some tau
(the parity descent's argument with the exact sets in place of the counts).

Scope: the residual's crowded level (MANUSCRIPT_v22 s17C; EightResidual): 7 readings, m multiples of 8
(m = 1..4, at most 6), n = 7 - m non-multiples, at least two odd (two_le_odd_of_residual), cost
sum max(2, gcd(d,8)) >= 8.  Patterns are multisets of residues mod 8 of the non-multiples.
Recorded: per shape, every pattern, coverable or not; for the coverable, one cover.
Pass condition (derivation checks only): (1) every pattern with ParitySplit8 is non-coverable (the proved theorem);
(2) the maximal sets are reached: for each residue r and each maximal set, an exact offset y in Fractions at which
the blocked set of the reading r equals it (positive control).
"""
import itertools
from fractions import Fraction as F
from collections import Counter

def maximal_sets(r):
    if r % 2:
        return [frozenset({x, (x + r) % 8}) for x in range(8)]
    if r % 4 == 2:
        return [frozenset({c, c + 4}) for c in range(4)]
    return [frozenset(range(0, 8, 2)), frozenset(range(1, 8, 2))]

def blocked(r, y):   # exact: shifts k with (r*k + y) mod 8 in (-1, 1)
    out = set()
    for k in range(8):
        z = (r * k + y) % 8
        if z < 1 or z > 7: out.add(k)
    return frozenset(out)

def control():
    bad = []
    for r in range(1, 8):
        reach = set()
        for num in range(0, 8 * 16):
            y = F(num, 16) + F(1, 32)          # non-integer offsets on a fine exact grid
            reach.add(blocked(r, y))
        for S in maximal_sets(r):
            if S not in reach: bad.append((r, sorted(S)))
    return bad

def coverable(rs):
    for choice in itertools.product(*[maximal_sets(r) for r in rs]):
        if frozenset().union(*choice) == frozenset(range(8)):
            return choice
    return None

def cost(r): return 2 if r % 2 or r % 4 == 2 else 4

def parity_split(rs):
    od = sum(1 for r in rs if r % 2); ev = [cost(r) for r in rs if r % 2 == 0]
    for mask in range(1 << len(ev)):
        a = sum(ev[i] for i in range(len(ev)) if mask >> i & 1); b = sum(ev) - a
        if not (od + a < 4 or od + b < 4): return False
    return True

if __name__ == '__main__':
    out = open('shift_cover_types_v1.out', 'w'); out.write(__doc__ + "\n")
    c = control()
    out.write("control (every maximal set reached by an exact offset): %s\n" % ("PASS" if not c else "FAIL %s" % c))
    viol = []
    for m in (1, 2, 3, 4):
        n = 7 - m
        pats = [p for p in itertools.combinations_with_replacement((1, 2, 3, 4, 5, 6, 7), n)
                if sum(1 for r in p if r % 2) >= 2 and sum(cost(r) for r in p) >= 8]
        cov = []; non = []
        for p in pats:
            ch = coverable(p)
            (cov if ch else non).append((p, ch))
            if parity_split(p) and ch: viol.append(p)
        out.write("\nshape (%d,%d): residue patterns %d; non-coverable (closed for every tau) %d; coverable %d\n" % (m, n, len(pats), len(non), len(cov)))
        bytype = Counter(); bytype_non = Counter()
        for p, ch in cov + non:
            ty = ''.join(sorted('o' if r % 2 else ('t' if r % 4 == 2 else 'f') for r in p))
            bytype[ty] += 1
            if not ch: bytype_non[ty] += 1
        for ty in sorted(bytype):
            out.write("  type %s: patterns %d, non-coverable %d\n" % (ty, bytype[ty], bytype_non[ty]))
        for p, ch in non:
            out.write("  NON-COVERABLE %s\n" % (p,))
        for p, ch in cov[:400]:
            out.write("  coverable %s by %s\n" % (p, [sorted(s) for s in ch]))
    out.write("\nderivation check (ParitySplit8 => non-coverable): %s\n" % ("PASS" if not viol else "FAIL %s" % viol[:10]))
    out.close()
    print(open('shift_cover_types_v1.out').read()[len(__doc__):][:6000])
