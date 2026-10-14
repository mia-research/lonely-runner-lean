"""E400 (2026-10-05), shift_cover_drop_check_v1: derivation check of the two arguments of shift_cover_types_v1 and
shift_cover_drop_v1 on whole-number sets, exact (Fractions).

For every 7-subset of [1, N] with at least two odd readings, m multiples of 8 (1 <= m <= 4) and cost >= 8 whose
residue pattern is settled:
  (a) type level (non-coverable): tau = the cofactors' first lonely instant (exact cascade at threshold 1/8 on the
      cofactors), then some k in 0..7 with every reading clear at (tau + k)/8;
  (b) drop (first passing W from shift_cover_drop_v1): t = the first lonely instant of S - W (exact cascade),
      tau = 8t, then some k with every reading of S clear at t + k/8.
The argument says the k exists; the check is that it does, exactly, on every set.  Failures are listed.
"""
import itertools, math, sys
from fractions import Fraction as F
sys.path.insert(0, '.')
from shift_cover_drop_v1 import type_coverable, drop_passes, cost

def cd(x):
    x = x - math.floor(x); return min(x, 1 - x)
E8 = F(1, 8)
def lonely(S, t): return all(cd(d * t) >= E8 for d in S)
def cascade(S):
    t = F(1, 8 * min(S))
    while True:
        bl = [d for d in S if cd(d * t) < E8]
        if not bl: return t
        t = max(F(8 * round(d * t) + 1, 8 * d) for d in bl)

def main(N):
    tot = fa = fb = na = nb = 0; fails = []
    drop_W = {}
    for S in itertools.combinations(range(1, N + 1), 7):
        nonm = [d for d in S if d % 8]; mult = [d for d in S if d % 8 == 0]
        if not (1 <= len(mult) <= 4): continue
        if sum(1 for d in nonm if d % 2) < 2 or sum(cost(d % 8) for d in nonm) < 8: continue
        if math.gcd(*S) != 1: continue
        P = tuple(sorted(d % 8 for d in nonm))
        tot += 1
        if not type_coverable(P):
            na += 1
            tau = cascade([d // 8 for d in mult])
            if not any(lonely(S, (tau + k) / 8) for k in range(8)):
                fa += 1; fails.append(('a', S))
            continue
        if P not in drop_W:
            W = None
            for size in range(1, len(P) + 1):
                for Wc in itertools.combinations(P, size):
                    if drop_passes(P, Wc)[0]: W = Wc; break
                if W: break
            drop_W[P] = W
        W = drop_W[P]
        if W is None: continue
        nb += 1
        rest = list(nonm); Wd = []
        for r in W:
            d = next(x for x in rest if x % 8 == r); rest.remove(d); Wd.append(d)
        Sp = mult + rest
        t = cascade(Sp)
        if not any(lonely(S, t + F(k, 8)) for k in range(8)):
            fb += 1; fails.append(('b', S, tuple(Wd)))
    return tot, na, fa, nb, fb, fails

if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    tot, na, fa, nb, fb, fails = main(N)
    out = open('shift_cover_drop_check_v1.out', 'w'); out.write(__doc__ + "\n")
    out.write("7-subsets of [1,%d], gcd 1, >=2 odd, 1-4 multiples of 8, cost >= 8: %d sets\n" % (N, tot))
    out.write("(a) type-level non-coverable: %d sets, failures %d\n" % (na, fa))
    out.write("(b) settled by a drop: %d sets, failures %d\n" % (nb, fb))
    for f in fails[:30]: out.write("  FAIL %s\n" % (f,))
    out.close(); print(open('shift_cover_drop_check_v1.out').read()[len(__doc__):])
