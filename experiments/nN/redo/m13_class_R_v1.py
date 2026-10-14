"""E407 (2026-10-06), m13_class_R_v1: where does M(1,3)'s open class R lie?  The classifier construct13 of
mixed_lemma_check_v1 (imported, unchanged), run on c in [1, CM] and distinct odd u1 < u2 < u3 in [1, UM]; for every
class-R case the exhaustive decision solvable() of the same script supplies a tau, checked exactly.
Recorded: the class-R count by c, the largest u3 seen in class R, and any case with no tau.
"""
import sys, itertools, collections
CM = int(sys.argv[1]) if len(sys.argv) > 1 else 48; UM = int(sys.argv[2]) if len(sys.argv) > 2 else 79
sys.argv = [sys.argv[0], str(max(CM, UM))]
sys.path.insert(0, '.')
from mixed_lemma_check_v1 import construct13, solvable, good
odds = [u for u in range(1, UM + 1) if u % 2]
byc = collections.Counter(); maxu = 0; nos = []; tot = 0; ex = []
for c in range(1, CM + 1):
    for U in itertools.combinations(odds, 3):
        tot += 1
        k, t = construct13(c, U)
        if k == 'R':
            byc[c] += 1; maxu = max(maxu, U[2])
            s = solvable((c,), U)
            if s is None or not good((c,), U, s): nos.append((c, U))
            if len(ex) < 10: ex.append((c, U, s))
msg = "c in [1,%d], odd u in [1,%d]: cases %d; class R %d, by c %s; largest u3 in class R %d; class-R cases with no tau %d %s" % (
    CM, UM, tot, sum(byc.values()), dict(sorted(byc.items())), maxu, len(nos), nos[:5])
out = open('m13_class_R_v1.out', 'w'); out.write(__doc__ + "\n" + msg + "\n")
for e in ex: out.write("  example c=%d U=%s tau=%s\n" % e)
out.close(); print(msg)
