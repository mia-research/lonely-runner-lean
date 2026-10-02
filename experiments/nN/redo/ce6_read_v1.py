"""E264: the 6 counterexamples read per flank (hole_C1_flanks_v1.flank) and by residue: which cluster flanks are free, shadowed
by one walker, or hand-off; each reading's residue mod 8 (the eight field), and c = L*u."""
import sys, re, os
HERE = os.path.dirname(os.path.abspath(__file__)); os.chdir(HERE); sys.path.insert(0, '../band_cert_v1'); sys.path.insert(0, HERE)
from hole_C1_flanks_v1 import flank
S6 = []
for line in open('restricted_b_v1.out'):
    m = re.match(r'\s+seed (\d+) mode A: \(([\d, ]+)\)', line)
    if m: S6.append((int(m.group(1)), tuple(int(x) for x in m.group(2).split(','))))
out = open('ce6_read_v1.out', 'w'); out.write(__doc__ + "\n")
def w(s): out.write(s + "\n"); out.flush()
for seed, S in S6:
    c = S[0]; cl = list(S[1:])
    w("seed %d: ratios x/c %s; mod 8 %s; mod 24 %s" % (seed, [round(x / c, 2) for x in cl], [x % 8 for x in S], [x % 24 for x in S]))
    for i, e in enumerate(cl):
        r = flank(c, cl, e)
        w("   flank %d (x/c %.2f, spread to fastest %.3f): %s" % (i + 1, e / c, cl[-1] / e, {k: (v if k != 'occ' else [(o[0], o[1], o[2], o[3], round(o[4], 3)) for o in v]) for k, v in r.items() if k in ('state', 'n', 's', 'walker', 'occ', 'idx')}))
out.close(); print(open('ce6_read_v1.out').read()[len(__doc__):])
