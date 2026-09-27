"""E164: for the sets needing a fine grid (the 15 captures of E157 and the 4 of m_vs_spread_v2): the least (m, j, c)
that works, whether the reference reading j is the captured reading (a multiple of 8 d_min), and the captured reading's
lap K at the bound (c_read = 8 d_min K).  Exact."""
import ast
from fractions import Fraction as F
from casec_gridclass_v1 import works
line = [l for l in open('casec_gridclass_v1.out') if l.startswith('P2')][0]
U = ast.literal_eval(line.split('uncovered (m<=8): ')[1].split(' ', 1)[1])
U += [ast.literal_eval(l.split(' spread')[0]) for l in open('m_vs_spread_v2.out')]
for T in U:
    s = [F(d) for d in T]; dm = T[0]
    caps = [i for i, d in enumerate(T) if d % (8 * dm) == 0]
    found = None
    for m in range(1, 65):
        for j in range(7):
            for c in (1, 3, 5, 7):
                if works(s, j, m, c): found = (m, j, c); break
            if found: break
        if found: break
    m, j, c = found
    print(T, "captured ranks", caps, "laps K", [T[i] // (8 * dm) for i in caps], "-> least m %d, reference rank %d (%s), class %d" % (m, j, 'the captured reading' if j in caps else 'reading %d' % T[j], c))
