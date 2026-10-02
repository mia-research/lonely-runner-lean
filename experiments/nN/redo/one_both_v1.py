"""E266: (1) the random cluster(s) with ranks 1 and 2 both shadowed (slow_flank_mech_v2 [B]); (2) per exception, the walkers whose shift
frees rank 1 in >= 6 of 8 shifts (critical set) against the shadowers named in slow_flank_mech_v1.out."""
import sys, os, random, re
from fractions import Fraction as F
HERE = os.path.dirname(os.path.abspath(__file__)); os.chdir(HERE); sys.path.insert(0, '../band_cert_v1'); sys.path.insert(0, HERE)
from slow_flank_mech_v1 import state, rand_cluster
from slow_flank_mech_v2 import valid, land_flank
out = open('one_both_v1.out', 'w'); out.write(__doc__ + "\n")
def w(s): out.write(s + "\n"); out.flush()
for seed in range(40):
    rnd = random.Random(seed)
    for _ in range(300):
        c, cl = rand_cluster(rnd)
        if not valid(c, cl): continue
        st = [state(c, cl, e) for e in cl]
        if st[0]['state'] != 'free' and st[1]['state'] != 'free':
            lf, ts = land_flank(c, cl)
            w("seed %d: x/c %s; x/x1 %s; states %s; landing flank %s, R = 8 c t = %.4f" % (seed, [round(x / c, 2) for x in cl], [round(x / cl[0], 3) for x in cl], [s['state'] for s in st], lf, float(8 * c * ts)))
            for i in (0, 1):
                s = st[i]
                if s['state'] == 'alone': w("   rank %d alone: walker %d, A %d, eps %.4f, ratio %.4f" % (i + 1, s['j'] + 1, s['A'], float(s['eps']), float(s['ratio'])))
                else:
                    from collections import Counter
                    occ = Counter(j + 1 for q in s['sets'] for j in q)
                    w("   rank %d hand-off: n %d, occupants (walker: openings) %s" % (i + 1, s['n'], dict(occ)))
# critical sets
txt = open('slow_flank_mech_v2.out').read().split('[C]')[1].splitlines()[1:]
w("\ncritical walkers (shift frees rank 1 in >= 6/8) per exception:")
for line in txt:
    m = re.match(r'seed (\d+) (\w) base landing (\w+): (.*)', line)
    if not m: continue
    crit = [int(a) for a, b in re.findall(r'w(\d): (\d)/8 free', m.group(4)) if int(b) >= 6]
    w("   seed %s %s base landing %s: critical %s" % (m.group(1), m.group(2), m.group(3), crit))
out.close(); print(open('one_both_v1.out').read()[len(__doc__):])
