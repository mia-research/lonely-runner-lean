# E642: random whole-number 7-sets from [1, M] (seeded) that pass the simple fields of EightResidual and the residue cases; which are left after
#   fixed instants (368), the gate chain, the window chain, the 53 cores and FlankList(n <= 12 or NL)?  Exact.  usage: M count seed [NL]
import sys, random, math, itertools, pickle
from fractions import Fraction as F
sys.argv_saved = sys.argv[:]
M = int(sys.argv[1]); COUNT = int(sys.argv[2]); SEED = int(sys.argv[3]); NL = int(sys.argv[4]) if len(sys.argv) > 4 else 12
from classes_lib_v1 import *
cores = [tuple(int(x) for x in l.split(',')) for l in open('core_cover_cores.txt').read().split()]
def flanklist(S, nl):
    for e in S:
        for n in range(0, nl + 1):
            t = F(8 * n + 1, 8 * e)
            if all(dist(d * t) >= E for d in S): return True
    return False
rnd = random.Random(SEED); tested = 0; left = []; stats = dict(fixed=0, gate=0, window=0, cores=0, flank=0)
while tested < COUNT:
    S = tuple(sorted([1] + rnd.sample(range(2, M + 1), 6)))
    if not simple_fields(S) or residue_settled(S): continue
    tested += 1
    if fixedR(S): stats['fixed'] += 1; continue
    if chain2([F(d, S[0]) for d in S]) or chain2q([F(d) for d in S]): stats['gate'] += 1; continue
    if chain_window(S): stats['window'] += 1; continue
    if any(set(C) <= set(S) for C in cores): stats['cores'] += 1; continue
    if flanklist(S, NL): stats['flank'] += 1; continue
    left.append(S)
print('M', M, 'tested', tested, stats, 'left', len(left))
print(left[:15])
pickle.dump(left, open('random_integer_left_M%d_s%d.pkl' % (M, SEED), 'wb'))
