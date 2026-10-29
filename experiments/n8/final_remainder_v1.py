# E641: the left-over whole-number sets (E639 window version) after the 53 cores (E640) and FlankBand(n <= 12).  Exact.  usage: N
import pickle, sys, math
from fractions import Fraction as F
N = int(sys.argv[1])
cores = [tuple(int(x) for x in l.split(',')) for l in open('core_cover_cores.txt').read().split()]
def flankband(S, nmax=12):
    for e in S:
        for n in range(0, nmax + 1):
            ok = True
            for d in S:
                p = F(d * (8 * n + 1), 8 * e); M = math.floor(p)
                if not (0 <= M <= n and p - M >= F(1, 8) and p - M <= F(7, 8)): ok = False; break
            if ok: return True
    return False
left = pickle.load(open('residual_window_left_N%d.pkl' % N, 'rb'))
inc = [S for S in left if any(set(C) <= set(S) for C in cores)]
rest = [S for S in left if S not in set(inc)]
fb = [S for S in rest if flankband(S)]
rem = [S for S in rest if S not in set(fb)]
print('N', N, 'left-over', len(left), 'in 53 cores', len(inc), 'further in FlankBand n<=12', len(fb), 'remaining', len(rem))
print(rem)
