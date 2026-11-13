# anchor_law_v4.py -- cross-order anchor-law test, hardened: per-order deadline, small default batches,
# progress lines flushed per 50 arrangements.  The v1-v3 failures: v1 chased pathological cascades
# (cap=4000, exponential R growth), v2/v3 died silently as `python3 -c` heredocs.  This file runs as a
# real script with time bounds and flushes, so any pathology is visible.
# usage: python3 anchor_law_v4.py [k] [N] [deadline_s]
import sys, random, time
from fractions import Fraction as F
sys.path.insert(0, '/Users/trentpalelei/Desktop/Math Ex/experiments/nn_schema')
import schema_sweep_v1 as S

def run_order(k, N, deadline, rnd):
    S.K = k
    ok = nomove = cap = li = lm = 0
    bad = []
    t0 = time.time()
    for i in range(N):
        if time.time() > deadline:
            print('  k=%d DEADLINE at %d/%d' % (k, i, N), flush=True)
            break
        rhos = [F(1)]
        while len(rhos) < k - 1:
            r = F(rnd.randint(65, (2 * k + 1) * 64), 64)
            if r > rhos[-1]: rhos.append(r)
        steps, landing = S.cascade(rhos, cap=120)
        if landing is None:
            cap += 1
        elif not steps:
            nomove += 1
        else:
            ok += 1
            num = landing * rhos[steps[0]['setter']]
            if num.denominator == 1:
                li += 1
                if num.numerator % k == 1: lm += 1
                else: bad.append(str(landing))
            else:
                bad.append('nonint:' + str(landing))
        if (i + 1) % 50 == 0:
            print('  k=%d %d/%d ok=%d cap=%d (%.1fs)' % (k, i + 1, N, ok, cap, time.time() - t0), flush=True)
    print('k=%d DONE: ok=%d nomove=%d cap=%d | integer %d/%d | =1modk %d/%d | bad %s' % (
        k, ok, nomove, cap, li, ok, lm, ok, bad[:5]), flush=True)

def main():
    ks = [int(x) for x in sys.argv[1].split(',')] if len(sys.argv) > 1 else [4]
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    budget = float(sys.argv[3]) if len(sys.argv) > 3 else 120.0
    rnd = random.Random(20261107)
    for k in ks:
        run_order(k, N, time.time() + budget, rnd)

if __name__ == '__main__':
    main()
