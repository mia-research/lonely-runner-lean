# Is a member's opener lap a copy of a lower-lap arrangement?  Shift the opener's reading by -8k/R* (exact Fractions);
# R* is preserved exactly; the question is whether the whole state sequence is preserved.
import sys, pickle
from fractions import Fraction as F
from multiprocessing import Pool
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
J = int(sys.argv[1]); got = pickle.load(open('cell_members_J%d.pkl' % J, 'rb'))
def states(rho):
    steps, R = path(rho); return tuple(s['R2'] for s in steps), R
def work(item):
    i, rho = item; o = outcome(rho); s, j = o['opener']; R = o['R']
    st0, _ = states(rho)
    best = 0; same = []
    for k in range(1, j):
        v = list(rho); v[s-1] = rho[s-1] - F(8*k) / R
        if v[s-1] <= 0: break
        v2 = sorted(v)
        if len(set(v2)) < 7: continue
        m = v2[0]; v2 = [x/m for x in v2] if m != 1 else v2
        # state sequence must be compared at the original scale (d_min may change if s == 1)
        if s == 1: continue
        st1, R1 = states(v2)
        if st1 == st0 and R1 == R: best = k; same.append(k)
    return (i, s, j, best, tuple(same))
if __name__ == "__main__":
    with Pool(3) as p: res = p.map(work, got, chunksize=200)
    pickle.dump(res, open('lap_shift_reduce_J%d.pkl' % J, 'wb'))
    n = len(res); red = [r for r in res if r[3] > 0]
    from collections import Counter
    print("J", J, "members", n, "with some lap-lowered copy having identical states and landing:", len(red))
    print("opener lap j vs largest reducible k (count):")
    c = Counter((min(r[2], 20), r[3]) for r in res)
    for j in sorted({r[2] for r in res}):
        row = {k: v for (jj, k), v in c.items() if jj == min(j, 20)}
        print("  lap", j, dict(sorted(row.items())))
    # reduced lap: j - best
    print("lowest reachable lap j-best distribution:", sorted(Counter(r[2]-r[3] for r in res).items())[:25])
