# E823: converse test of E822 item 2 on seeded random gcd-1 six-sets (exact): shift-0 chain exists iff max window end >= 1/3?  usage: seed
import sys, math, random
from multiprocessing import Pool
from fractions import Fraction as F
from chain_shift_cause_v1 import zero_shift_chain
def job(core):
    ok, mh, T = zero_shift_chain(core); return core, ok, mh, T
if __name__ == '__main__':
    random.seed(int(sys.argv[1])); sets = []
    for H, cnt in [(14, 200), (30, 200), (60, 150), (150, 100)]:
        while cnt:
            c = tuple(sorted(random.sample(range(1, H + 1), 6)))
            g = 0
            for d in c: g = math.gcd(g, d)
            if g == 1: sets.append(c); cnt -= 1
    with Pool(10) as p: res = p.map(job, sets, chunksize=4)
    bad = [r for r in res if (r[2] >= F(1, 3)) != r[1]]
    print('sets', len(res), 'prediction agrees on', len(res) - len(bad), 'disagrees on', len(bad))
    print('sets with max hi >= 1/3:', sum(1 for r in res if r[2] >= F(1, 3)), '; with max hi < 1/3:', sum(1 for r in res if r[2] < F(1, 3)))
    print('sets with max hi >= 1/3 and no shift-0 chain:', sum(1 for r in res if r[2] >= F(1, 3) and not r[1]), '; with max hi < 1/3 and a shift-0 chain:', sum(1 for r in res if r[2] < F(1, 3) and r[1]))
    for r in bad[:10]: print(r)
