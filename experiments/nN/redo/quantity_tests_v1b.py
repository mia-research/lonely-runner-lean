"""E170 follow-up: (a) pair recurrence with and without the depth; (b) how often the MixedLapOverlapN criterion
certifies, and how early; (c) E114's family at thresholds 1/8 and 1/5.  Exact; same cascade as quantity_tests_v1."""
import itertools, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from quantity_tests_v1 import quantities, next_opening, cd

def one(S):
    r = quantities(S)
    pairs_ab = Counter((a, b) for a, b, _ in r['pairs'])
    pair_rep = any(v > 1 for v in pairs_ab.values())
    state_rep = any(v > 1 for v in Counter(r['pairs']).values())
    cert = [j for j, row in enumerate(r['rows']) if row['_certified']]
    return r['N'], pair_rep, state_rep, (cert[0] if cert else None)

def work(sets): return [one(S) for S in sets]

def cascade_n(S, n):
    e = F(1, n); S = sorted(S); t = F(1, n * S[0]); k = 0
    while True:
        B = [d for d in S if cd(d * t) < e]
        if not B: return k
        t = max((math.ceil(d * t - e) + e) / d for d in B); k += 1

if __name__ == '__main__':
    pops = {'Case B to 24': [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1]]}
    import sys; sys.path.insert(0, '../band_cert_v1')
    from coverB_fine_v1 import late_shapes
    pops['late band shapes'] = late_shapes()
    with Pool(8) as pool:
        for name, sets in pops.items():
            res = [x for part in pool.map(work, [sets[i::32] for i in range(32)]) for x in part]
            multi = [x for x in res if x[0] >= 2]
            c = Counter()
            for N, pr, sr, fc in multi:
                c['chains>=2'] += 1; c['pair (a,b) recurs'] += pr; c['pair+depth recurs'] += sr
                if fc is not None:
                    c['criterion certifies somewhere'] += 1
                    c['certifies at j = N-1 (last move)'] += (fc == N - 1)
                    c['certifies at j <= N-3 (>= 2 moves early)'] += (fc <= N - 3)
            print(name, dict(c))
    for k in range(2, 11):
        S = [1, 5 * k - 2, 5 * k, 10 * k - 2]
        print('E114 family k=%d %s: moves at 1/8: %d, at 1/5: %d (2k+1 = %d)' % (k, S, cascade_n(S, 8), cascade_n(S, 5), 2 * k + 1))
