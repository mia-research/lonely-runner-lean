from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction as Q
from itertools import combinations_with_replacement
from math import gcd
import argparse

EXPECTED_COUNTS = {(4, 9): 444, (5, 10): 641, (6, 5): 125}

from mixed_harmonic_check import CAP, FIRST, SIX, cover_states


def run(job):
    p, times, c = job
    counts = cover_states(p, times, c)
    return p, counts


def jobs(k, top, times, c, *, exact_max):
    for p in combinations_with_replacement(range(1, top+1), k):
        if gcd(*p) == 1 and (not exact_max or p[-1] == top):
            yield p, times, c


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--workers', type=int, default=4)
    parser.add_argument('--group', choices=('four','five','six'), required=True)
    args = parser.parse_args()
    configs = {
        'four': [(4,9,(1,),Q(1,8),False), (4,9,(1,2),Q(1,8),False),
                 (4,9,(1,2),CAP,False)],
        'five': [(5,10,FIRST,CAP,True)],
        'six': [(6,5,SIX,CAP,True)],
    }
    with ProcessPoolExecutor(args.workers) as pool:
        for k, top, times, c, exact_max in configs[args.group]:
            all_jobs = list(jobs(k, top, times, c, exact_max=exact_max))
            assert len(all_jobs) == EXPECTED_COUNTS[k, top]
            residual = []
            for p, counts in pool.map(run, all_jobs):
                if counts[-1]:
                    residual.append((p, counts))
                    if len(residual) <= 10:
                        print('SURVIVES', p, counts, flush=True)
            print(k, 'harmonics,', 'max =' if exact_max else 'max <=', top, 'times', times,
                  'cap', str(c), ':', len(all_jobs), 'profiles,', len(residual), 'residual', flush=True)
            if times != (1,):
                assert not residual, residual[:10]
            if k == 4 and times == (1,) and c == Q(1,8):
                assert residual and residual[0][0] == (1,1,1,1)


if __name__ == '__main__':
    main()
