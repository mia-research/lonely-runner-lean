# E645: exact chain data: the 53 cores plus every gcd-1 six-subset of [1, N].  usage: N out.csv
import sys, math, itertools
from multiprocessing import Pool
from chain_fast_v1 import feats
def runs(core):
    s = sorted(core); r = []; cur = 1
    for a, b in zip(s, s[1:]):
        if b == a + 1: cur += 1
        else: r.append(cur); cur = 1
    r.append(cur); return r
def job(c):
    r = feats(c); return (c, r['chain'], r['y0'], r['w'], r['nw'], r['T'], runs(c))
if __name__ == '__main__':
    N = int(sys.argv[1]); out = sys.argv[2]
    cores = [tuple(int(x) for x in l.split(',')) for l in open('core_cover_cores.txt') if l.strip()]
    sets = set(cores)
    for C in itertools.combinations(range(1, N + 1), 6):
        g = 0
        for d in C: g = math.gcd(g, d)
        if g == 1: sets.add(C)
    sets = sorted(sets, key=lambda c: (max(c), c))
    with Pool(10) as p, open(out, 'w') as f:
        f.write('core|chain|y0|w|nwindows|T|runs|in53\n')
        for r in p.imap_unordered(job, sets, chunksize=4):
            f.write('%s|%s|%s|%s|%s|%s|%s|%d\n' % (','.join(map(str, r[0])), r[1], r[2], r[3], r[4], r[5], r[6], r[0] in set(cores))); f.flush()
