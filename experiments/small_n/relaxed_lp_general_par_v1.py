"""Parallel version of relaxed_lp_general_v1: splits the depth-first search on the first two moves.
Usage: n LMAX DMAX [EPS]"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from multiprocessing import Pool
n = int(sys.argv[1]); LMAX = int(sys.argv[2]); DMAX = int(sys.argv[3]); EPS = sys.argv[4] if len(sys.argv) > 4 else '1e-7'
def work(prefix):
    sys.argv = ['x', str(n), str(LMAX), str(DMAX), EPS]
    import importlib
    g = {}
    src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'relaxed_lp_general_v1.py')).read()
    src = src.split('dfs([], [])')[0]
    exec(compile(src, 'lp', 'exec'), g)
    word, laps = prefix
    g['dfs'](word, laps)
    return g['best'], g['nodes'], g['near_used']
if __name__ == '__main__':
    R = n - 2
    prefixes = []
    for y1 in range(R + 1):
        for q1 in range(1, LMAX + 1):
            for y2 in range(R + 1):
                if y2 == y1: continue
                for q2 in range(1, LMAX + 1):
                    prefixes.append(([y1, y2], [q1, q2]))
    t0 = time.time()
    with Pool() as p: res = p.map(work, prefixes, chunksize=1)
    best = max(res, key=lambda r: r[0][0])
    names = [chr(ord('b') + i) for i in range(R)] + ['a']
    w, l = best[0][1]
    print(f'n={n} LMAX={LMAX} DMAX={DMAX} EPS={EPS}: LP nodes {sum(r[1] for r in res)}, {time.time()-t0:.1f}s (prefix length 2)')
    print(f'supremum nearest reading {n*best[0][0]:.6f} at word {"".join(names[x] for x in w)} laps {l}')
    print(f'largest reading among chains in which the nearest runner sets a move: {max(r[2] for r in res):.6f}')
