# E645: do the long-chain six-sets of chain_stats_v1.py have a run of consecutive integers?  (float chains steer only; the run test is exact integer arithmetic).  usage: N
import sys, math, itertools, collections
N = int(sys.argv[1]); sys.argv = ['x', str(N)]
src = open('chain_stats_v1.py').read().split('rows = []')[0]
exec(src)
def longest_run(C):
    best = cur = 1
    for a, b in zip(C, C[1:]):
        cur = cur + 1 if b == a + 1 else 1; best = max(best, cur)
    return best
def has_step_run(C):
    # a run of length >=3 in an AP of common difference d where d divides every reading? (grid with step d)
    best = 1
    for d in range(1, N):
        s = set(C)
        for a in C:
            r = 1; x = a
            while x + d in s: x += d; r += 1
            best = max(best, r) if d == 1 else best
    return best
rows = []
for C in itertools.combinations(range(1, N + 1), 6):
    g = 0
    for d in C: g = math.gcd(g, d)
    if g != 1: continue
    J, T = windows(C); cl, y0 = chain_len(J, T)
    rows.append((C, cl, longest_run(C)))
def frac(sel): 
    sel = list(sel); return (sum(1 for r in sel if r[2] >= 3), len(sel))
print('N', N, 'sets', len(rows))
for lo, hi in [(2, 2), (3, 3), (4, 5), (6, 8), (9, 99)]:
    a, b = frac(r for r in rows if r[1] is not None and lo <= r[1] <= hi)
    print('chain length', lo, '-', hi, ': sets', b, ' with a run of >=3 consecutive integers', a)
