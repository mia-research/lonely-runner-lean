"""Interference between blockers on a rung, on the order-eight residual of [1,30].

Rung (e, N), M = e/N, openings a = 8*i*M + 1 for i in Z/N; d blocks i when d*a mod 8e is within e
of 0.  For two blockers, compare the observed overlap of their blocked openings with the
independent value |B_d|*|B_d'|/N.

A pair is LINKED when a small combination L = m*d - s*m'*d' (m, m' <= 3, s = +-1) has N | L and L
within e of a multiple of 8e.  Then m*x_d - s*m'*x_d' = L/(8e) mod 1 at every opening of the rung
(x = reading as a fraction of a turn): the two readings move together.  Reported: the overlap
ratio for linked and unlinked pairs, on the 10 sets of the 52 with cross-class collisions and on a
random sample of the residual.
"""
import itertools, random, sys
from math import gcd
sys.argv = [sys.argv[0], '30']
exec(open(__file__.replace('interference_v1.py', 'shift_levels_six_eight_v1.py')).read().split('t0 = time.time()')[0])

TEN = [(1, 5, 6, 7, 8, 17, 19), (1, 5, 6, 7, 16, 17, 19), (1, 5, 6, 7, 16, 19, 29), (1, 5, 6, 7, 16, 27, 29),
       (1, 5, 7, 8, 12, 25, 26), (1, 6, 7, 10, 16, 19, 29), (2, 5, 6, 7, 8, 17, 19), (2, 5, 6, 7, 16, 17, 19),
       (3, 4, 5, 7, 17, 19, 24), (3, 7, 8, 10, 12, 26, 29)]

def f(d, e, N):
    M = e // N
    return [0 if e <= (d * (8 * i * M + 1)) % (8 * e) <= 7 * e else 1 for i in range(N)]

def linked(d, d2, e, N, mmax=3):
    for m in range(1, mmax + 1):
        for m2 in range(1, mmax + 1):
            for sg in (1, -1):
                L = m * d - sg * m2 * d2
                if L % N == 0 and min(L % (8 * e), -L % (8 * e)) <= e: return True
    return False

def study(sets, label):
    tot = {True: [0.0, 0.0, 0], False: [0.0, 0.0, 0]}
    for S in sets:
        for e in S:
            for N in range(5, e + 1):
                if e % N: continue
                F = {d: f(d, e, N) for d in S if d != e}
                for d, d2 in itertools.combinations(sorted(F), 2):
                    a, b = F[d], F[d2]
                    if not sum(a) or not sum(b): continue
                    k = linked(d, d2, e, N)
                    tot[k][0] += sum(x * y for x, y in zip(a, b)); tot[k][1] += sum(a) * sum(b) / N; tot[k][2] += 1
    for k in (True, False):
        o, m, n = tot[k]
        print(f"{label}: {'linked' if k else 'unlinked'} pairs {n}: overlap observed/independent {o / m:.2f}")

study(TEN, "the 10")
random.seed(2)
R = [S for S in itertools.combinations(range(1, 31), 7) if eight_residual(S)]
study(random.sample(R, 300), "300 residual sets (seed 2)")
