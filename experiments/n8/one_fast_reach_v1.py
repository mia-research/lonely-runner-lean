"""The R* bound with one fast reading, test v1 (2026-11-25).  Exact Fractions; complete in f.

Setting: d = 1, S = {1} and five readings in (1, 7] (so |S| = 6), F = {f}, f > 7.  By E929 item 1 the landing is in the
first S window that F does not pass.  With one F reading a pass is one move, and by E930 item 1
(`one_move_pass_iff` [L]) f passes the S window [a, b] iff f lies in some I_k(a, b) = ((8k-1)/(8a), (8k+1)/(8b)),
k >= 1, which is non-empty only for b/a < (8k+1)/(8k-1) (E930 item 2), so for finitely many k when b > a.
Every S window lies in one of d's clear arcs [(8j+1)/8, (8j+7)/8].  Hence, EXACTLY:
   R* > 7  (the landing is past d's first arc)   iff f is in A_1(S) = the intersection over S windows in arc 0 of the
                                                     union over k of I_k, intersected with (7, oo);
   R* > 15 (past d's second arc)                  iff f is in A_2(S) = the same over the S windows in arcs 0 and 1.
(The landing cannot lie in d's zones (7/8, 9/8) or (15/8, 17/8), where d is in the way.)  So A_2(S) empty for an S
means: no single fast reading, of any size, puts the landing of S + {f} in d's third arc or later.
Run over: (i) every S with the five readings on the 1/6 grid in (1, 7]; (ii) the S sets of E340's members with
|S| = 6.  f is searched in (7, 10^4) (a cap needed only for zero-length S windows, which allow every lap).  Reported: how many S have A_1 non-empty, how many have A_2 non-empty (with examples), the largest f in any
A_1, and a cross-check of the interval prediction against the cascade on sampled f.
"""
import itertools, pickle, random, sys
from fractions import Fraction as Fr
from math import floor, ceil
exec(open('wall_window_index_v5.py').read().split('def f_run')[0])
def allowed(a, b, fmax):
    out = []
    k = 1
    while True:
        if Fr(8 * k - 1) / (8 * a) >= fmax: break          # beyond the f still allowed

        lo, hi = Fr(8 * k - 1) / (8 * a), Fr(8 * k + 1) / (8 * b)
        if (8 * k - 1) * b >= (8 * k + 1) * a: break       # I_k empty from here on (ratio (8k+1)/(8k-1) decreases)
        lo = max(lo, Fr(7))
        if lo < hi: out.append((lo, hi))
        k += 1
        if k > 10 ** 6: raise RuntimeError('k')
    return out
def inter(A, B):
    """intersection of two sorted lists of disjoint open intervals (two pointers)."""
    out = []; i = j = 0
    while i < len(A) and j < len(B):
        lo, hi = max(A[i][0], B[j][0]), min(A[i][1], B[j][1])
        if lo < hi: out.append((lo, hi))
        if A[i][1] < B[j][1]: i += 1
        else: j += 1
    return out
def reach(S):
    ws = windows(S, E, Fr(23, 8))
    A = [(Fr(7), Fr(10) ** 4)]; A1 = None
    for a, b, o in ws:
        if a > Fr(15, 8): break
        if b > Fr(7, 8) and A1 is None: A1 = list(A)
        if not A: break                                  # no f passes: nothing later can be passed
        iv = allowed(a, b, max(h for l, h in A))
        A = inter(A, iv)
        if not A and A1 is not None: break
    if A1 is None: A1 = list(A)
    return A1, A
def check(S, f):
    rs = sorted(S + [f]); T, _ = cascade(rs, E); return 8 * T
cnt = dict(S=0, A1=0, A2=0); ex2 = []; maxf = Fr(0); rng = random.Random(3); bad = 0; checks = 0
def run(S):
    global maxf, bad, checks
    cnt['S'] += 1
    A1, A2 = reach(S)
    if A1:
        cnt['A1'] += 1; maxf = max(maxf, max(h for l, h in A1))
        if rng.random() < 0.02:
            l, h = A1[rng.randrange(len(A1))]; f = (l + h) / 2
            R = check(S, f); checks += 1
            if not (R > 7): bad += 1
    if A2:
        cnt['A2'] += 1
        if len(ex2) < 10: ex2.append(([str(x) for x in S], [(str(l), str(h)) for l, h in A2[:3]]))
mode = sys.argv[1]
if mode == 'grid':
    vals = [Fr(i, 6) for i in range(7, 43)]
    for c in itertools.combinations(vals, 5): run([Fr(1)] + list(c))
else:
    rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
    seen = set()
    for r in rec:
        rs = sorted(Fr(x) for x in r[1]); S = [x for x in rs if x <= 7]
        if len(S) != 6 or tuple(S) in seen: continue
        seen.add(tuple(S)); run(S)
print(mode, cnt, '| largest f in any A_1:', maxf, '| cascade cross-checks of A_1 (R* > 7 predicted):', checks, 'failures', bad)
for e in ex2: print('A_2 non-empty:', e)
