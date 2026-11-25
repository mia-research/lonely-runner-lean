"""The landing bound with the fastest reading as the one mover, test v1 (2026-11-25).  Exact Fractions.

Object (E389's S6, extended): d = 1; `six` = the six slowest readings (1 included, any sizes); v = the fastest reading,
v > max(six).  The landing T is the first lonely instant >= t0 = 1/8 (the cascade's landing), so T is the first point
>= t0 of clear(six) that v leaves clear.  A closed window [a, b] of clear(six) is left with no clear point by v iff it lies
inside one open zone of v, i.e. v in I_k(a, b) = ((8k-1)/(8a), (8k+1)/(8b)) for some k >= 1 (E930 item 1; E389)
[PROVISIONAL: covering; the claim supported: B*(six) bounds R* for every fastest reading].  Walking the windows in order
with A = the set of v passing every window so far, the first window W = [a, b] at which A empties gives
B*(six) = 8b >= R* for EVERY v > max(six).  v is searched in (max six, vmax) with vmax = 1/(4 L) for the longest window
L > 0 met so far (a zone of v has length 1/(4v), so a window of length L is nested only if v < 1/(4L)); if every window
met is a single point the cap is not removed and the six is reported.
Modes:
  e340   every distinct six-slowest set of E340's 110,081 members (|F| any): B*, the obstruction kind (alone / pair /
         3+), the pair's window indices and laps; and the check R*(member) <= B*(six) for every member.
  climb  exact climb of B* over sixes from fixed starts (seed fixed; deterministic): the largest B* found and its six.
"""
import pickle, random, sys
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
exec(open('wall_window_index_v5.py').read().split('def f_run')[0])
T1 = Fr(39, 8)   # d's arcs 0..4

def passes(a, b, lo0, hi0, limit=None):
    """sorted disjoint open intervals of v in (lo0, hi0) whose zone at some lap k >= 1 contains [a, b].  The laps that
    can meet (lo0, hi0) are k with (8k+1)/(8b) > lo0 and (8k-1)/(8a) < hi0; I_k is non-empty iff 8k(b - a) < a + b."""
    out = []
    k0 = max(1, floor((8 * b * lo0 - 1) / 8)); k1 = ceil((8 * a * hi0 + 1) / 8)
    if a < b: k1 = min(k1, ceil((a + b) / (8 * (b - a))))
    if limit is not None and k1 - k0 > limit: return None
    for k in range(k0, k1 + 1):
        if a < b and 8 * k * (b - a) >= a + b: break
        lo, hi = max(Fr(8 * k - 1) / (8 * a), lo0), min(Fr(8 * k + 1) / (8 * b), hi0)
        if lo < hi: out.append((lo, hi, k))
    return out

def passes_in(a, b, A):
    out = []
    for l, h in A:
        P = passes(a, b, l, h)
        out.extend((x, y) for x, y, k in P)
    return out

def inter(A, B):
    out = []; i = j = 0
    while i < len(A) and j < len(B):
        lo, hi = max(A[i][0], B[j][0]), min(A[i][1], B[j][1])
        if lo < hi: out.append((lo, hi))
        if A[i][1] < B[j][1]: i += 1
        else: j += 1
    return out

def bstar(six, limit=2 * 10 ** 5):
    """walk the windows in order; at window n, vmax = 1/(4 L_n) with L_n the longest of windows 1..n.  The running
    intersection A_n is order-free, so it is rebuilt from the longest window J (fewest laps) whenever J changes and the
    other windows are applied inside A.  Returns (B*, n, A before n, windows, data, cap removed); B* = 'skipped' if the
    longest window's pass set exceeds `limit` laps."""
    ws = windows(six, E, T1)
    vmin = max(six); L = Fr(-1); J = None; A = None; pl = []
    for n, (a, b, o) in enumerate(ws):
        pl.append((a, b))
        if b - a > L:
            L = b - a; J = n
            vmax = Fr(1, 4) / L if L > 0 else Fr(10) ** 4
            P = passes(ws[J][0], ws[J][1], vmin, vmax, limit=limit)
            if P is None: return 'skipped', n, None, ws, pl, False
            Aprev = A; A = [(l, h) for l, h, k in P]
            for j in range(n + 1):
                if j != J and A: A = passes_in(ws[j][0], ws[j][1], A)
        else:
            Aprev = A; A = passes_in(a, b, A)
        if not A: return 8 * b, n, Aprev, ws, pl, L > 0
    return None, None, A, ws, pl, L > 0

def obstruction(n, pl, six):
    """smallest set of windows among 1..n whose pass sets do not meet in (vmin, 1/(4 L_n)): alone, or the earliest
    window j paired with n; 'skipped' if W's own pass set exceeds 10^5 laps."""
    vmin = max(six); L = max(b - a for a, b in pl[:n + 1]); vmax = Fr(1, 4) / L if L > 0 else Fr(10) ** 4
    a, b = pl[n]
    Pn = passes(a, b, vmin, vmax, limit=10 ** 5)
    if Pn is None: return ('skipped', None)
    if not Pn: return ('alone', None)
    Pn = [(l, h) for l, h, k in Pn]
    for j in range(n):
        if not passes_in(pl[j][0], pl[j][1], Pn): return ('pair', j)
    return ('3+', None)

if __name__ == '__main__':
    mode = sys.argv[1]; c = Counter()
    if mode == 'e340':
        rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
        memo = {}; best = None; worst_gap = None
        for r in rec:
            rs = sorted(Fr(x) for x in r[1]); six = tuple(rs[:6]); v = rs[6]
            if six not in memo:
                Bd, n, A, ws, pl, capok = bstar(list(six))
                memo[six] = (Bd, n, ws)
                if Bd is None or Bd == 'skipped': c['six: ' + ('skipped' if Bd else 'no bound below 39')] += 1; continue
                c['six: cap removed' if capok else 'six: cap NOT removed'] += 1
                c['six: B* <= 7' if Bd <= 7 else ('six: B* in [9, 15]' if Bd <= 15 else 'six: B* > 15')] += 1
                kind, j = obstruction(n, pl, list(six))
                a, b, o = ws[n]
                arc = 'arc0' if b <= Fr(7, 8) else 'arc1'
                c[('obstruction', kind, arc)] += 1
                if kind == 'pair': c[('pair: earlier window', 'window 1' if j == 0 else ('previous' if j == n - 1 else 'other'), arc)] += 1
                if best is None or Bd > best[0]: best = (Bd, six, n, ws[n])
            Bd, n, ws = memo[six]
            T, _ = cascade(rs, E); R = 8 * T
            c['member: B* not computed' if Bd in (None, 'skipped') else ('member: R* <= B*' if R <= Bd else 'member: R* > B* (FAIL)')] += 1
            c['member |F| = %d' % sum(1 for x in rs if x > 7)] += 0
        for k, val in sorted(c.items(), key=str): print(val, k)
        Bd, six, n, w = best
        print('largest B* =', Bd, '~', round(float(Bd), 6), '(floats steer only) | six =', [str(x) for x in six], '| W = window', n + 1, (str(w[0]), str(w[1])))
    elif mode == 'climb':
        random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
        rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
        sixes = {}
        for r in rec:
            rs = sorted(Fr(x) for x in r[1]); sixes[tuple(rs[:6])] = 1
        sc = sorted(((x if isinstance(x, Fr) else Fr(0), s) for s in list(sixes)[::50] for x in [bstar(list(s))[0]]), reverse=True)
        starts = [list(s) for _, s in sc[:12]]
        r5, r3, r7 = Fr(47, 9), Fr(47, 15), Fr(2209, 297); r6 = 7 * r7 / 9; r4 = 47 * r6 / 65; r2 = 23 * r4 / 41
        starts.append(sorted([Fr(1), r2, r3, r4, r5, r6]))
        for _ in range(12): starts.append(sorted([Fr(1)] + [Fr(random.randint(1100, 9000), 1000) for _ in range(5)]))
        gbest = (Fr(0), None)
        for s0 in starts:
            cur = list(s0); cb = bstar(cur)[0]; cb = cb if isinstance(cb, Fr) else Fr(0)
            for step in range(int(sys.argv[3]) if len(sys.argv) > 3 else 1500):
                new = list(cur); i = random.randint(1, 5)
                if random.random() < 0.1: new[i] = Fr(random.randint(1001, 12000), 1000)
                else:
                    e = 10 ** random.randint(2, 9); new[i] = (new[i] * (1 + Fr(random.randint(-9, 9), e))).limit_denominator(10 ** 14)
                if new[i] <= 1 or len(set(new)) < 6: continue
                new = sorted(new); nb = bstar(new)[0]
                if isinstance(nb, Fr) and nb >= cb: cur, cb = new, nb
            print('start', [round(float(x), 4) for x in s0], '-> B* =', cb, '~', round(float(cb), 6), '| six', [str(x) for x in cur], flush=True)
            if cb > gbest[0]: gbest = (cb, cur)
        print('largest B* found:', gbest[0], '~', round(float(gbest[0]), 6), '(floats steer only) | six', [str(x) for x in gbest[1]])
