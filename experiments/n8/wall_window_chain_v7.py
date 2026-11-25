"""Wall-window chain, test v7 (2026-11-25).  Exact Fractions; the cascade is the oracle.

E930 item 5: passes of an S window [a, b] by F's cascade in two or more moves.  Owner question: is each earlier move
also a one-move pass of a sub-window bounded by named instants; if not, why not.
Derivation under test ([P], checked here):
  (1) every intermediate state of the cascade is an exit e_i = (8k_i + 1)/(8 f_i) of its setter f_i at lap k_i, so each
      move i is a one-move pass of the sub-window [e_{i-1}, e_i) bounded by named instants (e_0 = a);
  (2) the setter f_{i+1} is blocked at e_i iff  (8k_{i+1} - 1)/(8k_i + 1) < f_{i+1}/f_i < (8k_{i+1} + 1)/(8k_i + 1)
      (E305's consecutive-zone condition, read at the exit);
  (3) F passes [a, b] iff [a, b] lies in the union of F's open zones: the cascade gives the first F-clear instant >= a.
      Checked by an INDEPENDENT computation: merge F's zones meeting [a, b] as intervals, no cascade.
  (4) S is clear on the whole window, so the only S-named instants in [a, b] are a and b; an earlier move ends at an
      F exit, never at an S-named instant.  Recorded: whether any earlier move already passes b (it cannot: the cascade
      would have stopped counting there).
Recorded per multi-move pass: chain length; setter repeats; rank / lap words; rank direction of each link; whether
each setter is the lowest-rank blocker (E331's setter relation).
Positions start at 1 (rule 5).  Populations as E929.
"""
import itertools, random, sys
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
SPLIT = "tab = Counter(); ex = {}"
exec(open('wall_window_index_v5.py').read().split(SPLIT)[0])

def f_chain(Fs, a, b):
    t = a; out = []
    while True:
        bl = [r for r in Fs if blocked(r, t)]
        if not bl: return out, False, t
        m = max(nxt(r, t) for r in bl)
        s = min(r for r in bl if nxt(r, t) == m)
        k = floor(s * t + E)
        out.append((s, k, t, m, min(bl) == s))
        t = m
        if t > b: return out, True, t

def covered(Fs, a, b):
    """Independent of the cascade: is [a, b] inside the union of F's open zones?  Interval merge."""
    zs = []
    for f in Fs:
        for k in range(max(1, floor(f * a) - 1), floor(f * b) + 2):
            lo, hi = Fr(8 * k - 1, 8) / f, Fr(8 * k + 1, 8) / f
            if hi > a and lo <= b: zs.append((lo, hi))
    zs.sort(); cur = a
    for lo, hi in zs:
        if lo >= cur: return False          # cur lies in no open zone: an F-clear instant in [a, b]
        if hi > cur: cur = hi
        if cur > b: return True
    return cur > b

tab = Counter(); ex = {}; wd = {}
def note(key, item=None):
    tab[key] += 1
    if item is not None and key not in ex: ex[key] = item

def case(pop, rs, label):
    rs = sorted(rs); d = rs[0]; t0 = E / d
    S = [r for r in rs if r <= 7 * d]; Fs = [r for r in rs if r > 7 * d]
    if not Fs: return
    T, _ = cascade(rs, t0)
    ws = windows(S, t0, T + 1)
    i = next(k for k, (a, b, o) in enumerate(ws) if a <= T <= b)
    for j in range(i + 1):
        a, b, o = ws[j]
        ch, passed, st = f_chain(Fs, a, b)
        cov = covered(Fs, a, b)
        note((pop, 'check (3): pass == covered', passed == cov),
             None if passed == cov else (label, [str(x) for x in rs], j))
        for n, (s, k, t, m, low) in enumerate(ch):
            note((pop, 'check (1): exit == (8k+1)/(8f)', m == Fr(8 * k + 1, 8) / s))
            if n:
                s0, k0 = ch[n - 1][0], ch[n - 1][1]
                note((pop, 'check (2): consecutive ratio condition',
                      Fr(8 * k - 1, 8 * k0 + 1) < s / s0 < Fr(8 * k + 1, 8 * k0 + 1)))
        if not passed or len(ch) < 2: continue
        rk = [Fs.index(s) + 1 for s, *_ in ch]; laps = [k for s, k, *_ in ch]
        word = tuple(zip(rk, laps))
        wd.setdefault(pop, Counter())[word] += 1
        note((pop, 'multi', 'length %s' % (len(ch) if len(ch) < 5 else '>=5')))
        rep = len(set(rk)) < len(rk)
        note((pop, 'multi', 'setter repeats' if rep else 'setters distinct'),
             (label, [str(x) for x in rs], word) if rep else None)
        dirs = ''.join('+' if rk[n] > rk[n - 1] else ('-' if rk[n] < rk[n - 1] else '=') for n in range(1, len(rk)))
        note((pop, 'multi', 'rank directions %s' % dirs), (label, [str(x) for x in rs], word))
        note((pop, 'multi', 'laps %s' % '-'.join(map(str, laps))))
        note((pop, 'multi', 'every setter = lowest-rank blocker' if all(c[4] for c in ch) else 'some setter not lowest-rank'))
        note((pop, 'multi', '(4) an earlier move passes b' if any(ch[n][3] > b for n in range(len(ch) - 1))
              else '(4) no earlier move passes b'))

def readings(v, k):
    return [abs(v[i] - v[k]) for i in range(len(v)) if i != k]
for v in itertools.combinations(range(1, 17), 8):
    for k in range(8): case('Z16', [Fr(x) for x in readings(v, k)], (v, k))
rng = random.Random(1)
for _ in range(3000):
    gaps = [Fr(rng.randint(6, 24), 12) for _ in range(7)]
    v = [Fr(1)]
    for g in gaps: v.append(v[-1] + g)
    for k in range(8): case('Q', readings(v, k), ([str(g) for g in gaps], k))
rng = random.Random(6); seen = 0
while seen < 2900:
    others = sorted(set(Fr(rng.randint(13, 480), 12) for _ in range(6)))
    if len(others) < 6: continue
    seen += 1; case('W40', [Fr(1)] + others, seen)

for kk, vv in sorted(tab.items(), key=lambda x: str(x[0])):
    print(vv, kk)
    if kk in ex: print('      e.g.', ex[kk])
for p, cw in wd.items():
    print(p, 'distinct (rank, lap) words:', len(cw), 'most common:', cw.most_common(8))
