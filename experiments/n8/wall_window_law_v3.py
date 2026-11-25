"""Wall-window law, test v3 (2026-11-25): v1 plus, for each miss, the landing setter (group S or F), its lap j (setter*T = j + 1/8), whether T = TF, and the S readings in the way at TF.  Exact Fractions; the cascade is the oracle.

Candidate rule, named from the readings before the landing is computed:
  r_1 <= ... <= r_7 the readings of a subject (positive; |v_i - v_k|), d = r_1.
  S = readings r <= 7 d (the ratio wall 7), F = the rest.
  Every reading of S is clear at t0 = 1/(8d) (its position r/(8d) lies in [1/8, 7/8]), so S's clear component at t0 is
  W = [t0, 7/(8 max S)]  (first entry of the fastest S reading; the other S readings enter later).
  Law: the landing T is the cascade of F alone started at t0, and it lies in W.
Forced by the definitions (not tested): F empty => T = t0.  If F's cascade from t0 fixes at a point of W, that point is
T (ChainCarried.chain_landing, E757 [L]: S is lonely on W and every earlier instant >= t0 has an F reading in the way).
Tested: that F's cascade from t0 fixes inside W.  Every miss is listed by kind for rule 22.
Populations:
  Z16: every 8-subset of {1..16}, every subject (E926's population).
  Q:   seeded random consecutive gaps a/12, 6 <= a <= 24, 3,000 arrangements, every subject (E669's H4).
  W40: seeded sets 1 < others in (1,40], k/12 grid (E672's W), 2,900 sets as readings.
"""
import itertools, random, sys
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter

E = Fr(1, 8)

def blocked(r, t):
    x = r * t
    f = x - floor(x)
    return f < E or f > 1 - E

def nxt(r, t):
    # leaving edge of the blocked interval of r containing t
    return (ceil(r * t - E) + E) / r

def cascade(rs, t, cap=100000):
    setters = []
    for _ in range(cap):
        b = [r for r in rs if blocked(r, t)]
        if not b:
            return t, setters
        m = max(nxt(r, t) for r in b)
        setters.append(min(r for r in b if nxt(r, t) == m))
        t = m
    raise RuntimeError('cap')

def lonely(rs, t):
    return not any(blocked(r, t) for r in rs)

tab = Counter(); miss = Counter(); ex = {}
def case(pop, rs, label):
    rs = sorted(rs)
    d = rs[0]
    t0 = Fr(1, 8) / d
    S = [r for r in rs if r <= 7 * d]
    Fs = [r for r in rs if r > 7 * d]
    T, st = cascade(rs, t0)
    assert lonely(rs, T)
    Wr = Fr(7, 8) / max(S)
    if not Fs:
        assert T == t0
        tab[(pop, 'F empty: T = t0')] += 1
        return
    TF, stF = cascade(Fs, t0)
    if TF <= Wr:
        assert TF == T, (pop, label)
        tab[(pop, 'law holds: F cascade fixes in W')] += 1
        tab[(pop, 'law holds, F moves %s' % ('0' if not stF else '>=1'))] += 1
    else:
        tab[(pop, 'MISS: F cascade passes W')] += 1
        s_ = st[-1]
        j = s_ * T - E
        assert j == int(j)
        grp = 'S' if s_ in S else 'F'
        blockS = [r for r in S if blocked(r, TF)]
        idxS = sorted(S.index(r) + 1 for r in blockS)  # 1 = slowest
        fastest_only = (blockS == [max(S)])
        key = (pop, 'T=TF' if T == TF else 'T!=TF', 'setter in %s' % grp, 'lap %d' % min(int(j), 3) if grp == 'S' else 'F lap',
               'S blockers at TF: fastest S only' if fastest_only else 'S blockers at TF: ranks %s of %d' % (idxS, len(S)))
        miss[key] += 1
        ex.setdefault(key, []).append((label, [str(r) for r in rs], 'T=' + str(T), 'TF=' + str(TF), 'W=' + str(Wr)))

def readings(v, k):
    return [abs(v[i] - v[k]) for i in range(len(v)) if i != k]

pops = sys.argv[1:] or ['Z16', 'Q', 'W40']
if 'Z16' in pops:
    for v in itertools.combinations(range(1, 17), 8):
        for k in range(8):
            case('Z16', [Fr(x) for x in readings(v, k)], (v, k))
if 'Q' in pops:
    rng = random.Random(1)
    for _ in range(3000):
        gaps = [Fr(rng.randint(6, 24), 12) for _ in range(7)]
        v = [Fr(0)]
        for g in gaps: v.append(v[-1] + g)
        for k in range(8):
            case('Q', readings(v, k), ([str(g) for g in gaps], k))
if 'W40' in pops:
    rng = random.Random(6)
    seen = 0
    while seen < 2900:
        others = sorted(set(Fr(rng.randint(13, 480), 12) for _ in range(6)))
        if len(others) < 6: continue
        seen += 1
        case('W40', [Fr(1)] + others, seen)

for kk, vv in sorted(tab.items()): print(vv, kk)
print('misses:')
for kk, vv in sorted(miss.items()):
    print('  ', vv, kk)
    for e in ex[kk][:3]: print('      e.g.', e)
