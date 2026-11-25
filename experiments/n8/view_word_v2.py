"""View words, test v2 (2026-11-25): v1 with the winding dropped.  Exact Fractions; the cascade is the oracle.
A path letter is the new setter's residue n mod 8 on the grid through the old setter (E747), with the side of its
deviation (sign of eps: '+', '-', '0'); a RUN-COMPRESSED path word replaces each maximal run of one letter by the letter
with '*'.  Counted per population: distinct letters, distinct raw words, distinct compressed words, shared sets, and
which letters occur at the first move (the start (8*0+1)/(8 d_min), M = 0).
"""
import sys
exec(open('view_word_v1.py').read().split("st = {}")[0])
from collections import Counter
import itertools, random
def cascade2(rs):
    d = min(rs); t = E / d; p, M = d, 0; path = []
    while True:
        bl = [r for r in rs if blocked(r, t)]
        if not bl: return t, path
        m = max(ex(r, t) for r in bl); s = min(r for r in bl if ex(r, t) == m)
        n, e = view(s, p)
        path.append('%d%s' % (n % 8, '+' if e > 0 else ('-' if e < 0 else '0')))
        p, M, t = s, floor(s * m), m
def compress(w):
    out = []
    for x in w:
        if out and out[-1].rstrip('*') == x: out[-1] = x + '*'
        else: out.append(x)
    return tuple(out)
def readings(v, k): return [abs(v[i] - v[k]) for i in range(len(v)) if i != k]
st = {}
def case(pop, rs):
    T, path = cascade2(sorted(rs))
    s = st.setdefault(pop, dict(L=Counter(), first=Counter(), raw=Counter(), comp=Counter()))
    for x in path: s['L'][x] += 1
    if path: s['first'][path[0]] += 1
    s['raw'][tuple(path)] += 1; s['comp'][compress(path)] += 1
pops = sys.argv[1:]
if 'Z16' in pops:
    for v in itertools.combinations(range(1, 17), 8):
        for k in range(8): case('Z16', [Fr(x) for x in readings(v, k)])
if 'Q' in pops:
    rng = random.Random(1)
    for _ in range(3000):
        gaps = [Fr(rng.randint(6, 24), 12) for _ in range(7)]
        v = [Fr(1)]
        for g in gaps: v.append(v[-1] + g)
        for k in range(8): case('Q', readings(v, k))
for H, seed in ((40, 6), (80, 7), (160, 8), (320, 9)):
    if 'W%d' % H not in pops: continue
    rng = random.Random(seed); seen = 0
    while seen < 2900:
        others = sorted(set(Fr(rng.randint(13, 12 * H), 12) for _ in range(6)))
        if len(others) < 6: continue
        seen += 1; case('W%d' % H, [Fr(1)] + others)
for pop, s in st.items():
    print(pop, '| letters', len(s['L']), dict(sorted(s['L'].items())))
    print('    first letters', dict(sorted(s['first'].items())))
    print('    raw words', len(s['raw']), '| compressed words', len(s['comp']))
for a, b in itertools.combinations(list(st), 2):
    A, B = set(st[a]['comp']), set(st[b]['comp'])
    print('compressed', a, b, 'shared', len(A & B), '| only', a, len(A - B), '| only', b, len(B - A))
for pop, s in st.items():
    print(pop, 'commonest compressed words:')
    for t, c in s['comp'].most_common(12): print('   ', c, ' '.join(t) or '(none: lands at the start)')
