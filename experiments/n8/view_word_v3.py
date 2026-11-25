"""View words v3: print the longest paths with readings, letters, setters and laps (Q and W80), to see what repeats."""
import sys
exec(open('view_word_v1.py').read().split("st = {}")[0])
import itertools, random
def readings(v, k): return [abs(v[i] - v[k]) for i in range(len(v)) if i != k]
def path_full(rs):
    d = min(rs); t = E / d; p, M = d, 0; out = []
    while True:
        bl = [r for r in rs if blocked(r, t)]
        if not bl: return t, out
        m = max(ex(r, t) for r in bl); s = min(r for r in bl if ex(r, t) == m)
        n, e = view(s, p)
        out.append((rs.index(s) + 1, floor(s * m), '%d%s' % (n % 8, '+' if e > 0 else ('-' if e < 0 else '0'))))
        p, M, t = s, floor(s * m), m
cases = []
rng = random.Random(1)
for _ in range(3000):
    gaps = [Fr(rng.randint(6, 24), 12) for _ in range(7)]
    v = [Fr(1)]
    for g in gaps: v.append(v[-1] + g)
    for k in range(8):
        rs = sorted(readings(v, k)); T, pth = path_full(rs); cases.append((len(pth), 'Q', rs, T, pth))
rng = random.Random(7); seen = 0
while seen < 2900:
    others = sorted(set(Fr(rng.randint(13, 960), 12) for _ in range(6)))
    if len(others) < 6: continue
    seen += 1; rs = [Fr(1)] + others; T, pth = path_full(rs); cases.append((len(pth), 'W80', rs, T, pth))
cases.sort(key=lambda c: -c[0])
for L, pop, rs, T, pth in cases[:25]:
    d = rs[0]
    print(pop, L, 'moves | readings/d_min', [str(r / d) for r in rs], '| 8 d_min T =', 8 * d * T)
    print('    (setter rank, lap, letter):', ' '.join('%d.%d.%s' % x for x in pth))
