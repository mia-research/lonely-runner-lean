"""E124: close the cone list under adversarial search.  Start from the 41 cones; repeatedly search (multi-start, exact) for a
band shape outside every cone; add the lap assignments of its clear components in [1,7] u [9,15]; stop when a full round of
searches finds none.  Writes the final list to band_cones_v1.txt.  Exact."""
import random, re, sys
from fractions import Fraction as F
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
CONES = []
for line in open('band_category_cover_v1.out'):
    m = re.search(r'laps (\S+|\([^)]*\))\s+newly', line)
    if m:
        t = m.group(1); CONES.append(tuple(int(x) for x in (t.strip('()').split(', ') if t.startswith('(') else t)))
def viol(s, cones):
    best = None
    for k in cones:
        v = max((8 * k[i] + 1) * s[j] - (8 * k[j] + 7) * s[i] for i in range(7) for j in range(7))
        if best is None or v < best: best = v
        if best <= 0: return best
    return best
def cats(s):
    out = set()
    for lo, hi in [(F(1), F(7)), (F(9), F(15))]:
        for a, b in clear_set(s, lo, hi):
            m = (a + b) / 2; out.add(tuple(int(x * m // 8) for x in s))
    return out
def search(args):
    seed, cones = args; rnd = random.Random(seed)
    s = [F(1)] + sorted(F(rnd.randrange(1000, 9000), 1000) for _ in range(5)) + [F(rnd.randrange(7000, 9001), 1000)]
    s = [F(1)] + sorted(s[1:])
    if not (7 <= s[6] <= 9): return None
    sc = viol(s, cones)
    for step in range(2500):
        t = list(s); i = rnd.randrange(1, 7); t[i] += F(rnd.randrange(-300, 301), 10000)
        t = [F(1)] + sorted(t[1:])
        if not (t[1] >= 1 and 7 <= t[6] <= 9): continue
        sc2 = viol(t, cones)
        if sc2 >= sc: s, sc = t, sc2
        if sc > 0: return s
    return None
if __name__ == '__main__':
    rnd_round = 0; seed = 0
    with Pool(8) as p:
        while True:
            rnd_round += 1
            found = [s for s in p.map(search, [(seed + i, CONES) for i in range(64)]) if s is not None]; seed += 64
            if not found:
                print("round %d: none escaped in 64 searches; cones = %d" % (rnd_round, len(CONES))); break
            new = set()
            for s in found: new |= cats(s)
            added = [k for k in new if k not in CONES]; CONES += added
            print("round %d: %d escaped; added %d; cones = %d" % (rnd_round, len(found), len(added), len(CONES))); sys.stdout.flush()
            if rnd_round > 40: print("stopping at 40 rounds"); break
    open('band_cones_v1.txt', 'w').write('\n'.join(' '.join(map(str, k)) for k in CONES) + '\n')
