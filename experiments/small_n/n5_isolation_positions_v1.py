"""n=5, the predictor's isolation: at R_final (the cascade's end, t = R_final/(5 d_min)), each runner's position in fifths
of a lap relative to the subject: p_x = s_x * R_final mod 5, in [1, 4].  For arrangements with R_final > 3 (annealed,
exact): the flank runner (p = 1 exactly, the last setter), the other positions, their AP index residues and deviations;
distribution of the positions; the nearest runner's own position is R_final itself."""
from fractions import Fraction as F
import math, random, collections
from multiprocessing import Pool
def near(x): return math.floor(x + F(1, 2))
def cascade(s):
    R = F(1); last = None
    while True:
        best = R; who = None
        for i, sx in enumerate(s):
            v = sx * R; N = near(v / 5)
            if abs(v - 5 * N) < 1:
                c = F(5 * N + 1) / sx
                if c > best: best, who = c, (i, N)
        if who is None: return R, last
        R = best; last = who
def job(seed):
    rng = random.Random(seed); found = []
    for restart in range(30):
        cur = sorted(1 + F(rng.randint(0, 12000), 1000) for _ in range(3)); cs = cascade(cur)[0]
        for it in range(1500):
            sc = [F(1, 10), F(1, 100), F(1, 1000)][it * 3 // 1500]
            new = sorted(max(F(1), x + sc * F(rng.randint(-100, 100), 100)) for x in cur)
            if len(set(new)) < 3: continue
            ns = cascade(new)[0]
            if ns >= cs or rng.random() < 0.02: cur, cs = new, ns
            if cs > 3: found.append(tuple(cur))
    return found
if __name__ == '__main__':
    with Pool() as p: arrs = set(x for r in p.map(job, range(32)) for x in r)
    print('arrangements with R > 3:', len(arrs))
    flankside = collections.Counter(); pos_hist = collections.Counter(); pattern = collections.Counter(); ex = {}
    gapmin = F(10)
    for s in arrs:
        R, last = cascade(list(s))
        ps = sorted((s[i] * R - 5 * math.floor(s[i] * R / 5), i) for i in range(3))
        allpos = sorted([R] + [p for p, _ in ps])   # nearest at R (fifths) plus the three others
        for p, i in ps:
            pos_hist[math.floor(p * 4) / 4] += 1
        # pattern: which positions are exactly at a threshold (1 or 4)
        exact = tuple(sorted(('flank+' if p == 1 else 'flank-' if p == 4 else 'free') for p, _ in ps))
        pattern[exact] += 1
        # spacing of all four positions on [1,4]
        gaps = [b - a for a, b in zip(allpos, allpos[1:])]
        gapmin = min(gapmin, min(gaps))
        key = exact
        if key not in ex or R > ex[key][0]: ex[key] = (R, [float(x) for x in s], [float(p) for p in allpos])
    print('threshold pattern of the three other runners at isolation (flank+ = exactly 1/5 ahead, flank- = exactly 1/5 behind):')
    for k, c in pattern.most_common(): print('   ', k, c, ' highest R example:', f'R={float(ex[k][0]):.4f}', 'readings', [round(x, 4) for x in ex[k][1]], 'positions incl. nearest', [round(x, 4) for x in ex[k][2]])
    print('positions of the other runners at isolation (fifths, binned by 1/4):', dict(sorted(pos_hist.items())))
    print('smallest spacing between consecutive positions (nearest included) at isolation:', float(gapmin))
