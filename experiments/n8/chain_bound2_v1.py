# E822: sharper exact lower bound.  A piece starting at a <= cur ends at most at cur + Lmax(cur), Lmax(y) = longest piece starting at or below y; so the chain has at least as many pieces as the steps of cur -> cur + Lmax(cur) from 3/8 to y0.
import csv, pickle
from multiprocessing import Pool
from fractions import Fraction as F
from chain_lo_v1 import win
def job(row):
    core, chain = row
    J, T = win(core)
    jw = max(J, key=lambda w: w[1] - w[0]); y0 = 1 / (4 * (jw[1] - jw[0]))
    cand = []
    for lo, hi in J:
        for n in range(0, 80):
            d = F(n) * T
            if hi + d == 0: continue
            k = 0
            while F(8 * k + 1, 8) / (hi + d) <= y0:
                a = F(8 * k + 1, 8) / (hi + d); b = F(8 * k + 7, 8) / (lo + d); cand.append((a, b - a)); k += 1
    cand.sort()
    cur = F(3, 8); steps = 0; i = 0; L = F(0)
    while cur < y0:
        while i < len(cand) and cand[i][0] <= cur:
            if cand[i][1] > L: L = cand[i][1]
            i += 1
        if L == 0: return core, chain, None, y0
        cur += L; steps += 1
    return core, chain, steps, y0
if __name__ == '__main__':
    rows = [(tuple(map(int, r['core'].split(','))), int(r['chain']), r['in53'] == '1') for r in csv.DictReader(open('chain_data_N12_v1.out'), delimiter='|')]
    with Pool(10) as p: res = p.map(job, [(c, ch) for c, ch, _ in rows], chunksize=8)
    pickle.dump(res, open('chain_bound2_v1.pkl', 'wb'))
    in53 = {c for c, _, f in rows if f}
    print('sets', len(res), 'bound2 none:', sum(1 for r in res if r[2] is None), 'violations (chain < bound2):', sum(1 for r in res if r[2] is not None and r[1] < r[2]))
    for tag, sel in [('53 cores', [r for r in res if r[0] in in53]), ('others', [r for r in res if r[0] not in in53])]:
        q = sorted(F(r[1], r[2]) for r in sel if r[2])
        print(tag, len(sel), 'chain/bound2 exact: min', q[0], 'median', q[len(q) // 2], 'max', q[-1], '; chain equals bound2 in', sum(1 for r in sel if r[1] == r[2]), '; chain - bound2 max', max(r[1] - r[2] for r in sel))
