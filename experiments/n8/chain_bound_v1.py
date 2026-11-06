# E645: exact lower bound chain >= ceil((y0 - 3/8)/Lmax), Lmax = longest single piece (any window, any shift n<80, any k with a <= y0); compared with the exact greedy chain.
import csv, math
from multiprocessing import Pool
from fractions import Fraction as F
from chain_lo_v1 import win
def job(row):
    core, chain = row
    J, T = win(core)
    jw = max(J, key=lambda w: w[1] - w[0]); y0 = 1 / (4 * (jw[1] - jw[0]))
    L = F(0); arg = None
    for lo, hi in J:
        for n in range(0, 80):
            d = F(n) * T
            if hi + d == 0: continue
            k = 0
            while F(8 * k + 1, 8) / (hi + d) <= y0:
                ln = F(8 * k + 7, 8) / (lo + d) - F(8 * k + 1, 8) / (hi + d)
                if ln > L: L = ln; arg = (lo, hi, n, k)
                k += 1
    b = math.ceil((y0 - F(3, 8)) / L)
    return core, chain, b, float(L), arg[2], float(y0)
if __name__ == '__main__':
    rows = []
    for r in csv.DictReader(open('chain_data_N12_v1.out'), delimiter='|'):
        rows.append((tuple(map(int, r['core'].split(','))), int(r['chain']), r['in53'] == '1'))
    with Pool(10) as p: res = p.map(job, [(c, ch) for c, ch, _ in rows], chunksize=8)
    import pickle; pickle.dump(res, open('chain_bound_v1.pkl', 'wb'))
    in53 = {c for c, _, f in rows if f}
    viol = [r for r in res if r[1] < r[2]]
    print('sets', len(res), 'chain < bound (violations of the derived bound):', len(viol))
    from chain_lo_v1 import win as _w
    def runs(core):
        s = sorted(core); best = cur = 1
        for a, b in zip(s, s[1:]):
            cur = cur + 1 if b == a + 1 else 1; best = max(best, cur)
        return best
    def med(xs): xs = sorted(xs); return xs[len(xs) // 2]
    y0of = {r[0]: F(r[5]).limit_denominator(10**6) if False else None for r in res}
    for tag, sel in [('53 cores', [r for r in res if r[0] in in53]), ('others', [r for r in res if r[0] not in in53])]:
        q = sorted(F(r[1], r[2]) for r in sel)
        print(tag, len(sel), 'chain/bound exact: min', q[0], 'median', q[len(q) // 2], 'max', q[-1], '; sum of chains', sum(r[1] for r in sel), '; sum of longest runs', sum(runs(r[0]) for r in sel), '; longest piece at shift n != 0:', sum(1 for r in sel if r[4] != 0))
    for r in sorted([r for r in res if r[0] in in53], key=lambda r: -F(r[1], r[2]))[:4]: print(r)
    # exact lo_min median and y0 sum
    from fractions import Fraction
    lo = {}
    for c, _, f in rows:
        J, T = _w(c); lo[c] = (min(J)[0], 1 / (4 * (max(J, key=lambda w: w[1] - w[0])[1] - max(J, key=lambda w: w[1] - w[0])[0])), f)
    for tag, f in [('53 cores', True), ('others', False)]:
        xs = [v for v in lo.values() if v[2] == f]
        print(tag, 'lo_min median exact', med([v[0] for v in xs]), '; sum of y0 exact', sum(v[1] for v in xs), 'over', len(xs))
