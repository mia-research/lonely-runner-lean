# E645: correlation of exact chain length with y0, 1/w, smax, longest run of consecutive readings, number of windows (chain_data_N12_v1.out).
import csv, math, statistics as st
from fractions import Fraction as F
R = []
for r in csv.DictReader(open('chain_data_N12_v1.out'), delimiter='|'):
    core = tuple(map(int, r['core'].split(',')))
    R.append((core, int(r['chain']), float(F(r['y0'])), float(F(r['w'])), int(r['nwindows']), eval(r['runs']), r['in53'] == '1'))
def corr(x, y):
    mx, my = st.mean(x), st.mean(y)
    return sum((a - mx) * (b - my) for a, b in zip(x, y)) / math.sqrt(sum((a - mx) ** 2 for a in x) * sum((b - my) ** 2 for b in y))
ch = [r[1] for r in R]
print('sets', len(R), 'in the 53:', sum(r[6] for r in R))
for nm, f in [('y0', lambda r: r[2]), ('1/w', lambda r: 1 / r[3]), ('smax', lambda r: max(r[0])), ('longest run', lambda r: max(r[5])), ('nwindows', lambda r: r[4])]:
    print('corr(chain,', nm, ') =', round(corr([f(r) for r in R], ch), 3))
for tag, sel in [('53 cores', [r for r in R if r[6]]), ('others', [r for r in R if not r[6]])]:
    print(tag, len(sel), 'mean chain', round(st.mean(r[1] for r in sel), 2), 'max', max(r[1] for r in sel), 'mean y0', round(st.mean(r[2] for r in sel), 1), 'mean longest run', round(st.mean(max(r[5]) for r in sel), 2))
