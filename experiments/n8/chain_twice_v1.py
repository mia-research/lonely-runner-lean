# E822: chain length against 2*(y0 - 3/8)*lo_min (exact Fractions); lo_min = least window start of the core.
import csv, math
from fractions import Fraction as F
from chain_lo_v1 import win
if __name__ == '__main__':
    rows = []
    for r in csv.DictReader(open('chain_data_N12_v1.out'), delimiter='|'):
        core = tuple(map(int, r['core'].split(',')))
        J, T = win(core); lo = min(J)[0]
        y0 = F(r['y0']); ch = int(r['chain'])
        rows.append((core, ch, y0, lo, T, r['in53'] == '1', F(ch) / (2 * (y0 - F(3, 8)) * lo)))
    def summ(sel, tag):
        q = sorted(r[6] for r in sel)
        print(tag, len(sel), 'chain / (2 (y0 - 3/8) lo_min): min', q[0], 'p10', q[len(q) // 10], 'median', q[len(q) // 2], 'p90', q[9 * len(q) // 10], 'max', q[-1])
    summ(rows, 'all'); summ([r for r in rows if r[5]], '53'); summ([r for r in rows if not r[5]], 'others')
    for r in sorted(rows, key=lambda r: r[6])[:4] + sorted(rows, key=lambda r: -r[6])[:6]: print(r[0], 'chain', r[1], 'y0', r[2], 'lo_min', r[3], 'T', r[4], 'ratio', r[6])
