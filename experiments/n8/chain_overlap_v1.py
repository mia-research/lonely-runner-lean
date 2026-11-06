# E822: exact decomposition of a chain: advance = piece length - overlap with what is already covered; which window (least lo, shift 0) each piece belongs to.
import pickle
from fractions import Fraction as F
res = pickle.load(open('chain_pieces_v1.pkl', 'rb'))
import csv
in53 = {tuple(map(int, l.split(','))) for l in open('core_cover_cores.txt') if l.strip()}
def stats(sel, tag):
    tot_len = tot_ov = n = nA = 0; ovA = ovO = F(0)
    for core, T, y0, ch in sel:
        lo_min = min(p[2] for p in ch)  # the least window start used by the chain
        cur = F(3, 8)
        for a, b, lo, hi, d, k in ch:
            ln = b - a; ov = max(F(0), cur - a); tot_len += ln; tot_ov += ov; n += 1
            if lo == lo_min and d == 0: nA += 1; ovA += ov
            else: ovO += ov
            cur = b
    print(tag, 'chains', len(sel), 'pieces', n, 'sum of lengths', tot_len, 'sum of overlaps', tot_ov, '; overlap share of length in [%d/100, %d/100)' % (int(tot_ov * 100 / tot_len), int(tot_ov * 100 / tot_len) + 1), '; pieces of the least-lo window at shift 0:', nA, ' overlap on those', ovA, ' on the others', ovO)
stats([r for r in res if r[0] in in53], '53')
stats([r for r in res if r[0] not in in53 and len(r[3]) >= 5], 'others with chain >= 5')
stats([r for r in res if r[0] not in in53 and len(r[3]) < 5], 'others with chain < 5')
