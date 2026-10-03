# tie_integer_law_v1.py -- integer readings: exact residue law for single-point windows, checked on lat1 (5,005 sets, readings {1} u 6 of {2..16}).
# Law: R0 = u/v lowest terms is the instant of a single-point window (R0>1) iff  u odd, no reading rho with (rho*u/v mod 8) in [0,1) u (7,8) ... (clear), some exit reading
# rho_a with v | rho_a, rho_a/v = u (mod 8), some entry reading rho_b with v | rho_b, rho_b/v = -u (mod 8).  (Derivation in tie_structure_v1.md section 4.)
import pickle, glob, itertools
from fractions import Fraction as F
from math import comb
exec(open('win_lib_v1.py').read())
recs = []
for f in glob.glob('win_rec_lat1_*_v1.pkl'): recs += pickle.load(open(f, 'rb'))
viol = 0; npt = 0; byv = {}
for lab, rh0, ws, *_ in recs:
    rh = norm(rh0)
    for w in ws:
        if w[0] != w[1]: continue
        R0 = w[0]; u, v = R0.numerator, R0.denominator; npt += 1
        byv[v] = byv.get(v, 0) + 1
        ex = [r for r in rh if (R0 * r) % 8 == 1]; en = [r for r in rh if (R0 * r) % 8 == 7]
        okk = (u % 2 == 1) and (R0 == 1 or ex) and en
        for r in ex: okk = okk and (r % v == 0) and (int(r / v) % 8 == u % 8)
        for r in en: okk = okk and (r % v == 0) and (int(r / v) % 8 == (-u) % 8)
        if R0 == 1: okk = okk and all(int(r) % 8 == 7 for r in en)
        if not okk: viol += 1
print('lat1 single-point windows checked', npt, 'violations of the residue law', viol, '| by denominator v of R0:', sorted(byv.items()))
# the first-window counts in lat1 from the law: start type iff some reading in {7,15} and none in {8,16}
n_start = comb(13, 6) - comb(11, 6)
print('lat1 sets with a reading in {7,15} and none in {8,16}:', n_start)
# odd-instant pair classes: {1,7} (mod 8) are single points iff a reading = 7 mod 8 and none = 0 mod 8; {3,5} iff readings 3 and 5 (mod 8) both present and none 0 mod 8
c17 = c35 = 0
for lab, rh0, ws, *_ in recs:
    ints = [int(r) for r in norm(rh0)]
    res = {c % 8 for c in ints}
    if 0 in res: continue
    p17 = 7 in res; p35 = (3 in res and 5 in res)
    pts = {w[0] for w in ws if w[0] == w[1]}
    assert (F(7) in pts) == p17 and (F(1) in pts) == p17 and (F(9) in pts) == p17
    assert (F(3) in pts) == p35 and (F(5) in pts) == p35
    c17 += p17; c35 += p35
print('lat1 sets without a multiple of 8: those with points at 1,7 (and 9,15,17,23):', c17, '; at 3,5 (and 11,13,19,21):', c35, '; asserted equal to the residue statements for every set')
