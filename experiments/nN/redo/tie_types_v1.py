# tie_types_v1.py -- exact classification of single-point lonely windows (and first-window zero-width landings).
# Criterion (derived in tie_structure_v1.md): for R0>1, [R0,R0] is a window iff every position p_y(R0)=R0*rho_y mod 8 lies in [1,7],
# some reading has p=1 (zone exit at R0) and some reading has p=7 (zone entry at R0). At the start R0=1 only the entry is needed.
# All arithmetic: Fraction. Data: win_rec_*.pkl (windows computed by win_lib_v1.windows, verified there).
import sys, pickle, glob
from fractions import Fraction as F
from collections import Counter, defaultdict
exec(open('win_lib_v1.py').read())
def pos_of(R, r): return (R * r) % 8
def classify(R0, rh):
    ps = [pos_of(R0, r) for r in rh]
    assert all(1 <= p <= 7 for p in ps)
    ex = [(i + 1, int((R0 * r - 1) / 8)) for i, (r, p) in enumerate(zip(rh, ps)) if p == 1]
    en = [(i + 1, int((R0 * r + 1) / 8)) for i, (r, p) in enumerate(zip(rh, ps)) if p == 7]
    return ex, en
def crit(R0, rh):
    ps = [pos_of(R0, r) for r in rh]
    ok = all(1 <= p <= 7 for p in ps)
    return ok and (R0 == 1 or 1 in ps) and 7 in ps
sets = {}
for f in sorted(glob.glob('win_rec_*_v1.pkl')):
    name = f.split('win_rec_')[1].split('_')[0]
    sets.setdefault(name, []).extend(pickle.load(open(f, 'rb')))
out = sys.stdout
agg = {}
for name, recs in sets.items():
    A = Counter(); first = Counter(); pairs = Counter(); ex_small = {}; mism = 0; npt = 0; nmem_pt = 0; nfirst = 0
    kinds = Counter(); integer_all = Counter()
    for rec in recs:
        lab, rh, ws = rec[0], norm(rec[1]), rec[2]
        pts = [w[0] for w in ws if w[0] == w[1]]
        # independent check: every candidate (8j+1)/rho and the start satisfy crit  <=> point window listed
        if pts: nmem_pt += 1
        for k, w in enumerate(ws):
            if w[0] != w[1]: continue
            R0 = w[0]; npt += 1
            if not crit(R0, rh): mism += 1
            ex, en = classify(R0, rh)
            kind = 'start' if R0 == 1 else 'pinch'
            tie = (len(ex), len(en))
            allint = all(r.denominator == 1 for r in rh)
            kinds[(kind, tie, 'int' if allint else 'nonint')] += 1
            if k == 0: first[(kind, tie, 'int' if allint else 'nonint')] += 1; nfirst += 1
            # pair type (rank a lap j exit, rank b lap j' entry)
            if kind == 'pinch':
                for a in ex:
                    for b in en:
                        key = (a, b)
                        pairs[key] += 1
                        sk = (rh[-1], rh)
                        if key not in ex_small or sk < ex_small[key][0]: ex_small[key] = (sk, R0)
            else:
                for b in en:
                    key = (None, b); pairs[key] += 1
                    sk = (rh[-1], rh)
                    if key not in ex_small or sk < ex_small[key][0]: ex_small[key] = (sk, R0)
        # completeness: any candidate point satisfying crit must be a listed point window
        cands = {F(1)} | {F(8 * j + 1) / r for r in rh for j in range(1, 4)}
        listed = set(pts)
        for c in cands:
            if 1 <= c <= 23 and crit(c, rh) and c not in listed:
                # crit true => must be a window of zero width
                mism += 1000
    agg[name] = (len(recs), nmem_pt, npt, nfirst, mism, kinds, first, pairs, ex_small)
    print('DATASET', name, 'members', len(recs), 'members with a point window', nmem_pt, 'point windows', npt, 'first window a point', nfirst, 'criterion mismatches', mism, file=out)
    print('  all point windows by (kind,(#exits,#entries),integer?):', sorted(kinds.items(), key=lambda x: -x[1]), file=out)
    print('  first-window point by same:', sorted(first.items(), key=lambda x: -x[1]), file=out)
pickle.dump({k: (v[0], v[1], v[2], v[3], v[4], dict(v[5]), dict(v[6]), dict(v[7]), v[8]) for k, v in agg.items()}, open('tie_types_v1.pkl', 'wb'))
