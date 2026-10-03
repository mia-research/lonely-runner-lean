# sigpair_analyse_v1 -- aggregate sigpair_res_J{J}_v1.jsonl: pair feasibility counts, member checks, target pairs.
import sys, json, pickle, collections
sys.path.insert(0, '.')
from fractions import Fraction as F
J = int(sys.argv[1])
R = {}
for line in open(f'sigpair_res_J{J}_v1.jsonl'):
    r = json.loads(line); R[r['i']] = r
T = pickle.load(open(f'terminals5_J{J}.pkl', 'rb')); M = dict(pickle.load(open(f'cell_members_J{J}.pkl', 'rb')))
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
print('J', J, 'cells', len(T), 'results', len(R), 'errors', sum(1 for r in R.values() if 'error' in r))
FEAS = ('FE', 'FO', 'FD')
cnt = collections.Counter(st for r in R.values() if 'status' in r for st in r['status'].values())
print('status counts over (cell, closer):', dict(cnt))
# per pair: cells with each status
pair = collections.defaultdict(collections.Counter)
for r in R.values():
    if 'status' not in r: continue
    for c, st in r['status'].items(): pair[(r['opener'], int(c) + 1)][st] += 1
print('pair table (opener, closer): cells FE | FE+FO+FD | TB | TIE | TOUCH | BUDGET')
feas_pairs = set(); fe_pairs = set()
for o in range(1, 8):
    for c in range(1, 8):
        d = pair[(o, c)]; f = sum(d[s] for s in FEAS)
        print((o, c), d['FE'], f, d['TB'], d['TIE'], d['TOUCH'], d['BUDGET'])
        if f: feas_pairs.add((o, c))
        if d['FE']: fe_pairs.add((o, c))
print('pairs with an exact certificate (FE/FO/FD):', len(feas_pairs), 'missing:', sorted({(o, c) for o in range(1, 8) for c in range(1, 8)} - feas_pairs))
# member check
mem_pairs = collections.Counter(); bad = []; nmem = 0
for i, rho in M.items():
    o = outcome(rho); pr = (o['opener'][0], o['closer'][0]); mem_pairs[pr] += 1; nmem += 1
    st = R[i]['status'][str(pr[1] - 1)] if i in R and 'status' in R[i] else 'NA'
    if R[i]['opener'] != pr[0] or st not in ('FE', 'FO', 'FD', 'TB'): bad.append((i, pr, st, R[i]['opener']))
print('members', nmem, 'member-pair set', len(mem_pairs), 'member pair not feasible in own cell / opener mismatch:', len(bad), bad[:10])
print('pairs feasible by LP/cert but no member:', sorted(feas_pairs - set(mem_pairs)))
print('member pairs with no feasible cell:', sorted(set(mem_pairs) - feas_pairs))
# cells with no member
nom = [i for i in R if i not in M]
print('cells without member', len(nom), 'pairs feasible only in such cells:')
withm = set(); only = collections.Counter()
for i, r in R.items():
    if 'status' not in r: continue
    for c, st in r['status'].items():
        if st in FEAS and i in M: withm.add((r['opener'], int(c) + 1))
for i in nom:
    r = R[i]
    for c, st in r['status'].items():
        if st in FEAS and (r['opener'], int(c) + 1) not in withm: only[(r['opener'], int(c) + 1)] += 1
print(dict(only))
pickle.dump(dict(pair={k: dict(v) for k, v in pair.items()}, feas=sorted(feas_pairs), members=dict(mem_pairs)), open(f'sigpair_summary_J{J}_v1.pkl', 'wb'))
