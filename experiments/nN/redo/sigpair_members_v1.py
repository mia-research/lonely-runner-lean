# sigpair_members_v1 -- exact (opener rank, closer rank) pair set of the J exact cell members; first witness per pair (exact Fractions)
import sys, pickle, json, collections
sys.path.insert(0, '.')
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
J = int(sys.argv[1]); M = pickle.load(open(f'cell_members_J{J}.pkl', 'rb'))
cnt = collections.Counter(); wit = {}
for i, rho in M:
    o = outcome(rho); k = (o['opener'][0], o['closer'][0]) if o['opener'] else None
    cnt[k] += 1
    if k not in wit: wit[k] = (i, [str(x) for x in rho])
print('J', J, 'members', len(M), 'pairs', len([k for k in cnt if k]), 'members with no move', cnt.get(None, 0))
for k in sorted(k for k in cnt if k): print(k, cnt[k])
print('absent:', sorted({(o, c) for o in range(1, 8) for c in range(1, 8)} - set(cnt)))
json.dump({str(k): v for k, v in wit.items()}, open(f'sigpair_members_J{J}_v1.json', 'w'))
