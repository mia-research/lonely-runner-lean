# sigpair_allpairs_v1 -- python3 sigpair_allpairs_v1.py J part nparts [seconds]
# For each of the 49 (opener rank o, closer rank c) pairs (part::nparts of them): scan the path-prefix nodes of opener rank o, exact decision per node
# (decide_node), stopping at the first exact witness (FEAS).  A pair with no witness after every node is reported with the verdict counts.
# Resumable: state in sigpair_allpairs_J{J}_state_p{part}of{nparts}_v1.json
import sys, json, pickle, time, os
sys.path.insert(0, '.')
from sigpair_exact_v1 import *
J, part, nparts = [int(x) for x in sys.argv[1:4]]; LIMIT = float(sys.argv[4]) if len(sys.argv) > 4 else 500
NODES = pickle.load(open(f'sigpair_nodes_J{J}_v1.pkl', 'rb'))
by = {o: [p for p in NODES if p[-1][0] == o] for o in range(1, 8)}
PAIRS = [(o, c) for o in range(1, 8) for c in range(1, 8)][part::nparts]
SF = f'sigpair_allpairs_J{J}_state_p{part}of{nparts}_v1.json'
state = json.load(open(SF)) if os.path.exists(SF) else {}
t0 = time.time()
for (o, c) in PAIRS:
    k = f'{o},{c}'
    st = state.setdefault(k, {'idx': 0, 'counts': {}, 'done': False, 'witness': None, 'total': len(by[o])})
    while not st['done']:
        if time.time() - t0 > LIMIT: break
        if st['idx'] >= len(by[o]): st['done'] = True; break
        p = by[o][st['idx']]; st['idx'] += 1
        v, s, nlp = decide_node(p, J, c - 1)
        st['counts'][v] = st['counts'].get(v, 0) + 1
        if v == 'FEAS':
            st['witness'] = dict(path=[list(x) for x in p], arr=[str(x) for x in s['feas'][0]], path_equal=s['feas'][1], nodes_scanned=st['idx']); st['done'] = True
        if st['idx'] % 200 == 0: json.dump(state, open(SF, 'w'))
    json.dump(state, open(SF, 'w'))
    if time.time() - t0 > LIMIT: break
print('state saved; pairs done:', sum(1 for v in state.values() if v['done']), 'of', len(PAIRS))
