# sigpair_nodeall_run_v1 -- python3 sigpair_nodeall_run_v1.py J part nparts [seconds]
# exact verdict (FEAS / INF / BUDGET / UNCERT) of the 7 pairs (opener rank of the node, closer c) at every path-prefix node of window J.
import sys, json, pickle, time, os
sys.path.insert(0, '.')
from sigpair_exact_v1 import *
J, part, nparts = [int(x) for x in sys.argv[1:4]]; LIMIT = float(sys.argv[4]) if len(sys.argv) > 4 else 500
N = pickle.load(open(f'sigpair_nodes_J{J}_v1.pkl', 'rb'))[part::nparts]
OUT = f'sigpair_nodeall_J{J}_p{part}of{nparts}_v1.jsonl'
done = set()
if os.path.exists(OUT):
    for l in open(OUT):
        try: done.add(tuple(tuple(x) for x in json.loads(l)['path']))
        except Exception: pass
todo = [p for p in N if p not in done]
print('nodes', len(N), 'done', len(done), 'todo', len(todo), flush=True)
t0 = time.time(); n = 0; seen = set()
with open(OUT, 'a') as f:
    for p in todo:
        res = decide_node_all(p, J)
        rec = dict(path=[list(x) for x in p], o=p[-1][0], v=''.join({'FEAS': 'F', 'INF': 'I', 'BUDGET': 'B', 'UNCERT': 'U'}[res[c][0]] for c in range(7)))
        for c in range(7):
            v, st = res[c]
            if v == 'FEAS' and (p[-1][0], c + 1) not in seen:
                seen.add((p[-1][0], c + 1)); rec.setdefault('arr', {})[str(c + 1)] = [str(x) for x in st['feas'][0]]
        rec['cert'] = sum(res[c][1]['cert_closed'] + res[c][1]['cert_strict'] for c in range(7))
        f.write(json.dumps(rec) + '\n'); n += 1
        if n % 100 == 0: f.flush()
        if time.time() - t0 > LIMIT: break
print('this run', n, 'nodes in', round(time.time() - t0), 's', flush=True)
