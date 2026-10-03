# sigpair_scan_v1 -- python3 sigpair_scan_v1.py J o c seed seconds [order]
# exact decision of pair (o, c) over path-prefix nodes with opener rank o, in a shuffled order, until the first exact witness or the deadline; resumable via jsonl.
import sys, json, pickle, random, time, os
sys.path.insert(0, '.')
from sigpair_exact_v1 import *
J, o, c, seed = [int(x) for x in sys.argv[1:5]]; LIMIT = float(sys.argv[5]); order = sys.argv[6] if len(sys.argv) > 6 else 'shuffle'
N = [p for p in pickle.load(open(f'sigpair_nodes_J{J}_v1.pkl', 'rb')) if p[-1][0] == o]
if order == 'shuffle': random.Random(seed).shuffle(N)
OUT = f'sigpair_scan_J{J}_o{o}_c{c}_v1.jsonl'
done = set()
if os.path.exists(OUT):
    for l in open(OUT): done.add(tuple(tuple(x) for x in json.loads(l)['path']))
    for l in open(OUT):
        if json.loads(l)['verdict'] == 'FEAS': print('witness already recorded'); sys.exit(0)
todo = [p for p in N if p not in done]
print('opener', o, 'closer', c, 'nodes', len(N), 'done', len(done), 'todo', len(todo), flush=True)
t0 = time.time(); n = 0
with open(OUT, 'a') as f:
    for p in todo:
        v, st, nlp = decide_node(p, J, c - 1, node_budget=3000)
        rec = dict(path=[list(x) for x in p], verdict=v, nodes=st['nodes'], npass=st['pass'], uncert=st['uncert'])
        if st['feas']: rec['arr'] = [str(x) for x in st['feas'][0]]; rec['path_equal'] = st['feas'][1]
        f.write(json.dumps(rec) + '\n'); f.flush(); n += 1
        if v == 'FEAS': print('FEAS after', n, 'nodes'); break
        if time.time() - t0 > LIMIT: break
print('this run', n, 'nodes', round(time.time() - t0), 's', flush=True)
