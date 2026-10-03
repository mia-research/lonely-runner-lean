# sigpair_node_run_v1 -- python3 sigpair_node_run_v1.py J opener closer part nparts [seconds]
# EXACT decision of pair (opener, closer) over the landing region L(P) of every path-prefix node P of the J-window tree whose last setter has rank `opener`.
# (Terminal cells only record nodes with no children; the landing region of an internal node is not in terminals5.)
import sys, json, pickle, time, os
sys.path.insert(0, '.')
from sigpair_exact_v1 import *
J, o, c, part, nparts = [int(x) for x in sys.argv[1:6]]; LIMIT = float(sys.argv[6]) if len(sys.argv) > 6 else 500
N = [p for p in pickle.load(open(f'sigpair_nodes_J{J}_v1.pkl', 'rb')) if p[-1][0] == o]
N = N[part::nparts]
OUT = f'sigpair_node_J{J}_o{o}_c{c}_p{part}of{nparts}_v1.jsonl'
done = set()
if os.path.exists(OUT):
    for l in open(OUT): done.add(tuple(tuple(x) for x in json.loads(l)['path']))
todo = [p for p in N if p not in done]
print('nodes', len(N), 'done', len(done), 'todo', len(todo), flush=True)
t0 = time.time(); n = 0
with open(OUT, 'a') as f:
    for p in todo:
        v, st, nlp = decide_node(p, J, c - 1)
        rec = dict(path=[list(x) for x in p], verdict=v, nodes=st['nodes'], cert_closed=st['cert_closed'], cert_strict=st['cert_strict'], interval=st['interval'], uncert=st['uncert'], box_cert=st['box_cert'], box_fail=st['box_fail'], nlp=nlp, npass=st['pass'])
        if st['feas']: rec['arr'] = [str(x) for x in st['feas'][0]]; rec['path_equal'] = st['feas'][1]
        f.write(json.dumps(rec) + '\n'); n += 1
        if n % 50 == 0: f.flush()
        if time.time() - t0 > LIMIT: break
print('this run', n, 'nodes in', round(time.time() - t0), 's', flush=True)
