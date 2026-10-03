# sigpair_exact_run_v1 -- python3 sigpair_exact_run_v1.py J opener closer [seconds]  : exact decision of pair (opener, closer) over every cell with that opener rank
import sys, json, pickle, time, os
sys.path.insert(0, '.')
from sigpair_exact_v1 import *
J = int(sys.argv[1]); o = int(sys.argv[2]); c = int(sys.argv[3]); LIMIT = float(sys.argv[4]) if len(sys.argv) > 4 else 500
T = pickle.load(open(f'terminals5_J{J}.pkl', 'rb'))
OUT = f'sigpair_exact_J{J}_o{o}_c{c}_v1.jsonl'
done = set()
if os.path.exists(OUT):
    for l in open(OUT): done.add(json.loads(l)['i'])
todo = [i for i, t in enumerate(T) if t[0][-1][0] == o and i not in done]
print('cells with opener', o, ':', sum(1 for t in T if t[0][-1][0] == o), 'done', len(done), 'todo', len(todo), flush=True)
t0 = time.time()
with open(OUT, 'a') as f:
    for i in todo:
        p, lo_, hi_, box, w = T[i]
        v, st, nlp = decide_exact(p, box, J, c - 1)
        rec = dict(i=i, verdict=v, nodes=st['nodes'], cert_closed=st['cert_closed'], cert_strict=st['cert_strict'], interval=st['interval'], uncert=st['uncert'], nlp=nlp)
        if st['feas']: rec['arr'] = [str(x) for x in st['feas'][0]]; rec['path_equal'] = st['feas'][1]
        f.write(json.dumps(rec) + '\n')
        if time.time() - t0 > LIMIT: break
    f.flush()
print('done this run', time.time() - t0)
