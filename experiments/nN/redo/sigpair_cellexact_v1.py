# sigpair_cellexact_v1 -- python3 sigpair_cellexact_v1.py J set part nparts [seconds]
# exact verdict of the 7 pairs (opener rank of the cell, closer c) in each tree cell, region = path class intersected with the cell's stored box (relaxed by exactly 1e-9).
# set = nomember (cells without exact member) | member | all
import sys, json, pickle, time, os
sys.path.insert(0, '.')
from sigpair_exact_v1 import *
J = int(sys.argv[1]); which = sys.argv[2]; part, nparts = int(sys.argv[3]), int(sys.argv[4]); LIMIT = float(sys.argv[5]) if len(sys.argv) > 5 else 500
T = pickle.load(open(f'terminals5_J{J}.pkl', 'rb')); M = set(i for i, _ in pickle.load(open(f'cell_members_J{J}.pkl', 'rb')))
ids = [i for i in range(len(T)) if (which == 'all' or (which == 'nomember') == (i not in M))][part::nparts]
OUT = f'sigpair_cellexact_J{J}_{which}_p{part}of{nparts}_v1.jsonl'
done = set()
if os.path.exists(OUT):
    for l in open(OUT): done.add(json.loads(l)['i'])
todo = [i for i in ids if i not in done]
print('cells', len(ids), 'done', len(done), 'todo', len(todo), flush=True)
t0 = time.time(); n = 0
with open(OUT, 'a') as f:
    for i in todo:
        p, lo_, hi_, box, w = T[i]; p = tuple(tuple(x) for x in p)
        cell = Cell(p, box, J); S = setup(cell); lo, hi = exact_bounds(cell); vs = ''; arr = {}
        for c in range(7):
            v, st, nlp = decide_exact(p, box, J, c, 3000, shared=(cell, S, lo, hi))
            vs += {'FEAS': 'F', 'INF': 'I', 'BUDGET': 'B', 'UNCERT': 'U'}[v]
            if v == 'FEAS': arr[str(c + 1)] = [str(x) for x in st['feas'][0]]
        f.write(json.dumps(dict(i=i, o=p[-1][0], v=vs, arr=arr)) + '\n'); n += 1
        if n % 50 == 0: f.flush()
        if time.time() - t0 > LIMIT: break
print('this run', n, 'cells', round(time.time() - t0), 's', flush=True)
