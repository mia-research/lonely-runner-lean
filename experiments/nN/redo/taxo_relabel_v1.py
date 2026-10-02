# taxo_relabel_v1.py -- re-run the independent labeller (opener rule B) on the stored sample; compare with the stored cascade labels.
import pickle, sys
from multiprocessing import Pool
from collections import Counter
from taxo_lib_v1 import *
rows = pickle.load(open('taxo_sample_v1.pkl', 'rb'))
def f(chunk): return [label_conditions(r[1])[0] for r in chunk]
if __name__ == '__main__':
    ch = [rows[i:i + 2000] for i in range(0, len(rows), 2000)]
    with Pool(2) as p: out = [x for part in p.map(f, ch) for x in part]
    viol = [(r, l) for r, l in zip(rows, out) if r[2] != l]
    print("rows", len(rows), "label violations (cascade vs conditions, opener rule B):", len(viol))
    for r, l in viol[:5]: print("  ", [str(x) for x in r[1]], r[2], l)
    print("condition-label sizes", sorted(Counter(out).items()))
    pickle.dump(out, open('taxo_relabel_v1.pkl', 'wb'))
