# Transformation 6: exchange the values of two readings (positions a,b of the tuple).  As a multiset map this is the identity; what can change is only the LABEL of the setter/closer.
# Tested on the tuple as given (path() labels by tuple position), with and without the condition "zones of the two readings are disjoint at every visited state".
import sys; sys.path.insert(0, '.')
from equiv_lib_v1 import *
from collections import Counter
arrs, rnd = pool(6006, 3500)
tab = Counter(); ex = {}
for a in arrs:
    a = list(a); rnd.shuffle(a)                      # unsorted tuple: labels are tuple positions
    ia = ident(a); sts = ia['S']
    for _ in range(3):
        i, j = rnd.sample(range(7), 2); b = list(a); b[i], b[j] = b[j], b[i]; ib = ident(b)
        # zones disjoint at every visited state: neither reading blocks at any state, or they never block the same state (strongest: both clear everywhere)
        both_clear = clear_all(a[i], sts) and clear_all(a[j], sts)
        never_both_block = all(not (blocks(R, a[i]) and blocks(R, a[j])) for R in sts)
        zone_disjoint_exact = True
        for R in sts:
            zi = blocks(R, a[i]); zj = blocks(R, a[j])
            if zi and zj:
                li = round(R * a[i] / 8); lj = round(R * a[j] / 8)
                if max((8 * li - 1) / a[i], (8 * lj - 1) / a[j]) < min((8 * li + 1) / a[i], (8 * lj + 1) / a[j]): zone_disjoint_exact = False
        cls = "both clear at every state" if both_clear else ("never both blocking" if never_both_block else "both block at a common state")
        tab[(cls, 'n')] += 1
        tab[(cls, 'S equal')] += ia['S'] == ib['S']; tab[(cls, 'landing equal')] += ia['L'] == ib['L']
        perm = {i: j, j: i}; mp = lambda x: perm.get(x, x)
        lab = ia['I'] == tuple((mp(s_), l) for s_, l in zip([x[0] for x in ib['I']], [x[1] for x in ib['I']])) if False else None
        tab[(cls, 'identity path equals original path with positions i,j exchanged')] += (tuple((mp(s_), l) for s_, l in ia['I']) == ib['I'])
        tab[(cls, 'closer equals original with positions exchanged')] += ((mp(ia['C'][0]), ia['C'][1]) == ib['C'])
        oa, ob = full(a), full(b); tab[(cls, 'sorted-rank (rank,lap) path equal')] += oa['path'] == ob['path']; tab[(cls, 'sorted outcome (opener,closer) equal')] += (oa['opener'], oa['closer']) == (ob['opener'], ob['closer'])
        if (mp(ia['C'][0]), ia['C'][1]) != ib['C'] and 'closer' not in ex: ex['closer'] = (a, i, j, ia, ib)
        if not (tuple((mp(s_), l) for s_, l in ia['I']) == ib['I']) and 'lab' not in ex: ex['lab'] = (a, i, j, ia, ib)
        if ia['S'] != ib['S'] and 'S' not in ex: ex['S'] = (a, i, j, ia, ib)
for cls in ("both clear at every state", "never both blocking", "both block at a common state"):
    print(cls, "| n =", tab[(cls, 'n')])
    for k in ('S equal', 'landing equal', 'identity path equals original path with positions i,j exchanged', 'closer equals original with positions exchanged', 'sorted-rank (rank,lap) path equal', 'sorted outcome (opener,closer) equal'):
        print("    %-70s %d" % (k, tab[(cls, k)]))
for k, v in ex.items(): print("example", k, fmt(v[0]), "swap positions", v[1], v[2], "| path before", v[3]['I'], "after", v[4]['I'], "| states", [str(x) for x in v[3]['S']], [str(x) for x in v[4]['S']], "| closer", v[3]['C'], v[4]['C'], "entry", v[3]['E'], v[4]['E'])
