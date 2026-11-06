# E831: chain types near given vectors (floats steer only): perturb each start by random relative sizes, take the greedy zone chain of the perturbed vector, solve the LP margin for that type (frontier_type_search_v1.lp_margin), and report the distinct types, the largest margin, and the exact carves among the LP optima.  usage: group seed perturbations
import sys, glob, re, pickle, random, collections
sys.argv_saved = sys.argv; 
src = open('frontier_type_search_v1.py').read().split('found = []; types_seen')[0]
sys.argv = ['x', '1', '15', '80', '1', '1']
exec(src)
sys.argv = sys.argv_saved
group = sys.argv[1]; random.seed(int(sys.argv[2])); N = int(sys.argv[3])
starts = []
if group == 'lap3':
    for f in sorted(glob.glob('frontier_box_carve_v1_23_25_s*.pkl')): starts += pickle.load(open(f, 'rb'))[:6]
elif group == 'above25':
    for f in sorted(glob.glob('frontier_box_carve_v1_hi2_s*.out')):
        m = re.search(r'readings \(float\): \[(.*)\]', open(f).readline()); starts.append([float(v) for v in m.group(1).split(',')])
    starts.append(pickle.load(open('frontier_polish_v1_first.pkl', 'rb')))
types = collections.Counter(); pos = {}; best = -1e9; ncarve = 0; carve_types = set(); mx7 = 0
for it in range(N):
    x0 = random.choice(starts); scale = random.choice([1e-3, 1e-2, 5e-2, 0.1])
    x = sorted(max(1.0001, v * (1 + scale * random.uniform(-1, 1))) for v in x0)
    ch = chain_of(x)
    if ch is None or ch in types: types[ch] += 1; continue
    types[ch] += 1
    hi7 = max(x[5] * 1.5, 41.0)
    n_ = 6
    r = lp_margin(ch)
    if r is None: continue
    t, xs = r; best = max(best, t)
    if t > 1e-9:
        xs = list(map(float, xs))
        if carves_exact(xs): ncarve += 1; carve_types.add(ch); mx7 = max(mx7, xs[5])
print(group, '| perturbations', N, '| distinct chain types', len(types), '| types whose LP margin is positive and whose LP optimum is an exact carve:', len(carve_types), '| largest r7 of those optima (float):', round(mx7, 3), '| best margin over types (float):', best)
