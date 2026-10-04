# adj_reps_v1 -- one representative arrangement per K6 template of the stored gate crossers (115), X24, and the 5 largest rho_7 crossers.
# Exact (Fractions).  Output adj_reps_v1.pkl, adj_t115_v1.pkl, adj_reps_v1.out
import pickle, glob
exec(open('tmpl_lib_v1.py').read())
X24 = [F(1), F(2752864293769,970238379379), F(3691147638604,961559468885), F(4851775667488,988103849833), F(5240560485773,830842598345), F(2806730537001,400961505286), F(474233610200591258564537783,19451412054102649094869700)]
tuples = {}
for f in sorted(glob.glob('tmpl_rec_*_v1.pkl')):
    d = pickle.load(open(f, 'rb'))
    for (n, rh, tid) in d['cross']:
        tuples.setdefault(tuple(rh), (d['src'], n))
seeds = pickle.load(open('stress_seeds_v1.pkl', 'rb'))
print('crosser tuples from tmpl_rec files', len(tuples))
tuples.setdefault(tuple(X24), ('X24', 0))
bytmpl = {}
nbad = 0
for rh, src in tuples.items():
    r = list(rh)
    T, W = template(r)
    assert gate(r, W)
    bytmpl.setdefault(T, []).append(rh)
print('distinct templates', len(bytmpl))
reps = []
for i, (T, lst) in enumerate(sorted(bytmpl.items(), key=lambda kv: tstr(kv[0]))):
    reps.append(('T%03d' % i, lst[0], tstr(T)))
top = sorted(tuples, key=lambda rh: -rh[6])[:5]
for i, rh in enumerate(top): reps.append(('top7_%d' % (i + 1), rh, 'rho7=%s' % (float(rh[6]))))
reps.append(('X24', tuple(X24), ''))
pickle.dump(reps, open('adj_reps_v1.pkl', 'wb'))
pickle.dump(set(bytmpl.keys()), open('adj_t115_v1.pkl', 'wb'))
pickle.dump(list(tuples.keys()), open('adj_alltuples_v1.pkl', 'wb'))
for lab, rh, ts in reps: print(lab, float(rh[6]), ts)
