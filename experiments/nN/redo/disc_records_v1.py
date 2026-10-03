# Build outcome records for all tree members. record: cell, R*, width, positions p_y (exact), states, exits(setter,lap), rhos
import pickle, time
from fractions import Fraction as F
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
mem = pickle.load(open('cell_members_J2.pkl','rb'))
recs = []
t=time.time()
for ci, rh in mem:
    steps, R = path(rh)
    ps = [(R*r) % 8 for r in rh]
    w = min((7-p)/r for p, r in zip(ps, rh))
    states = [F(1)/min(rh)] + [s['R2'] for s in steps]
    exits = [(s['setter'], s['lap']) for s in steps]
    recs.append((ci, rh, R, w, ps, states, exits))
print(len(recs), time.time()-t, all(rh==sorted(rh) for _,rh in mem))
pickle.dump(recs, open('disc_records_v1.pkl','wb'))
