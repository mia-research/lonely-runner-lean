# adj_cover_v1 -- how many of the stored crossers' fine cells (16,152 tuples) are among the cells reached (exact signature match)
import pickle, sys
exec(open('adj_lib_v1.py').read())
mode = sys.argv[1]
S = pickle.load(open('adj_state_%s_v1.pkl' % mode, 'rb'))
tuples = pickle.load(open('adj_alltuples_v1.pkl', 'rb'))
box = 25 if mode == 'box' else None
sigs = {}
for rh in tuples:
    x = norm(list(rh))
    if box is not None and x[6] > box: continue
    sigs.setdefault(sig_of(x, box)[0], []).append(rh)
inn = [s for s in sigs if s in S['seen']]
exp = [s for s in sigs if S['seen'].get(s) is not None]
print('mode', mode, 'distinct fine cells among stored crossers', len(sigs), 'of which reached (seen)', len(inn), 'expanded', len(exp), 'not reached', len(sigs) - len(inn))
pickle.dump([sigs[s][0] for s in sigs if s not in S['seen']], open('adj_notreached_%s_v1.pkl' % mode, 'wb'))
