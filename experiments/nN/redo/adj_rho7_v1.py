# adj_rho7_v1 -- rho_7 closure maxima over reached cells; exact certificates for the 12 cells with the largest float maxima; entry-point rho_7 of unexpanded cells
import pickle
exec(open('adj_lib_v1.py').read())
from ceil_lib_v1 import maxrho
S = pickle.load(open('adj_state_unb_v1.pkl', 'rb'))
ex = [(sg, r) for sg, r in S['seen'].items() if r]
fm = sorted(((r['fmax'][7], sg) for sg, r in ex), reverse=True)
print('expanded cells', len(ex), ' float LP closure max of rho_7: largest', fm[0][0], ' cells above 24:', sum(1 for v, s in fm if v > 24), 'above 20:', sum(1 for v, s in fm if v > 20), 'above 16.5:', sum(1 for v, s in fm if v > 16.5), 'above 9:', sum(1 for v, s in fm if v > 9))
print('exact (Fraction LP with Farkas certificate) closure maxima of rho_7, 12 largest float cells:')
for v, sg in fm[:12]:
    r = S['seen'][sg]; rows, tags, steps, R = cell_of(norm(list(r['entry'])))
    res = maxrho(rows, 7)
    if res is None: print('  cert failed', sg[:8]); continue
    X, lam = res; xv = norm(list(X)); print('  %s = %.9f  (cell %s; vertex is a gate crosser: %s)' % (X[6], float(X[6]), sg[:8], crosses2(xv)[0]))
ent = [x[6] for sg, x, lab in S['queue']] + [r['entry'][6] for sg, r in ex]
print('reached cells (expanded + frontier):', len(ent), ' largest rho_7 of an entry point', float(max(ent)), ' entry points with rho_7 > 17:', sum(1 for v in ent if v > 17))
