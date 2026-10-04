# adj_known_v1 -- are the cells found by earlier walks (E344 extremal, X7, 511/31 cell, rho_6 8.1512 cell, X24) among the reached cells?
import pickle, ast, sys
exec(open('adj_lib_v1.py').read())
from ceil_lib_v1 import X7
mode = sys.argv[1]; S = pickle.load(open('adj_state_%s_v1.pkl' % mode, 'rb')); seen = S['seen']
def mem(s): return [F(t) for t in ast.literal_eval(s)]
known = {}
known['E344 extremal member (b12_A_x0)'] = list(pickle.load(open('b12_A_x0_v1.pkl', 'rb'))[0])
known['X7'] = list(X7)
known['rho6 8.1512 walk member'] = mem("['1', '8549887/2310000', '17669759/3430000', '5343689/866250', '69999/10000', '71249/8750', '2009227757/228690000']")
for l in open('ceil_pivot7b_v1.out'):
    if l.startswith('best cell member'):
        known['pivot7b best member (rho7 24.40)'] = mem(l.split('member')[1].split('landing')[0].strip())
for l in open('ceil_pivot7_v1.out'):
    if l.startswith('best cell member'):
        known['pivot7 best member (rho7 16.48)'] = mem(l.split('member')[1].split('landing')[0].strip())
for k, x in known.items():
    x = norm(x); ok, st, R = crosses2(x); sg = sig_of(x)[0]
    print('%-40s gate crosser %s  rho7 %.5f  moves %d  cell reached: %s  expanded: %s' % (k, ok, float(x[6]), len(st), sg in seen, seen.get(sg) is not None))
