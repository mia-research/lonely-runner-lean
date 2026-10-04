# adj_boxcmp_v1 -- compare the first N discovered cells of the box run (rho_7 <= 25 rho_1 row added) with the unbounded run (exact signatures recomputed without the box row)
import pickle
exec(open('adj_lib_v1.py').read())
U = pickle.load(open('adj_state_unb_v1.pkl', 'rb')); B = pickle.load(open('adj_state_box_v1.pkl', 'rb'))
pts = {}
for sg, r in B['seen'].items():
    if r is not None: pts[sg] = r['entry']
for sg, x, lab in B['queue']: pts[sg] = x
kb = list(B['seen']); mapped = [sig_of(pts[k], None)[0] for k in kb]
ku = list(U['seen'])
print('box cells seen', len(kb), 'expanded', sum(1 for k in kb if B['seen'][k] is not None), 'queue', len(B['queue']))
print('sequence equal to unbounded discovery prefix:', mapped == ku[:len(mapped)], ' set equal to unbounded prefix:', set(mapped) == set(ku[:len(mapped)]), ' subset of unbounded seen:', set(mapped) <= set(ku))
print('box wall facets encountered', B['boxwall'], ' unresolved', len(B['unresolved']))
