import pickle
from ceil_lib_v1 import *
from ceil_allowed7_v1 import allowed7
from ceil_k6_lib_v1 import clear_components
v, six = pickle.load(open('ceil_climb_best_1_v1.pkl', 'rb'))
for den in (10**15, 10**12, 10**9):
    x6 = [F(t).limit_denominator(den) for t in six]; x6[0] = F(1)
    comps, al = allowed7(x6, cap=F(60), H=F(7))
    print('den', den, 'six', [str(t) for t in x6]); print(' K6 comps on [1,7]:', [(float(a), float(b)) for a, b in comps])
    print(' allowed rho7 intervals:', [(float(l), float(h)) for l, h in al])
    if al:
        l, h = al[-1]; m = (l + h) / 2; x = x6 + [m]
        ok, st, R = crosses(x); print(' rho7 midpoint', float(m), 'exact full path: gate crossed', ok, 'landing', float(R), 'moves', len(st), 'setter-1 moves', sum(1 for s in st if s['setter'] == 0))
        print(' x =', [str(t) for t in x])
