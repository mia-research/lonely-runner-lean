# Exact checks of the two reductions on data.
# (L1) landing(path) = first clear point >= 1 of the zone union (so landing > 7  <=>  no clear point in [1,7])   [compared: path() vs clear_components(all 7, H=7)]
# (L2) landing > 7  <=>  every component of K6 on [1,7] lies in one open zone of reading 7   [compared with in_zone7]
# (W)  then rho_7 < 2/(longest component of K6 on [1,7]).
import pickle, random, sys, time
from ceil_lib_v1 import *
from ceil_k6_lib_v1 import *
T0 = time.time(); rnd = random.Random(5)
seeds = [norm(list(x)) for x in pickle.load(open('stress_seeds_v1.pkl', 'rb')).keys()]
def rand_arr(kind):
    if kind == 0: return norm([F(1)] + sorted(F(rnd.randint(105, 1700), 100) for _ in range(6)))
    if kind == 1: return norm([F(1)] + sorted(F(rnd.randint(100, 900), 100) + F(rnd.choice([-1, 0, 1]), rnd.randint(1, 2000)) for _ in range(6)))
    return norm([F(1)] + sorted(F(8 * rnd.randint(1, 4) + rnd.choice([-1, 1, 0]), rnd.choice([1, 2, 3, 5])) + F(rnd.randint(1, 100), 10**6) for _ in range(6)))
data = [('seed', x) for x in seeds] + [('rand%d' % k, rand_arr(k)) for k in (0, 1, 2) for _ in range(6000)]
cnt = {}; bad = []; worstW = None
for tag, x in data:
    if len(set(x)) < 7 or any(x[i] >= x[i+1] for i in range(6)): continue
    st, R = path(x); cross = R > 7
    c7 = clear_components(x, F(7))
    L1 = (len(c7) == 0) == cross and (cross or (c7[0][0] == R))
    c6 = clear_components(x[:6], F(7))
    L2 = all(in_zone7(x[6], a, b) is not None for a, b in c6) == cross
    ok = L1 and L2
    key = (tag.rstrip('0123456789') if tag.startswith('seed') else tag, 'cross' if cross else 'no')
    cnt[key] = cnt.get(key, 0) + 1
    if not ok: bad.append((tag, [str(t) for t in x], L1, L2))
    if cross:
        lmax = max((b - a for a, b in c6), default=F(0))
        if lmax > 0:
            slack = 2 / lmax - x[6]        # >0 required
            if slack <= 0: bad.append(('W', [str(t) for t in x]))
            if worstW is None or slack < worstW[0]: worstW = (slack, float(x[6]), float(lmax), tag)
print('counts', cnt); print('violations of L1/L2/W:', len(bad), bad[:3]); print('smallest slack 2/lmax - rho7 among crossers:', worstW)
print('time', round(time.time() - T0))
