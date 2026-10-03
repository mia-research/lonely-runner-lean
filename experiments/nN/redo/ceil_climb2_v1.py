# hill-climb (floats steer, Fractions verify) on six readings maximising the largest rho_7 for which no clear point exists in [1,7] (gate crossing).
import sys, time, random, math, pickle
from fractions import Fraction as F
from ceil_allowed7_v1 import allowed7
from ceil_k6_lib_v1 import clear_components
def fcomps(r, H=7.0):
    Z = []
    for x in r:
        j = 1
        while (8*j - 1) / x < H + 1:
            Z.append(((8*j - 1) / x, (8*j + 1) / x)); j += 1
    Z.sort(); comps = []; cur = 1.0; me = None
    for a, b in Z:
        if b <= 1.0: continue
        if me is None:
            if a >= cur: comps.append((cur, a))
            me = b
        elif a >= me: comps.append((me, a)); me = max(me, b) if False else b
        else: me = max(me, b)
        if me > H: break
    if me is None: comps.append((1.0, H))
    elif me <= H: comps.append((me, H))
    return [(a, min(b, H)) for a, b in comps if a <= H]
def fallowed(six, cap=60.0, H=7.0):
    comps = fcomps(six, H); cur = [(six[-1], cap)]
    for a, b in comps:
        ivs = []; j = 1
        while True:
            lo = (8*j - 1) / a; hi = (8*j + 1) / b
            if lo >= cap: break
            if lo < hi: ivs.append((lo, hi))
            j += 1
        new = []
        for (l1, h1) in cur:
            for (l2, h2) in ivs:
                l = max(l1, l2); h = min(h1, h2)
                if l < h: new.append((l, h))
        cur = new
        if not cur: return comps, None
    return comps, max(h for l, h in cur)
if __name__ == "__main__":
    LIM = float(sys.argv[1]); seed = int(sys.argv[2]); cap = float(sys.argv[3]); T0 = time.time(); rnd = random.Random(seed)
    starts = pickle.load(open('ceil_starts2_v1.pkl', 'rb'))
    best_all = (0, None); nev = 0; runs = 0
    while time.time() - T0 < LIM:
        s = rnd.choice(starts); six = [float(t) for t in s]; 
        c, v = fallowed(six, cap)
        if v is None: continue
        cur = (v, six); runs += 1; stall = 0
        while time.time() - T0 < LIM and stall < 20000:
            k = rnd.choice([1, 1, 2, 3, 5]); idx = rnd.sample(range(1, 6), min(k, 5)); y = list(cur[1])
            for i in idx: y[i] *= 1 + rnd.choice([-1, 1]) * 10 ** (-rnd.uniform(1.5, 11))
            if not all(y[i] < y[i+1] for i in range(5)) or y[0] != 1.0: stall += 1; continue
            nev += 1; c2, v2 = fallowed(y, cap)
            if v2 is not None and v2 >= cur[0]:
                if v2 > cur[0] + 1e-12: stall = 0
                else: stall += 1
                cur = (v2, y)
            else: stall += 1
        if cur[0] > best_all[0]: best_all = cur
        print('run', runs, 'start rho6 %.3f' % six[-1], 'end sup rho7 %.9f' % cur[0], 'rho6 %.6f' % cur[1][-1], 'evals', nev, flush=True)
    v, six = best_all
    print('best float sup', v, [repr(t) for t in six])
    pickle.dump(best_all, open('ceil_climb2_best_%d_v1.pkl' % seed, 'wb'))
