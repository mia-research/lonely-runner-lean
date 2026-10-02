# Is 26433/2209 = 11.966 (the exact supremum for readings <= 9 d_min) also the supremum over WIDER windows?  Hill-climb the landing from seeds that
# add whole laps to the extremal J=1 arrangement (the fastest readings raised by 8, 16) and from random seeds, windows 17 / 25 / 33.
import sys, random, math
sys.argv = [sys.argv[0]]
exec(open('extremes_deep_v1.py').read().split('\nif __name__ ==')[0])
seed0 = [1.0, 2.3465147, 3.1333333, 4.1829175, 5.2222222, 5.7848859, 7.4377104]
def climb(start, W, iters, rnd):
    rho = list(start); cur = fpath(rho)[0]
    for it in range(iters):
        new = list(rho); i = rnd.randrange(1, 7)
        scale = (W - 1) * (0.05 if it < iters // 3 else (0.01 if it < 2 * iters // 3 else 0.001))
        new[i] = min(W, max(1.0001, new[i] + rnd.gauss(0, scale))); new = [1.0] + sorted(new[1:])
        if len(set(new)) < 7: continue
        R, n = fpath(new)
        if n >= 10**6: continue
        if R >= cur: rho, cur = new, R
    return cur, rho
rnd = random.Random(332); best = {}
for W in (17, 25, 33):
    top = (0, None)
    for rep in range(40):
        s = list(seed0)
        k = rnd.sample(range(1, 7), rnd.choice((1, 2, 3)))
        for i in k: s[i] += 8 * rnd.choice((1, 2)) if s[i] + 8 <= W else 0
        s = [1.0] + sorted(s[1:])
        if len(set(s)) < 7 or s[-1] > W: continue
        v, rho = climb(s, W, 2500, rnd)
        if v > top[0]: top = (v, rho)
    for rep in range(30):
        s = [1.0] + sorted(rnd.uniform(1.0, W) for _ in range(6)); v, rho = climb(s, W, 2500, rnd)
        if v > top[0]: top = (v, rho)
    print("window rho_7 <= %d: largest landing found %.4f   readings %s" % (W, top[0], [round(x, 4) for x in top[1]]), flush=True)
