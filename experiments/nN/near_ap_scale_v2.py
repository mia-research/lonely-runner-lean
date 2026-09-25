"""Deformations of the AP at scale, searched FOR residual membership.

near_ap_scale_v1: random +-3 deformations of k*(1..7) are settled by R6 (171/158/146 of 200) -- an
arithmetic accident, not geometry.  Here S = {k*i + e_i}, |e_i| <= E, is hill-climbed toward the
residual (objective: how far down the field list it gets, as residual_members_v4), for
k = 10^3, 10^4, 10^5 and E = k/100, k/10.  Members: least clearing resolution (ladder, cap 4k);
position of their first lonely opening relative to the AP spine 1/(8k) (exact).
"""
exec(open('residual_members_v4.py').read().split("t0 = time.time()")[0])
from fractions import Fraction as Fr
def least_D(S, cap):
    for D in range(1, cap + 1):
        if any(clears(S, D, 8 * j + 1) for j in range(D)): return D
    return None
def first_opening(S):
    best = None
    for e in S:
        for j in range(e):
            if all(e <= d * (8 * j + 1) % (8 * e) <= 7 * e for d in S):
                t = Fr(8 * j + 1, 8 * e)
                if best is None or t < best: best = t
                break
    return best
def score_ap(S):
    if len(set(S)) < 7: return -1
    for i, (_, f) in enumerate(FIELDS):
        if not f(S): return i
    return len(FIELDS)
rnd = random.Random(36)
for k in (1000, 10000, 100000):
    for E in (k // 100, k // 10):
        found = []
        for r in range(40):
            e = [rnd.randrange(-E, E + 1) for _ in range(7)]
            S = tuple(sorted(k * (i + 1) + e[i] for i in range(7))); sc = score_ap(S)
            for step in range(400):
                e2 = list(e); i = rnd.randrange(7); e2[i] = rnd.randrange(-E, E + 1)
                T = tuple(sorted(k * (j + 1) + e2[j] for j in range(7))); s2 = score_ap(T)
                if s2 >= sc: e, S, sc = e2, T, s2
                if sc == len(FIELDS): break
            if sc == len(FIELDS): found.append(S)
        line = f"k={k}, |e_i|<={E}: residual members {len(set(found))} of 40 restarts"
        if found and k <= 10000:
            S = found[0]; D = least_D(S, 4 * k); t = first_opening(S)
            line += f";  e.g. {S}: least clearing D = {D}; first lonely opening t = {t} = {float(t * 8 * k):.4f} x 1/(8k)"
        print(line, flush=True)
