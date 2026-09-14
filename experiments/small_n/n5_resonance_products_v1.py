"""n=5.  (A) resonance window: A1 exact handoff strip; runs of repeated handoffs x->y with constant lap step (p,q):
A2 (k-1) p |eps| < 2h, A3 growth < 1 + 2h/(|eps|(P1+h)), A4 admissible iff D = pQ1 - qP1 in [h(q-p), h(q+p)].
(D) laps against chain position.  (C) setter-lap product prod (5Q+1)/(5Q-1) against the actual growth 5*t_end."""
from fractions import Fraction as F
import math, random, collections
n = 5; h = F(1, n)
def cdist(x):
    f = x - math.floor(x); return min(f, 1 - f)
def near(x): return math.floor(x + F(1, 2))
def chain(ds):
    t = h / ds[0]; its = []   # (t, setter index or None, lap, inway dict idx->lap)
    setter = (0, 0)
    while True:
        inw = {}; best = t; who = None
        for i, d in enumerate(ds):
            if cdist(d * t) < h:
                k = near(d * t); inw[i] = k
                o = (k + h) / d
                if o > best: best, who = o, (i, k)
        its.append((t, setter, inw))
        if who is None: return its
        t = best; setter = who
rng = random.Random(17)
RATS = [F(1), F(4, 3), F(3, 2), F(5, 3), F(2), F(5, 2), F(3), F(4), F(5)]
def gen():
    for _ in range(50000):
        M = rng.choice([4, 10, 30, 100])
        yield sorted(1 + F(rng.randint(0, 10**6), 10**6) * M for _ in range(3))
    for _ in range(70000):
        b = 1 + F(rng.randint(0, 300000), 1000)
        yield sorted([b, b * rng.choice(RATS) + F(rng.randint(-2000, 2000), 1000), b * rng.choice(RATS) + F(rng.randint(-2000, 2000), 1000)])
    for _ in range(30000):
        g = F(rng.randint(1, 12), rng.randint(1, 3)); base = F(rng.randint(1, 60), rng.randint(1, 4))
        yield sorted(base + i * g + F(rng.randint(-300, 300), 1000 * rng.randint(1, 9)) for i in range(3))
a1_fail = 0; a1_n = 0; a2_fail = a3_fail = a4_fail = 0; runs_n = 0
growth_by_type = collections.defaultdict(lambda: [0, F(1)])  # (p,q,D,admissible) -> count, max growth
max_nonadm = F(1); max_adm = F(1)
prod_max = F(0); prod_ge4 = 0; ratio_max = F(0); prod_by_maxlap = collections.defaultdict(F); cnt = 0
lapD = collections.defaultdict(F)  # position bucket -> max Q_j / Q_1
lap_minus = collections.defaultdict(int)  # position -> max (Q_j - Q_1) among chains with Q_1 = 1
for r in gen():
    if len(set(r)) < 3 or r[0] <= 1: continue
    ds = [F(1)] + list(r); its = chain(ds); cnt += 1
    moves = [(its[j][1], j) for j in range(1, len(its))]
    # (C)
    prod = F(1)
    for (x, Q), _ in moves: prod *= F(5 * Q + 1, 5 * Q - 1)
    G = 5 * its[-1][0]
    if moves:
        prod_max = max(prod_max, prod); prod_ge4 += prod >= 4; ratio_max = max(ratio_max, G / prod)
        ml = max(Q for (x, Q), _ in moves); key = ml if ml <= 10 else (20 if ml <= 20 else 99)
        prod_by_maxlap[key] = max(prod_by_maxlap[key], prod)
        Q1 = moves[0][0][1]
        for (x, Q), j in moves:
            b = min(j, 40) // 5 * 5
            lapD[b] = max(lapD[b], F(Q, Q1))
            if Q1 == 1 and j <= 12: lap_minus[j] = max(lap_minus[j], Q - Q1)
    # (A) handoffs: at iterate j>=1, setter x at lap P; each y in the way at lap Q
    occ = collections.defaultdict(list)
    for j in range(1, len(its)):
        t, (x, P), inw = its[j]
        for y, Q in inw.items():
            if y == x: continue
            rr = ds[y] / ds[x]; a1_n += 1
            u = Q - rr * P
            if not (h * (rr - 1) < u < h * (rr + 1)): a1_fail += 1
            occ[(x, y)].append((P, Q))
    for (x, y), lst in occ.items():
        rr = ds[y] / ds[x]
        i = 0
        while i < len(lst) - 1:
            p, q = lst[i + 1][0] - lst[i][0], lst[i + 1][1] - lst[i][1]
            if p <= 0: i += 1; continue
            k = i + 1
            while k + 1 < len(lst) and (lst[k + 1][0] - lst[k][0], lst[k + 1][1] - lst[k][1]) == (p, q): k += 1
            run = lst[i:k + 1]; kk = len(run); runs_n += 1
            P1, Q1 = run[0]; Pk = run[-1][0]
            eps = rr - F(q, p)
            if not ((kk - 1) * p * abs(eps) < 2 * h): a2_fail += 1
            growth = (Pk + h) / (P1 + h)
            if eps != 0 and not (growth < 1 + 2 * h / (abs(eps) * (P1 + h))): a3_fail += 1
            D = p * Q1 - q * P1
            adm = h * (q - p) <= D <= h * (q + p)
            g = math.gcd(p, q); typ = (p // g, q // g, D, adm)
            rec = growth_by_type[typ]; rec[0] += 1; rec[1] = max(rec[1], growth)
            if adm: max_adm = max(max_adm, growth)
            else: max_nonadm = max(max_nonadm, growth)
            i = k
print('arrangements', cnt)
print(f'A1 handoffs {a1_n}, strip violations {a1_fail}')
print(f'runs (k>=2) {runs_n}; A2 violations {a2_fail}; A3 violations {a3_fail}')
print(f'largest run growth: admissible resonances {float(max_adm):.4f}, non-admissible {float(max_nonadm):.4f}')
print('run types by count (p,q,D,admissible): count, max growth')
for typ, (c, g) in sorted(growth_by_type.items(), key=lambda kv: -kv[1][0])[:18]:
    print(f'   {typ}: {c}, {float(g):.4f}')
print('admissible (p,q,D) with p,q <= 5 at n=5:', [(p, q, D) for p in range(1, 6) for q in range(p, 6 * p) if math.gcd(p, q) == 1 for D in range(-10, 11) if h * (q - p) <= D <= h * (q + p)][:30])
print('(D) max Q_j/Q_1 by position bucket:', {k: round(float(v), 3) for k, v in sorted(lapD.items())})
print('(D) chains with Q_1 = 1: max Q_j - Q_1 at position j:', dict(sorted(lap_minus.items())))
print(f'(C) max setter-lap product {float(prod_max):.4f}; chains with product >= 4: {prod_ge4}; max actual/product {float(ratio_max):.4f}')
print('(C) max product by largest lap used:', {k: round(float(v), 4) for k, v in sorted(prod_by_maxlap.items())})
