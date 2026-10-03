# Task 1(b): R2 -- the exact set of rho_7 (> rho_6) giving gate crossing (landing > 7) is the intersection over components [a,b] of K6 of the union over j>=1
# of the open intervals ((8j-1)/a, (8j+1)/b).  Test against the direct cascade path() of the seven readings on 2000 six-tuples.
import random, time
from k6map_lib_v1 import *
CAP = F(80)
def allowed(six, cap=CAP):
    comps = K6(six)
    cur = [(six[-1], cap)]
    for a, b in comps:
        ivs = []; j = 1
        while F(8*j - 1) / a < cap:
            lo = F(8*j - 1) / a; hi = F(8*j + 1) / b
            if lo < hi: ivs.append((lo, hi))
            j += 1
        new = []
        for l1, h1 in cur:
            for l2, h2 in ivs:
                l = max(l1, l2); h = min(h1, h2)
                if l < h: new.append((l, h))
        cur = sorted(new)
        if not cur: break
    return comps, cur
def inA(A, x): return any(l < x < h for l, h in A)
rnd = random.Random(20261003)
def q(x, d=10**4): return F(round(x * d), d)
def gen(kind):
    if kind == 0: xs = [F(rnd.randint(8, 24 * 6), rnd.choice((1, 2, 3, 6))) / (1 if False else 1) for _ in range(5)]; xs = [x / 6 * 6 for x in xs]
    return None
def gen_any():
    k = rnd.randrange(5)
    if k == 0: xs = [F(rnd.randint(2, 24)) for _ in range(5)]
    elif k == 1: xs = [F(rnd.randint(7, 144), rnd.choice((2, 3, 6))) for _ in range(5)]
    elif k == 2: xs = [q(rnd.uniform(1.05, rnd.choice((8, 12, 25)))) for _ in range(5)]
    elif k == 3: xs = [F(rnd.randint(2, 16)) + F(rnd.randint(-30, 30), 100) for _ in range(5)]
    else: xs = [F(rnd.randint(3, 96), rnd.choice((2, 3, 4, 5, 6, 7))) + F(rnd.randint(-3, 3), 1000) for _ in range(5)]
    xs = sorted(set(x for x in xs if x > 1))
    if len(xs) < 5: return None
    return [F(1)] + xs
def points(six, A, cap=CAP):
    pts = set()
    r6 = six[-1]
    pts.add(r6 + F(1, 7)); pts.add(r6 * 2); pts.add(r6 * 3)
    for _ in range(8): pts.add(r6 + F(rnd.randint(1, 10**5), 10**5) * (cap - r6))
    for l, h in A:
        w = h - l
        for x in (l, h, (l + h) / 2, l + w / 1000, h - w / 1000, l - w / 1000, h + w / 1000, l - F(1, 10**9), h + F(1, 10**9)): pts.add(x)
    for (l1, h1), (l2, h2) in zip(A, A[1:]): pts.add((h1 + l2) / 2)
    return sorted(x for x in pts if x > r6 and x < cap)
t0 = time.time(); tuples = []
tuples.append(("X24 six", [F(t) for t in ['1', '2752864293769/970238379379', '3691147638604/961559468885', '4851775667488/988103849833', '5240560485773/830842598345', '2806730537001/400961505286']]))
# X7 six (readings of ceil_k6_X7): taken from the 16.2108 vertex of ceil_cell_v1: (1,95/33,475/123,475/99,19/3,475/69)
tuples.append(("16.21 vertex six", [F(1), F(95, 33), F(475, 123), F(475, 99), F(19, 3), F(475, 69)]))
generic = 0
while len(tuples) < 1000:
    s = gen_any()
    if s: tuples.append(("generic", s))
nonempty_target = 1000; ne = 0; draws = 0
while ne < nonempty_target and time.time() - t0 < 330:
    s = gen_any(); draws += 1
    if not s: continue
    c, A = allowed(s)
    if A: tuples.append(("A nonempty", s)); ne += 1
print("tuples:", len(tuples), "of which drawn with nonempty allowed set above rho_6 (cap 80):", ne, "after", draws, "draws", "time", round(time.time() - t0, 1))
tested = 0; mism = 0; cross_true = 0; cross_false = 0; nonempty = 0; ratios = []; ties_at_end = 0
for name, s in tuples:
    c, A = allowed(s)
    if A: nonempty += 1
    for x in points(s, A):
        R = path(s + [x])[1]
        direct = R > 7
        pred = inA(A, x)
        tested += 1
        if direct != pred:
            mism += 1
            if mism <= 5: print("MISMATCH", name, [str(t) for t in s], x, direct, pred, R)
        if direct: cross_true += 1
        else: cross_false += 1
    if A:
        Lmax = max(b - a for a, b in c)
        sup = max(h for l, h in A)
        ratios.append(sup * Lmax / 2)
print("six-tuples", len(tuples), "| with nonempty allowed set:", nonempty, "| test points (exact rho_7):", tested, "| direct crossing:", cross_true, "not crossing:", cross_false, "| mismatches R2 vs direct path():", mism)
if ratios: print("sup(A) * L_max / 2 over nonempty tuples: max %s = %.6f, min %s = %.6f (W says < 1 each)" % (max(ratios), float(max(ratios)), min(ratios), float(min(ratios))))
print("X24 six: components", [(str(a), str(b)) for a, b in K6(tuples[0][1])][:6] if False else len(K6(tuples[0][1])))
print("X24 allowed:", [(float(l), float(h)) for l, h in allowed(tuples[0][1])[1]])
print("16.21 vertex six allowed:", [(float(l), float(h)) for l, h in allowed(tuples[1][1])[1]])
