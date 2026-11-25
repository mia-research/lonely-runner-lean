"""v8c (2026-11-25): exact criterion for E932 rule 22.  For a link (k, k'), let p/q be the largest fraction below k'/k
with 1 <= q <= k (Farey neighbour).  A ratio in the cell ((8k'-1)/(8k+1), (8k'+1)/(8k+1)) can be closer to p/q than to
k'/k iff the cell's lower end lies below the midpoint (p/q + k'/k)/2 ([P], since the cell lies below k'/k + (k-k')/(k(8k+1))
and fractions above k'/k are farther).  Checked: every non-best-approximation link of v8 lies in a pair that CAN fail,
and its ratio lies below the midpoint; also counted, per population, the links in can-fail pairs that did not fail."""
exec(open('wall_window_word_v8.py').read().split("c = Counter(); fw = {}; lw = {}")[0])
def below_neighbour(x, k):
    best = None
    for q in range(1, k + 1):
        p = ceil(x * q) - 1
        f = Fr(p, q)
        if f < x and (best is None or f > best): best = f
    return best
c = Counter()
def case(pop, rs, label):
    rs = sorted(rs); d = rs[0]; t0 = E / d
    S = [r for r in rs if r <= 7 * d]; Fs = [r for r in rs if r > 7 * d]
    if not Fs: return
    T, _ = cascade(rs, t0)
    ws = windows(S, t0, T + 1)
    i = next(k for k, (a, b, o) in enumerate(ws) if a <= T <= b)
    for j in range(i):
        a, b, o = ws[j]
        ch, passed, st = f_chain(Fs, a, b)
        if len(ch) < 2: continue
        for n in range(1, len(ch)):
            k0, k1 = ch[n - 1][1], ch[n][1]; x = ch[n][0] / ch[n - 1][0]; kk = Fr(k1, k0)
            pq = below_neighbour(kk, k0); mid = (pq + kk) / 2
            can = Fr(8 * k1 - 1, 8 * k0 + 1) < mid
            failed = best_approx(x, k0) != kk
            c[(pop, 'pair can fail' if can else 'pair cannot fail', 'failed' if failed else 'best approx',
               ('x < midpoint' if x < mid else 'x >= midpoint') if can else '')] += 1
def readings(v, k): return [abs(v[i] - v[k]) for i in range(len(v)) if i != k]
for v in itertools.combinations(range(1, 17), 8):
    for k in range(8): case('Z16', [Fr(x) for x in readings(v, k)], (v, k))
rng = random.Random(1)
for _ in range(3000):
    gaps = [Fr(rng.randint(6, 24), 12) for _ in range(7)]
    v = [Fr(1)]
    for g in gaps: v.append(v[-1] + g)
    for k in range(8): case('Q', readings(v, k), 0)
rng = random.Random(6); seen = 0
while seen < 2900:
    others = sorted(set(Fr(rng.randint(13, 480), 12) for _ in range(6)))
    if len(others) < 6: continue
    seen += 1; case('W40', [Fr(1)] + others, seen)
for k, v in sorted(c.items(), key=str): print(v, k)
