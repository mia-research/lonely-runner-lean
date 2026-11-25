"""v8b (2026-11-25): the W40 links where k'/k is not the best approximation of f'/f with q <= k (v8 item 2).
Recorded per link: (k, k'), f'/f, the best approximation p/q, and whether f'/f lies below k'/k by more than half the gap
to p/q: the link cell ((8k'-1)/(8k+1), (8k'+1)/(8k+1)) has centre 8k'/(8k+1) = (k'/k)(1 - 1/(8k+1)), below k'/k."""
exec(open('wall_window_word_v8.py').read().split("c = Counter(); fw = {}; lw = {}")[0])
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
        for n in range(1, len(ch)):
            k0, k1 = ch[n - 1][1], ch[n][1]; x = ch[n][0] / ch[n - 1][0]
            ba = best_approx(x, k0)
            if ba != Fr(k1, k0):
                c[((k0, k1), 'best p/q = %s' % ba, 'f\'/f below k\'/k' if x < Fr(k1, k0) else 'f\'/f above k\'/k',
                   'p/q < k\'/k' if ba < Fr(k1, k0) else 'p/q > k\'/k')] += 1
rng = random.Random(6); seen = 0
while seen < 2900:
    others = sorted(set(Fr(rng.randint(13, 480), 12) for _ in range(6)))
    if len(others) < 6: continue
    seen += 1; case('W40', [Fr(1)] + others, seen)
for k, v in sorted(c.items(), key=str): print(v, k)
