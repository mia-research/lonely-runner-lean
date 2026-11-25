"""v7b (2026-11-25): cross-tabulation for E931 rule 22: Z16 multi-move passes by (length >= 5, setter repeats)."""
exec(open('wall_window_chain_v7.py').read().split("def readings(v, k):")[0])
import itertools
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
        rk = [s for s, *_ in ch]
        c[('length >= 5' if len(ch) >= 5 else 'length < 5', 'repeat' if len(set(rk)) < len(rk) else 'distinct')] += 1
def readings(v, k): return [abs(v[i] - v[k]) for i in range(len(v)) if i != k]
for v in itertools.combinations(range(1, 17), 8):
    for k in range(8): case('Z16', [Fr(x) for x in readings(v, k)], (v, k))
for k, v in sorted(c.items()): print(v, k)
