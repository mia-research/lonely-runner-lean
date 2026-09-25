"""Bottlenecks along the deformation from the ideal: delta(lambda) = max_t min_d ||d t||.

Floating point, t in (0, 2], candidates at mirror and equal meetings.  For 10 hard sets, the two
with delta = 2/15 and 8 random residual sets of [1,40]: the deepest dip of delta for lambda >= 0.05,
and the nearest small-integer pattern of the speeds there.
"""
import itertools, random, time, math
_rs = __file__.replace('bottleneck_v1.py', 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])
def nd(x): return abs(x - round(x))
def delta_real(D, T=2.0):
    best = (-1, None)
    for i, j in itertools.combinations(range(len(D)), 2):
        for m in (D[i] + D[j], abs(D[i] - D[j])):
            if m < 1e-12: continue
            for k in range(1, int(m * T) + 1):
                t = k / m
                v = min(nd(d * t) for d in D)
                if v > best[0]: best = (v, t)
    return best
def path(S, steps=200):
    s = sorted(S); ks = range(1, 8)
    Delta = sum(k * x for k, x in zip(ks, s)) / 140
    prof = []
    for st in range(steps + 1):
        lam = st / steps
        D = [(1 - lam) * k * Delta + lam * x for k, x in zip(ks, s)]
        v, t = delta_real(D); prof.append((lam, v, t, D))
    return prof
def ap_fit(D):
    """best progression m_k * Delta' (m_k positive integers <= 60) for the speeds: relative error"""
    best = (9, None)
    for M in range(1, 61):
        Dp = D[0] / M
        ms = [round(d / Dp) for d in D]
        if min(ms) < 1: continue
        Dp = sum(m * d for m, d in zip(ms, D)) / sum(m * m for m in ms)
        err = max(abs(d - m * Dp) for m, d in zip(ms, D)) / Dp
        if err < best[0]: best = (err, tuple(ms))
    return best
_rl = __import__('itertools')
R = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
hard = [S for S in R if not any(rule(S, q, free_exact) for q in range(2, 9))][:10]
random.seed(9)
sets = hard + [(1, 3, 4, 5, 7, 11, 24), (1, 4, 5, 6, 7, 11, 16)] + random.sample(R, 8)
t0 = time.time()
for S in sets:
    prof = path(S)
    mid = [p for p in prof if p[0] >= 0.05]
    lam, v, t, D = min(mid, key=lambda p: p[1])
    err, ms = ap_fit(D)
    print(f"{S}: delta at lambda=1 {prof[-1][1]:.4f};  deepest dip for lambda >= 0.05: {v:.4f} at lambda {lam:.3f}, t* {t:.4f};  speeds there ~ {[round(x, 2) for x in D]};  nearest integer pattern {ms} (max rel. error {err:.3f})")
print(f"({time.time()-t0:.0f}s)")
