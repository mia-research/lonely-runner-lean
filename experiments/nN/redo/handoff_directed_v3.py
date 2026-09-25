"""handoff_directed_v2's one miss, core (32,224): 224/32 = 7, the core is DOUBLY PINNED at t_C = 1/256
(32 t_C = 1/8, 224 t_C = 7/8), so its clear set there is one isolated point, which v1's predictor (built from
cell midpoints) never looked at.  At an isolated point the train's condition cannot be read from its shape: it
depends on where N*t0 falls.  Refined prediction: t_ref = min( first isolated core-clear point t0 in
[t_C, t_pred] at which the actual train {N+e} is clear (exact, N-dependent),  t_pred ).
Rerun every arrangement of v1 and v2 against t_ref, and sweep N for the pinned core to read the N-law."""
from fractions import Fraction as F
from handoff_directed_v1 import run, breakpoints
from arrangement_lib import nd

def isolated_core_points(core, lo, hi):
    pts = []
    for t in breakpoints(core, [], lo, hi):
        if all(nd(c * t) >= F(1, 8) for c in core):
            eps = F(1, 10**12)
            if not (all(nd(c * (t - eps)) >= F(1, 8) for c in core) or all(nd(c * (t + eps)) >= F(1, 8) for c in core)):
                pts.append(t)
    return pts

def t_ref(a, b, E, N, r):
    for t0 in isolated_core_points([a, b], r['tC'], r['tp']):
        if all(nd((N + e) * t0) >= F(1, 8) for e in E): return t0
    return r['tp']

cases = [(10, b, d, f) for b in (61, 63, 65, 67, 68, 69) for d in (12, 14, 16, 18, 20) for f in (4, 5)] + \
        [(32, 208, 16, 5), (16, 96, 16, 5), (48, 320, 16, 4), (32, 224, 16, 4), (24, 162, 6, 5)]
worst = 0; n = 0
for a, b, d, f in cases:
    for N in (10**4, 10**5, 10**6):
        r = run(a, b, d, f, N); tr = t_ref(a, b, [j * d for j in range(f)], N, r)
        worst = max(worst, abs(r['t'] - tr) * N); n += 1
print(f"{n} arrangements: max |t* - t_ref| * N = {float(worst):.3f}")
print("\npinned core (32,224), train 16 x4: the event against N mod 256")
for N in range(10**5, 10**5 + 24):
    r = run(32, 224, 16, 4, N)
    tag = 't_C (isolated point)' if r['t'] == r['tC'] else f"{float(r['t']):.7f} (t_pred {r['tp']})"
    print(f"  N={N}  N mod 256 = {N % 256:3d}  N/256 frac {float(F(N, 256) % 1):.4f}:  event {tag}")
