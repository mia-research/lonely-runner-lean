"""Checks of the premises in the 2026-09-15 target proposals (exact rationals throughout).
(A) order 8, integer speeds: are the cascade's scales D_j = 1/(8 t_j) integers after the first step, and does any step
    after the first reach 8·D_j > spread (the region where no runner shares a slot)?
(B) every n tested: does each runner set at strictly increasing laps?
(C) order 5: true R against the setter-lap product prod F(Q_j) and against the per-runner lap bound prod_x g(L_x),
    L_x = floor(s_x R/n + 1/n), F(Q) = (nQ+1)/(nQ-1), g(L) = prod_{r<=L} F(r).
(D) order 5: how often the final R is an integer (an own-AP instant)."""
from fractions import Fraction as F
import math, random, itertools
def cdist(x):
    f = x - math.floor(x); return min(f, 1 - f)
def chain(ds, n):
    th = F(1, n); a = min(ds); t = th / a; steps = []
    while True:
        best = t; who = None
        for i, d in enumerate(ds):
            if cdist(d * t) < th:
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, (i, k)
        if who is None: return t, steps
        steps.append((who[0], who[1], best)); t = best
def g(L, n): return math.prod((F(n * r + 1, n * r - 1) for r in range(1, L + 1)), start=F(1))

# (A)
rng = random.Random(1)
arrs = [c for c in itertools.combinations(range(1, 17), 8) if math.gcd(*[x - c[0] for x in c[1:]]) == 1]
arrs += [tuple(sorted(rng.sample(range(1, 201), 8))) for _ in range(2000)]
runners = moved = int_scale_steps = scale_steps = live_after_first = 0
for v in arrs:
    spread = v[-1] - v[0]
    for i in range(8):
        ds = [abs(x - v[i]) for x in v if x != v[i]]
        t, steps = chain([F(d) for d in ds], 8); runners += 1
        if steps: moved += 1
        for (_, _, tj) in steps:
            D = 1 / (8 * tj); scale_steps += 1
            if D.denominator == 1: int_scale_steps += 1
            if 8 * D > spread: live_after_first += 1
print(f'(A) order 8: {runners} runners, {moved} with at least one move, {scale_steps} scales reached by a move')
print(f'    integer scales among them: {int_scale_steps}; scales with 8·D > spread: {live_after_first}')

# (B), (C), (D)
RATS = [F(1), F(4, 3), F(3, 2), F(5, 3), F(2), F(5, 2), F(3)]
for n in (5, 6, 8):
    rng = random.Random(n); viol = 0; chains = 0; rows = []; intR = 0; movedR = 0
    k = n - 1
    for it in range(6000 if n == 5 else 1500):
        if it % 2 == 0:
            ds = sorted({F(1)} | {1 + F(rng.randint(0, 9000), 1000) for _ in range(k - 1)})
        else:
            b = 1 + F(rng.randint(0, 3000), 1000)
            ds = sorted({F(1), b} | {max(F(1), b * rng.choice(RATS) + F(rng.randint(-300, 300), 1000)) for _ in range(k - 2)})
        if len(ds) != k: continue
        t, steps = chain(ds, n); chains += 1
        last = {}
        for (i, q, _) in steps:
            if i in last and q <= last[i]: viol += 1
            last[i] = q
        R = n * ds[0] * t
        if steps:
            movedR += 1
            if R.denominator == 1: intR += 1
        if n == 5 and steps:
            P = math.prod((F(n * q + 1, n * q - 1) for _, q, _ in steps), start=F(1))
            B = math.prod((g(math.floor(s * R / n + F(1, n)), n) for s in ds), start=F(1))
            rows.append((float(R), float(P), float(B), len(steps)))
    print(f'(B) n={n}: {chains} chains; runners setting twice at a non-increasing lap: {viol}')
    print(f'(D) n={n}: final R an integer in {intR} of {movedR} chains with a move')
    if n == 5:
        rows.sort()
        print(f'(C) n=5: R <= prod F(Q_j) in {sum(r[0] <= r[1] + 1e-12 for r in rows)} of {len(rows)}; '
              f'prod F <= prod_x g(L_x) in {sum(r[1] <= r[2] + 1e-12 for r in rows)} of {len(rows)}')
        print('    largest R rows (R, prod F, prod g, moves):', [tuple(round(x, 3) for x in r) for r in rows[-3:]])
        print('    longest chains (R, prod F, prod g, moves):', [tuple(round(x, 3) for x in r) for r in sorted(rows, key=lambda r: r[3])[-3:]])
