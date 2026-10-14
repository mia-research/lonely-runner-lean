"""The framework's named cases, as a runnable regression set.

WHY THIS EXISTS. On 2026-09-17 a random sweep of 28,000 arrangements returned "0 beyond the first
window" and that null was reported as if it settled the question. MANUSCRIPT_v9_1 section 6.7 already
named an arrangement with `u = 1.28` laps, and section 6.9's table named another for which *nothing
clears in the first window at all*. Checking either would have refuted the null in one second. The
failure was not the sweep; it was reporting a null without calibrating against the cases already on
file.

So: every case the manuscript names, with its published values, runnable. Any claim of the form "no
arrangement does X" is checked here FIRST. A claim that survives this is not proved, but a claim that
fails here is refuted at no cost.

Add a row whenever the manuscript names a case. Do not delete rows.

Sources: MANUSCRIPT_v9_1.md lines 114, 373-378, 484, 533, 543-548, 557-558.
"""
import sys
from fractions import Fraction as F

n = 8; INV_N = F(1, n)

def fract(x):          return x - (x.numerator // x.denominator)
def circDist(x):       return min(fract(x), 1 - fract(x))
def inWay(d, t):       return circDist(d * t) < INV_N
def ceil_(x):          return -((-x.numerator) // x.denominator)
def nextOpening(d, t): return (F(ceil_(d * t - INV_N)) + INV_N) / d
def Lonely(ds, s):     return all(INV_N <= circDist(d * s) for d in ds)
def move(ds, t):
    acc = t
    for d in ds:
        if inWay(d, t):
            o = nextOpening(d, t)
            if o > acc: acc = o
    return acc

def cascade(speeds, subject, maxsteps=500):
    ds = sorted(F(abs(subject - v)) for v in speeds if v != subject)
    m = min(ds)
    t = F(1) / (n * m); steps = 0; nearest_set_at = []
    while steps <= maxsteps:
        t2 = move(ds, t)
        if t2 == t: break
        if any(d == m and inWay(d, t) and nextOpening(d, t) == t2 for d in ds):
            nearest_set_at.append(steps + 1)
        t = t2; steps += 1
    return dict(ds=ds, d_min=m, t=t, steps=steps, u=m * t, R=n * m * t,
                lonely=Lonely(ds, t), nearest_set_at=nearest_set_at)

def clears_in_first_window(speeds, subject, denom=2520):
    """Is there ANY lonely instant with u in [1/8, 7/8]? Scanned on a fine rational grid plus the
    cascade's own openings; a negative here is grid-limited and says 'none found', not 'none exists'."""
    ds = sorted(F(abs(subject - v)) for v in speeds if v != subject)
    m = min(ds)
    lo, hi = F(1, 8), F(7, 8)
    k = 0
    while True:
        u = lo + F(k, denom)
        if u > hi: return False
        if Lonely(ds, u / m): return True
        k += 1

# ---------------------------------------------------------------- the named cases
CASES = [
    dict(name="section 6.7 adversarial climb",
         speeds=[27, 70, 107, 137, 159, 188, 344, 393], subject=393,
         expect=dict(t=F(49, 1872), steps=28),
         note="28 moves; the most in the replication. R = 2401/234 ~ 10.26, u ~ 1.28 laps."),
    dict(name="section 6.9 table / v7 Claim refutation",
         speeds=[1, 31, 75, 97, 128, 160, 176, 225], subject=1,
         expect=dict(t=F(11, 256), steps=23, d_min=F(30), u=F(165, 128)),
         note="'nothing clears in its first window, and it is lonely at t = 9/40' (line 558)."),
    dict(name="section 6.6 near-wrap",
         speeds=[1, 2, 3, 4, 5, 6, 7, 9], subject=1,
         expect=dict(u=F(9, 64)),
         note="first lonely instant stays at u = 9/64 (two scales); line 114/484."),
    dict(name="section 6.2 scale chain",
         speeds=[1, 2, 3, 4, 5, 6, 8, 9], subject=1,
         expect=dict(R=F(9, 7)),
         note="chain (8,N=1),(7,N=1) ends at D_final = 7/9; R = d_min/D_final = 9/7 (line 118, 378)."),
]

def main():
    print(f"order {n}: the framework's named cases\n")
    failures = 0
    for c in CASES:
        got = cascade(c['speeds'], c['subject'])
        bad = []
        for k, v in c['expect'].items():
            if got[k] != v: bad.append(f"{k}: expected {v}, got {got[k]}")
        status = "OK  " if not bad else "FAIL"
        if bad: failures += 1
        print(f"  [{status}] {c['name']}")
        print(f"         speeds {c['speeds']}  subject {c['subject']}")
        print(f"         t = {got['t']}   moves = {got['steps']}   d_min = {got['d_min']}")
        print(f"         u = {got['u']} = {float(got['u']):.4f} laps    R = n*u = {got['R']} = {float(got['R']):.4f}")
        print(f"         lonely: {got['lonely']}   nearest runner set at steps: {got['nearest_set_at'] or 'never'}")
        print(f"         beyond the first window (u > 7/8): {got['u'] > F(7,8)}"
              f"    above the cap (R >= {n-1}): {got['R'] >= n-1}")
        for b in bad: print(f"         MISMATCH {b}")
        print(f"         note: {c['note']}")
        print()

    print("  --- what these refute, mechanically ---")
    over = [c['name'] for c in CASES if cascade(c['speeds'], c['subject'])['R'] >= n - 1]
    print(f"  arrangements here with R >= {n-1} (the first-window cap): {len(over)}")
    for o in over: print(f"     {o}")
    print(f"  => any claim that R < {n-1} for every arrangement at order 8 is refuted by these rows.")
    c = CASES[1]
    found = clears_in_first_window(c['speeds'], c['subject'])
    print(f"\n  '{c['name']}': lonely instant found in the first window u in [1/8, 7/8]: {found}")
    print(f"     (manuscript line 558: nothing clears in its first window)")
    print(f"\n  named cases failing their published values: {failures}")
    return 1 if failures else 0

if __name__ == '__main__':
    sys.exit(main())
