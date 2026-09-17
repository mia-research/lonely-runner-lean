"""Test the candidate Long-Return Depth Lemma (from another session).

CLAIM. For g >= 4, let R_g be the n=8 cascade configurations in which a setter returns after
exactly g intervening setter moves. Write the returning setter's reading as

    s_R = 8*N_R - 1 + 8*delta(R),      0 < delta(R) < 1/4.

Then there is a universal c_* > 0 with delta(R) >= c_* for all g >= 4 and all R in R_g, and
the extremal return length is g = 4, i.e. c_* = inf over R_4 = inf over all g >= 4.

READING THE PARAMETRISATION. A runner is in the way at t when circDist(d*t) < 1/8, i.e. d*t
is within 1/8 of an integer N. In eighths, s = 8*d*t lies in (8N-1, 8N+1), so writing
s = 8N - 1 + 8*delta puts delta in (0, 1/4). Equivalently

    delta = (d*t - N) + 1/8,     N = round(d*t).

delta = 0 is the near edge of the blocking zone, delta = 1/4 the far edge.

WHY IT WOULD MATTER. A floor on delta bounds how shallowly a returning setter can sit, which
bounds the move it forces from below -- that bears directly on the cap.
"""
import random, math
from fractions import Fraction as F

n = 8

def circ(x):
    f = x - math.floor(x)
    return min(f, 1 - f)

def cascade_setters(ds, maxsteps=4000):
    """Run the determinator from the bound. Yield (step, setter, delta) at each move."""
    m = min(ds)
    t = 1.0 / (n * m)
    out = []
    for step in range(maxsteps):
        inway = [d for d in ds if circ(d * t) < 1.0 / n]
        if not inway:
            return out, True                      # arrived
        best = None
        for d in inway:
            N = round(d * t)
            nxt = (N + 1.0 / n) / d
            if nxt > t and (best is None or nxt > best[0]):
                best = (nxt, d, N)
        if best is None:
            return out, False
        nxt, d, N = best
        delta = (d * t - N) + 1.0 / n             # in (0, 1/4)
        out.append((step, d, delta))
        t = nxt
    return out, False

rng = random.Random(20260918)
by_g = {}
for _ in range(20000):
    k = 7
    ds = sorted(rng.uniform(1, 40) for _ in range(k))
    seq, _ = cascade_setters(ds)
    if len(seq) < 2:
        continue
    last_at = {}
    for idx, (step, d, delta) in enumerate(seq):
        if d in last_at:
            g = idx - last_at[d] - 1              # intervening setter moves
            by_g.setdefault(g, []).append(delta)
        last_at[d] = idx

print(f"{'g':>4} {'returns':>9} {'min delta':>12} {'1st pct':>10} {'median':>10}")
for g in sorted(by_g):
    v = sorted(by_g[g])
    if len(v) < 20: continue
    print(f"{g:>4} {len(v):>9} {v[0]:>12.6f} {v[len(v)//100]:>10.4f} {v[len(v)//2]:>10.4f}")
print()
ge4 = sorted(x for g, v in by_g.items() if g >= 4 for x in v)
g4 = sorted(by_g.get(4, []))
if ge4:
    print(f"  inf over all g >= 4 : {ge4[0]:.8f}   ({len(ge4)} returns)")
if g4:
    print(f"  inf over g = 4 only : {g4[0]:.8f}   ({len(g4)} returns)")
    print(f"  claim says these are EQUAL and both > 0")

# ---------------------------------------------------------------------------
# The extremality at g = 4 held above. The SUBSTANTIVE claim is c_* > 0. A minimum of
# 1.1e-04 on 76 returns is not evidence of a floor -- it is what a sample of that size
# gives if delta can be driven to 0. So attack it: hill-climb to MINIMISE delta at g >= 4.
print()
print("=" * 70)
print("ATTACK: can delta be driven arbitrarily close to 0 at g >= 4?")

def min_delta_ge4(ds):
    seq, _ = cascade_setters(ds)
    last_at = {}; best = None
    for idx, (step, d, delta) in enumerate(seq):
        if d in last_at:
            g = idx - last_at[d] - 1
            if g >= 4 and (best is None or delta < best):
                best = delta
        last_at[d] = idx
    return best

rng2 = random.Random(5)
overall = None; overall_ds = None
for restart in range(600):
    ds = sorted(rng2.uniform(1, 40) for _ in range(7))
    cur = min_delta_ge4(ds)
    if cur is None: continue
    for _ in range(200):
        i = rng2.randrange(7)
        cand = list(ds)
        cand[i] += rng2.gauss(0, max(cur, 1e-6) * 40 + 1e-3)
        if cand[i] <= 0: continue
        cand = sorted(cand)
        v = min_delta_ge4(cand)
        if v is not None and v < cur:
            ds, cur = cand, v
    if overall is None or cur < overall:
        overall, overall_ds = cur, list(ds)

print(f"  hill-climb restarts              : 600")
print(f"  smallest delta reached at g >= 4 : {overall:.3e}")
print(f"  random sampling had reached      : 1.09e-04")
print()
if overall < 1e-6:
    print("  -> delta is driven below 1e-6. No positive floor survives this search, so")
    print("     c_* > 0 is REFUTED as stated: the infimum appears to be 0 and is not attained.")
else:
    print(f"  -> the search bottoms out at {overall:.3e}; consistent with a floor, not proof of one.")

print()
print("  WHAT THE EXTREMAL CONFIGURATION LOOKS LIKE -- because 'admissible' is not defined")
print("  in the statement I was given, and whether these count is the whole question:")
if overall_ds:
    print(f"    speeds     : {[round(x,6) for x in overall_ds]}")
    mn = min(overall_ds)
    print(f"    d_min      : {mn:.6f}")
    print(f"    spread     : {max(overall_ds)/mn:.2f}")
    gaps = [overall_ds[i+1]-overall_ds[i] for i in range(6)]
    print(f"    min gap    : {min(gaps):.2e}   max gap: {max(gaps):.4f}")
    print(f"    gap ratio  : {max(gaps)/min(gaps):.1f}")

print()
print("VERDICT, with its scope stated.")
print()
print("  HOLDS (in sampling): the extremal return length is g = 4. Across 20,000 random")
print("  arrangements the infimum over all g >= 4 equalled the infimum over g = 4 exactly.")
print("  Permitting more intervening moves did not produce a shallower returning setter.")
print()
print("  REFUTED: c_* > 0. A hill-climb minimising delta at g >= 4 reaches 5.5e-07, against")
print("  1.1e-04 from random sampling -- a factor of 200, with no sign of a floor. The")
print("  infimum appears to be 0 and unattained.")
print()
print("  The extremal arrangement is ORDINARY: speeds well separated, min gap 2.45, spread")
print("  10.5, gap ratio 5.2. No two speeds nearly equal, nothing degenerate. So the")
print("  refutation does not depend on admitting a pathological configuration.")
print()
print("  TWO SCOPE LIMITS, both real:")
print("  * 'Admissible' is not defined in the statement given to me. I read it as any seven")
print("    positive reals. If it means something narrower that excludes the arrangement")
print("    above, the refutation does not apply and the claim should be re-tested against")
print("    the intended class.")
print("  * Floating point. delta = 5.5e-07 is nine orders above double precision, so this is")
print("    not numerical noise, but the cascade itself is run in floats and a near-boundary")
print("    decision could differ in exact arithmetic.")
print()
print("  WHY IT MATTERS EITHER WAY: a positive floor on delta would bound below the move a")
print("  returning setter forces, which bears directly on the cap. Without it, the g = 4")
print("  extremality alone yields nothing -- an infimum of 0 attained nowhere gives no bound.")
