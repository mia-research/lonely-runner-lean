#!/usr/bin/env python3
# APPLY the frozen difference-set character test to the real 82.
# Exact integer signal path (int pow Legendre). Decision vs FROZEN region [-115, +111].
import csv, random, bisect
random.seed(20260726)

P   = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
QUA = (P - 1) // 2
BASE   = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation"
SCR    = "/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/c9342981-88ed-4087-91d0-dfebd9a02142/scratchpad"

def leg(z):                      # exact integer Legendre symbol (z|P)
    z %= P
    if z == 0: return 0
    r = pow(z, QUA, P)
    if r == 1: return 1
    if r == P - 1: return -1
    raise ValueError("not +-1")

def sdiff(xs):                   # signed j<k difference-set character sum (frozen orientation)
    S = 0; n = len(xs)
    for j in range(n):
        xj = xs[j]
        for k in range(j + 1, n):
            S += leg(xj - xs[k])
    return S

# ---- REAL 82, ascending bit-length (frozen ordering) ----
real = []
with open(f"{BASE}/solved_puzzles_xy.csv") as f:
    for r in csv.DictReader(f):
        real.append((int(r["bits"]), int(r["X"], 16)))
real.sort(key=lambda t: t[0])
assert len(real) == 82 and len({t[0] for t in real}) == 82, "need 82 distinct bit-lengths"
xs_real = [x for _, x in real]

S_real = sdiff(xs_real)
print("################  APPLY: real 82  ################")
print(f"S_diff(real)      = {S_real}")
print(f"S_diff(real)^2    = {S_real*S_real}")
print(f"odd? (must be)    = {S_real % 2 != 0}")

# ---- FROZEN null (seed 20260726, from pre-registration) ----
with open(f"{SCR}/frozen_null_seed20260726.txt") as f:
    null = sorted(int(t) for t in f if t.strip())
n = len(null)
mean = sum(null) / n
var  = sum((v - mean)**2 for v in null) / n
L, U = -115, 111                                   # FROZEN region
print("\n################  frozen null (verify artifact)  ################")
print(f"n={n}  mean={mean:.2f}  sigma={var**0.5:.2f}  min/max={null[0]}/{null[-1]}  all_odd={all(v%2 for v in null)}")
print(f"order-stat check: 250th smallest={null[249]} (=>L={L}?)  9751st smallest={null[9750]} (=>U={U}?)")

# ---- decision vs FROZEN region + two-sided rank p ----
le = bisect.bisect_right(null, S_real)   # #{null <= S}
ge = n - bisect.bisect_left(null, S_real) # #{null >= S}
p_two = (1 + 2*min(le, ge)) / (n + 1)
inside = (L <= S_real <= U)
print("\n################  DECISION (frozen rule)  ################")
print(f"frozen reject region: S_diff < {L} or > {U}")
print(f"S_diff(real) = {S_real}  ->  {'INSIDE (no reject)' if inside else 'OUTSIDE (REJECT null)'}")
print(f"two-sided rank p = {p_two:.4f}   (percentile: {le/n*100:.1f}% of null <= real)")
band = "MARGINAL (111-115 seed-jitter band)" if 111 <= abs(S_real) <= 115 else "clear of jitter band"
print(f"jitter status: {band}")

# ---- independent cross-check of the frozen null (trust-but-verify) ----
# rebuild control pool by bit-length; regenerate a smaller matched null with a DIFFERENT seed.
print("\n################  independent regen (cross-check, 1500 resamples)  ################")
pool = {}
with open(f"{BASE}/constructed_keys_1to160_100k.csv") as f:
    for r in csv.DictReader(f):
        pool.setdefault(int(r["bits"]), []).append(int(r["X"], 16))
real_bits = [b for b, _ in real]
random.seed(999)
regen = []
for _ in range(1500):
    xs = [random.choice(pool[b]) for b in real_bits]
    regen.append(sdiff(xs))
regen.sort()
m2 = sum(regen)/len(regen); s2 = (sum((v-m2)**2 for v in regen)/len(regen))**0.5
lo2 = regen[int(0.025*len(regen))]; hi2 = regen[int(0.975*len(regen))]
print(f"regen n={len(regen)} (seed 999)  mean={m2:.2f}  sigma={s2:.2f}  2.5%={lo2}  97.5%={hi2}")
print(f"  (frozen said mean~-2.3, sigma~57.69, 2.5%=-115, 97.5%=+111 -> consistent if close)")
