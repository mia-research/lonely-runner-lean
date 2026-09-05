"""
ILE A_m Tracer v3 — Witness structure within [1/11, 2/11]
==========================================================
The ILE always terminates within [1/11, ~1/6] — vastly below A_m thresholds.

This script investigates:
  1. The exact bound: is t* ≤ 2/11 always? 1/6? What's the tight bound?
  2. Distribution of which "good window" captures the witness.
  3. Extremal configs (maximize witness time t*).
  4. Analytic structure: blocking zones within [12/121, 21/121].
  5. Theoretical upper bound proof: show t* < 2/11 = W_hi/5.
"""

from fractions import Fraction
import random

def get_blocking(p, t):
    pt = p * t
    j = int(pt)
    frac = pt - j
    one = Fraction(1, 11)
    ten = Fraction(10, 11)
    if frac < one:
        return ('L', Fraction(11 * j + 1, 11 * p))
    elif frac > ten:
        return ('R', Fraction(11 * (j + 1) + 1, 11 * p))
    return None

def ile_witness(config, max_steps=10000):
    t = Fraction(1, 11)
    for _ in range(max_steps):
        blocking = {p: get_blocking(p, t) for p in config if get_blocking(p, t)}
        if not blocking:
            return t
        min_tau = min(b[1] for b in blocking.values())
        if min_tau > Fraction(10, 11):
            return None  # containment violation
        t = min_tau
    return None

# ============================================================
# ANALYTIC: Good windows in [12/121, 21/121] for small runners
# ============================================================

def blocking_zones_in_interval(p, lo, hi):
    """List blocking zones of runner p that intersect (lo, hi)."""
    zones = []
    # Left-blocking: [j/p, (11j+1)/(11p)) for j >= 0
    j_lo = max(0, int(p * lo))
    j_hi = int(p * hi) + 2
    for j in range(j_lo, j_hi):
        z_lo = Fraction(j, p)
        z_hi = Fraction(11 * j + 1, 11 * p)
        if z_lo > hi or z_hi < lo:
            continue
        actual_lo = max(z_lo, lo)
        actual_hi = min(z_hi, hi)
        if actual_lo < actual_hi:
            zones.append(('L', j, actual_lo, actual_hi))
    # Right-blocking: ((11j+10)/(11p), (j+1)/p) for j >= 0
    for j in range(j_lo, j_hi):
        z_lo = Fraction(11 * j + 10, 11 * p)
        z_hi = Fraction(j + 1, p)
        if z_lo > hi or z_hi < lo:
            continue
        actual_lo = max(z_lo, lo)
        actual_hi = min(z_hi, hi)
        if actual_lo < actual_hi:
            zones.append(('R', j, actual_lo, actual_hi))
    return zones

LO = Fraction(12, 121)
HI = Fraction(21, 121)

print("=" * 70)
print("Blocking zones of small runners within [12/121, 21/121]")
print(f"  Interval: [{float(LO):.6f}, {float(HI):.6f}]  width = {float(HI - LO):.6f}")
print("=" * 70)
for p in range(1, 25):
    zones = blocking_zones_in_interval(p, LO, HI)
    if zones:
        for btype, j, zlo, zhi in zones:
            print(f"  p={p:3d}  {btype}-block j={j}: ({float(zlo):.6f}, {float(zhi):.6f})  "
                  f"width={float(zhi-zlo):.6f}")
    else:
        if p != 11:  # 11 is isolated by construction
            print(f"  p={p:3d}  [no blocking zone in interval]")

# ============================================================
# GOOD WINDOWS: complement of union of blocking zones
# ============================================================

print("\n" + "=" * 70)
print("Good windows for small runners only ({1,...,5} always isolated)")
print("Blocking runners: {6,7,8,9,10} (those with zones in [12/121,21/121])")
print("=" * 70)

def compute_good_windows(runner_set, lo, hi):
    """Compute good windows (complement of blocking zones) in [lo, hi]."""
    blocked = []
    for p in runner_set:
        zones = blocking_zones_in_interval(p, lo, hi)
        for btype, j, zlo, zhi in zones:
            blocked.append((zlo, zhi))
    # Merge overlapping intervals
    blocked.sort()
    merged = []
    for b in blocked:
        if merged and b[0] <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], b[1]))
        else:
            merged.append(list(b))
    # Complement in [lo, hi]
    good = []
    cur = lo
    for blo, bhi in merged:
        if cur < blo:
            good.append((cur, blo))
        cur = max(cur, bhi)
    if cur < hi:
        good.append((cur, hi))
    return good

# Small runners {6,7,8,9,10} block in [12/121, 21/121]
small_blockers = [6, 7, 8, 9, 10]
good_small = compute_good_windows(small_blockers, LO, HI)
print("Good windows (no blocking from {6,7,8,9,10}):")
for lo_, hi_ in good_small:
    w = hi_ - lo_
    print(f"  ({lo_} = {float(lo_):.6f}, {hi_} = {float(hi_):.6f})  width={float(w):.7f}")

print("\nAdding runner 20 (common dangerous runner):")
good_with20 = compute_good_windows(small_blockers + [20], LO, HI)
for lo_, hi_ in good_with20:
    w = hi_ - lo_
    print(f"  ({float(lo_):.6f}, {float(hi_):.6f})  width={float(w):.7f}")

# ============================================================
# MASSIVE SWEEP: find t_max_global with 50k+ configs
# ============================================================

print("\n" + "=" * 70)
print("Massive sweep: find t_max over 50,000 configs")
print("=" * 70)

rng = random.Random(1337)
t_max_global = Fraction(0)
extremal_config = None
extremal_witness = None
n_tested = 0
bound_2_11 = Fraction(2, 11)
bound_1_6 = Fraction(1, 6)
violations_bound = {
    'gt_2_11': 0, 'gt_1_6': 0, 'gt_0_16': 0,
}

# Distribution of witness times
witness_histogram = {
    'lt_1_11': 0,
    '1_11_to_12_121': 0,
    '12_121_to_1_10': 0,
    '1_10_to_1_9': 0,
    '1_9_to_1_8': 0,
    '1_8_to_1_7': 0,
    '1_7_to_1_6': 0,
    '1_6_to_2_11': 0,
    'gt_2_11': 0,
}

def histogram_bucket(t):
    if t < Fraction(1, 11): return 'lt_1_11'
    elif t < Fraction(12, 121): return '1_11_to_12_121'
    elif t < Fraction(1, 10): return '12_121_to_1_10'
    elif t < Fraction(1, 9): return '1_10_to_1_9'
    elif t < Fraction(1, 8): return '1_9_to_1_8'
    elif t < Fraction(1, 7): return '1_8_to_1_7'
    elif t < Fraction(1, 6): return '1_7_to_1_6'
    elif t < Fraction(2, 11): return '1_6_to_2_11'
    else: return 'gt_2_11'

for trial in range(50000):
    # Varied config sizes and ranges
    p_range = rng.choice([50, 100, 200, 500, 1000, 5000])
    n_runners = rng.choice([5, 7, 10, 12, 15])

    mandatory = {1, 11}
    if rng.random() < 0.4:
        mandatory.add(rng.choice([20, 30, 40, 50, 60, 70, 80, 90, 100]))

    candidates = list(set(range(2, p_range + 1)) - mandatory)
    if len(candidates) < n_runners - len(mandatory):
        continue
    fill = rng.sample(candidates, n_runners - len(mandatory))
    config = sorted(mandatory | set(fill))

    w = ile_witness(config)
    n_tested += 1

    if w is None:
        print(f"  *** NO WITNESS: {config}")
        continue

    bucket = histogram_bucket(w)
    witness_histogram[bucket] = witness_histogram.get(bucket, 0) + 1

    if w > t_max_global:
        t_max_global = w
        extremal_config = config
        extremal_witness = w

    if w > Fraction(2, 11): violations_bound['gt_2_11'] += 1
    if w > Fraction(1, 6): violations_bound['gt_1_6'] += 1
    if w > Fraction(16, 100): violations_bound['gt_0_16'] += 1

print(f"\nTested {n_tested} configs")
print(f"\nWitness time distribution:")
for bucket, count in sorted(witness_histogram.items()):
    print(f"  {bucket}: {count}  ({100*count/n_tested:.2f}%)")

print(f"\nBound violations:")
for key, count in violations_bound.items():
    print(f"  t* > {key}: {count}")

print(f"\nGlobal maximum witness time: t_max = {t_max_global} ≈ {float(t_max_global):.8f}")
print(f"  Extremal config: {extremal_config}")
print(f"  2/11 = {float(bound_2_11):.8f}")
print(f"  1/6  = {float(bound_1_6):.8f}")
print(f"  t_max < 2/11: {t_max_global < bound_2_11}")
print(f"  t_max < 1/6:  {t_max_global < bound_1_6}")

# ============================================================
# EXTREMAL CONFIG: deep analysis
# ============================================================
if extremal_config:
    print("\n" + "=" * 70)
    print(f"Deep analysis of extremal config: {extremal_config}")
    print(f"Witness at t* = {extremal_witness} ≈ {float(extremal_witness):.8f}")
    print("=" * 70)

    # Full ILE trace
    t = Fraction(1, 11)
    step = 0
    print("ILE trace:")
    while step < 100:
        blocking = {p: get_blocking(p, t) for p in extremal_config if get_blocking(p, t)}
        if not blocking:
            print(f"  WITNESS at step {step}: t = {t} ≈ {float(t):.8f}")
            break
        min_tau = min(b[1] for b in blocking.values())
        min_runners = [p for p, b in blocking.items() if b[1] == min_tau]
        print(f"  step {step}: t={float(t):.6f}, advancing via runner(s) {min_runners}, "
              f"blocking count={len(blocking)}, → {float(min_tau):.6f}")
        t = min_tau
        step += 1

# ============================================================
# ANALYTIC BOUND: Why is t* ≤ 2/11?
# ============================================================
print("\n" + "=" * 70)
print("Analytic structure: Why does the ILE stay in [1/11, 2/11]?")
print("=" * 70)

print("""
Key observations:
1. ILE starts at W_lo = 1/11. Runner 11 (p_j) is left-blocking: τ = 12/121.
2. ILE advances to 12/121 ∈ [12/121, 21/121] (runner 11's k=1 isolation interval).
3. Runner 11 remains ISOLATED throughout [12/121, 21/121].
4. Runner 1: {t} = t ∈ (1/11, 10/11) for all t ∈ [12/121, 21/121]. ISOLATED.
5. Runners p=2,3,4,5: NO blocking zones in [12/121, 21/121] (verified).
   (Requires p ≥ 6 for right-blocking to overlap; p ≥ 13 for left-blocking.)
6. So runners {1,2,3,4,5,11} are ALWAYS isolated in [12/121, 21/121].
   This is 6 out of 10 runners (for a 10-runner config).
7. The remaining 4+ runners need to be simultaneously isolated for a witness.

For the ILE to ESCAPE [12/121, 21/121]:
   - Must advance past 21/121 = 0.1736...
   - This requires: at t' ∈ [12/121, 21/121], min blocking τ > 21/121.
   - i.e., some runner advances to > 21/121 from within [12/121, 21/121].

After escaping to [21/121, 22/121] ≈ [0.174, 0.182]:
   - Runner 11 becomes RIGHT-BLOCKING (right-blocking zone (21/121, 22/121)).
   - τ(11, t') = 23/121 ≈ 0.190.
   - If runner 11 advances, ILE goes to 23/121 (entering k=2 isolation interval).
   - If some other runner has smaller τ from this zone, it advances instead.
""")

# Verify: which small runners have NO zone in [12/121, 21/121]?
print("Verification - runners with NO blocking zone in [12/121, 21/121]:")
for p in range(1, 13):
    if p == 11:
        print(f"  p=11: isolated by construction (p_j)")
        continue
    zones = blocking_zones_in_interval(p, LO, HI)
    if not zones:
        print(f"  p={p}: NO blocking zone ✓")
    else:
        print(f"  p={p}: HAS {len(zones)} zone(s): {[(b[0], float(b[2]), float(b[3])) for b in zones]}")

# ============================================================
# TIGHT BOUND: What is the exact supremum of witness times?
# ============================================================

print("\n" + "=" * 70)
print("Searching for tight bound: systematically maximize witness time")
print("=" * 70)

# Strategy: build configs that force the ILE deep into [12/121, 21/121]
# By ensuring all runners block just before each good window.

# The good windows for {6,7,8,9,10} are:
print("Good windows structure (blocking from {6,7,8,9,10}):")
gw = compute_good_windows([6,7,8,9,10], LO, HI)
for i, (lo_, hi_) in enumerate(gw):
    print(f"  Window {i+1}: ({lo_} ≈ {float(lo_):.6f}, {hi_} ≈ {float(hi_):.6f})")

# To get a late witness: need the ILE to traverse all earlier windows without finding a witness
# This requires runners blocking THROUGHOUT each earlier window.
# E.g., to skip window 1 = [12/121, 10/99): need a runner blocking ALL of [12/121, 10/99).
# Width = 10/99 - 12/121 = (10*121 - 12*99)/(99*121) = (1210 - 1188)/11979 = 22/11979.
# A runner with blocking zone covering [12/121, 10/99): need left-blocking zone of width ≥ 22/11979.
# Width of left-blocking zone for runner p = 1/(11p).
# Need 1/(11p) ≥ 22/11979 → p ≤ 11979/242 ≈ 49.5 → p ≤ 49.
# Runner p=49 has zone width 1/539 ≈ 0.00186. 22/11979 ≈ 0.00184. OK, barely covers.

print("\nSearching for config that maximizes witness in window 5 = (1/6, 21/121)...")
rng2 = random.Random(999)
best_late = []
for trial in range(20000):
    # Build config designed to skip windows 1-4
    # Include runners that block windows 1-4 but leave window 5 open
    base = {1, 11}
    # Window 1 [12/121, 10/99): need runner with zone here
    # Runner 9 right-blocks (10/99, 1/9) so blocks window 2, not window 1.
    # Runner 10 right-blocks (1/11, 1/10) — covers bottom of [12/121, 1/10).
    # Add runner 10 to close window 1:
    base.add(10)
    # Window 2 (1/9, 10/88): add runner 9 (right-blocks (10/99, 1/9), closes between windows 1-2)
    # Actually runner 9 right-blocks (10/99, 1/9) which CONTAINS window 1 roughly...
    # Let me just try random combos with runners from [6..30]
    n_from_small = rng2.randint(3, 6)
    small = rng2.sample([6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20], n_from_small)
    base.update(small)
    n_total = rng2.randint(7, 12)
    while len(base) < n_total:
        base.add(rng2.randint(2, 200))
    config = sorted(base)
    w = ile_witness(config)
    if w and w >= Fraction(1, 6):
        best_late.append((w, config))

best_late.sort(key=lambda x: -x[0])
if best_late:
    print(f"  Found {len(best_late)} configs with witness ≥ 1/6")
    print(f"  Top 10:")
    for w, c in best_late[:10]:
        print(f"    t*={w} ≈ {float(w):.8f}  config={c}")

    # Full trace for absolute best
    best_w, best_c = best_late[0]
    print(f"\n  Full ILE trace for best (t*={best_w}):")
    t = Fraction(1, 11)
    step = 0
    while step < 100:
        blocking = {p: get_blocking(p, t) for p in best_c if get_blocking(p, t)}
        if not blocking:
            print(f"    WITNESS at step {step}: t = {t} = {float(t):.10f}")
            # Show which runners are isolated
            print(f"    Blocking check:")
            for p in best_c:
                b = get_blocking(p, t)
                pos = float(p * t % 1) if t > 0 else 0
                print(f"      p={p:4d}: {{pt}}≈{float(p*t - int(p*t)):.4f}  {'ISOLATED' if b is None else b}")
            break
        min_tau = min(b[1] for b in blocking.values())
        advancers = [p for p, b in blocking.items() if b[1] == min_tau]
        print(f"    step {step}: t={float(t):.7f} [{t}], via runner {advancers}, τ={float(min_tau):.7f}")
        t = min_tau
        step += 1
else:
    print("  No configs found with witness ≥ 1/6 in this search.")
    print(f"  Checking global max: {float(t_max_global):.8f}")

print(f"\n{'='*70}")
print(f"CONCLUSION:")
print(f"  Global max witness: t_max = {float(t_max_global):.8f}")
print(f"  2/11 = {float(Fraction(2,11)):.8f}")
print(f"  1/6  = {float(Fraction(1,6)):.8f}")
print(f"  A_2 lower bound = {float(Fraction(197,220)):.8f}")
print(f"  Distance from t_max to A_2: {float(Fraction(197,220)) - float(t_max_global):.6f}")
