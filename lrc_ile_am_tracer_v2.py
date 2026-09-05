"""
ILE A_m Tracer v2 — Distribution of witness times and approach to W_hi
=======================================================================
Focus:
  1. What is the distribution of witness times across configs?
  2. What is the MAXIMUM ILE state (t_max) reached before a witness?
  3. Find configs that push t_max closest to A_m thresholds (~0.895).
  4. Understand WHY the ILE always terminates far from A_m.
  5. Try to force the ILE deep into [0.5, W_hi) by adversarial design.
"""

from fractions import Fraction
import random
from collections import defaultdict

# ---- ILE core (same as v1, extract min version) ----

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


def ile_stats(config, max_steps=200000):
    """Run ILE, return (witness, t_max_reached, n_steps, trace_snippet_near_A)."""
    W_hi = Fraction(10, 11)
    A2_lo = Fraction(99*2-1, 110*2)  # ≈0.8954
    t = Fraction(1, 11)
    t_max = t
    n_steps = 0
    trace_near_A = []

    for _ in range(max_steps):
        blocking = {}
        for p in config:
            b = get_blocking(p, t)
            if b:
                blocking[p] = b
        if not blocking:
            return t, t_max, n_steps, trace_near_A  # witness
        min_tau = min(b[1] for b in blocking.values())
        if min_tau > W_hi:
            return None, t_max, n_steps, trace_near_A  # containment violation
        if t > A2_lo:
            trace_near_A.append((t, {p: b for p, b in blocking.items()}))
        t = min_tau
        if t > t_max:
            t_max = t
        n_steps += 1

    return None, t_max, n_steps, trace_near_A


# ---- Design configs specifically to push ILE high ----

def blocking_density_at_t(config, t):
    """Count blocking runners at t."""
    return sum(1 for p in config if get_blocking(p, t) is not None)


# Strategy: make ALL runners have blocking zones near W_lo (1/11),
# so early witnesses are impossible, forcing the ILE higher.
# For runner p, left-blocking near 1/11: {p/11} < 1/11, i.e., p ≡ 0 (mod 11).
# But p_j=11 is already there. Others: p = 22, 33, 44, ...
# Right-blocking near 1/11: {p/11} > 10/11, i.e., p ≡ 10 (mod 11), i.e., p ∈ {10,21,32,...}.

def push_configs_by_density(n_runners=10, n_configs=2000, seed=10):
    """Generate configs where many runners are blocking near W_lo to push ILE higher."""
    rng = random.Random(seed)
    configs = []

    for _ in range(n_configs * 5):
        if len(configs) >= n_configs:
            break
        # Include runner 11 (p_j) and runners that are blocking near 1/11
        # Right-blocking near 1/11: p ≡ 10 mod 11 → p ∈ {10, 21, 32, 43, ...}
        # Left-blocking near 1/11: p ≡ 0 mod 11 → p ∈ {11, 22, 33, ...} (already have 11)
        base = {1, 11}
        # Add some right-blocking runners near 1/11 (will push t up)
        rb_near = [10 + 11*k for k in range(0, 10)]  # 10, 21, 32, 43, 54, 65, 76, 87, 98, 109
        to_add = rng.sample(rb_near[:8], min(rng.randint(2, 5), 8))
        base.update(to_add)
        # Add runner 20 (dangerous mult-of-10)
        base.add(20)
        # Fill to n_runners
        while len(base) < n_runners:
            p = rng.randint(2, 500)
            base.add(p)
        config = sorted(base)[:n_runners]
        configs.append(config)

    return configs


def adversarial_blocking_configs():
    """
    Configs where every runner has a blocking zone near W_lo,
    forcing the ILE to step past W_lo repeatedly.
    """
    configs = []

    # Config 1: All runners ≡ 0 or 10 (mod 11) near W_lo
    # p ≡ 0 (mod 11): 11, 22, 33, 44, 55, 66, 77, 88, 99, 110
    # But p_j=11 and 22,33 etc. are not necessarily p_1=1
    # With p_1=1: need 10-runner set including 1 and 11
    c = [1, 10, 11, 20, 21, 22, 32, 33, 43, 44]  # mix of mod-11 residues
    configs.append(sorted(c))

    # Config 2: 1, 11 + many multiples of 11 (force blocking at many t=k/11)
    c = [1, 11, 22, 33, 44, 55, 66, 77, 88, 99]
    configs.append(sorted(c))

    # Config 3: Pacemaker-like: 1, 10, 11, 12, ..., 19
    c = list(range(1, 12)) + [20]  # 1..11 + 20 = 12 items, trim
    configs.append(sorted(c[:10]))

    # Config 4: 1, 11, then very closely spaced runners to create many blocking events
    # p = 220, 221, 222, ..., 228 (9 runners near 220)
    c = [1, 11] + list(range(220, 229))
    configs.append(sorted(c[:10]))

    # Config 5: Designed to have blocking runners at t ≈ 0.5 (push through middle)
    # Want {p*0.5} near 0 or 1. {p/2} < 1/11 → p even and near even multiples.
    # Actually {p/2} = 0 for even p, so all even runners are left-blocking at t=1/2.
    c = [1, 2, 4, 6, 8, 10, 11, 20, 22, 44]
    configs.append(sorted(c))

    # Config 6: All runners ≡ 1 (mod 2) — odd runners, avoid easy witnesses at 1/2
    c = [1, 3, 5, 7, 9, 11, 13, 15, 17, 19]
    configs.append(sorted(c))

    # Config 7: Mix specifically targeting t ≈ 0.8
    # {p*0.8} < 1/11 → p*4/5 near integer → p ≡ 0 (mod 5)
    c = [1, 5, 10, 11, 15, 20, 25, 30, 35, 40]
    configs.append(sorted(c))

    # Config 8: Very spaced runners (p_10 >> p_1)
    c = [1, 11, 20, 100, 200, 300, 400, 500, 600, 700]
    configs.append(sorted(c))

    # Config 9: The "worst case" for pacemaker (Case R>, p10/p1 very large)
    c = [1, 11, 20, 1100, 1200, 1300, 1400, 1500, 1600, 1700]
    configs.append(sorted(c))

    # Config 10: All runners that are blocking at t = 9/10 - epsilon
    # (near A_2 threshold)
    # Want runners blocking just below 9/10.
    # Runner p right-blocking at t=0.89: {0.89p} > 10/11
    # Runner p left-blocking at t=0.89: {0.89p} < 1/11
    # From analysis: multiples of 10 are right-blocking. Let's add many:
    c = [1, 10, 11, 20, 30, 40, 50, 60, 70, 80]  # multiples of 10
    configs.append(sorted(c))

    return configs


# ---- Main: find configs with large t_max ----

print("=" * 70)
print("ILE A_m Tracer v2 — Searching for configs with large t_max")
print("=" * 70)

# Collect t_max distribution
all_results = []

print("\n[A] Testing adversarial blocking configs...")
adv2 = adversarial_blocking_configs()
for config in adv2:
    w, t_max, nsteps, trace = ile_stats(config)
    all_results.append((t_max, config, w, nsteps))
    status = f"witness={float(w):.4f}" if w else "NO WITNESS"
    print(f"  t_max={float(t_max):.5f} ({nsteps} steps), {status}: {config}")

print("\n[B] Push configs (runners blocking near W_lo)...")
push = push_configs_by_density(n_runners=10, n_configs=3000, seed=10)
push_results = []
for config in push:
    w, t_max, nsteps, trace = ile_stats(config)
    push_results.append((t_max, config, w, nsteps))

# Sort by t_max descending
push_results.sort(key=lambda x: -x[0])
print(f"  Top 10 by t_max:")
for t_max, config, w, nsteps in push_results[:10]:
    status = f"w={float(w):.5f}" if w else "NO WITNESS"
    print(f"  t_max={float(t_max):.6f}  steps={nsteps}  {status}  {config}")

all_results.extend(push_results)

print("\n[C] Large random sweep (p_10 up to 5000, including dangerous runners)...")
rng = random.Random(42)
sweep_results = []
for trial in range(5000):
    # Random config with p_j=11 and p_10 in [11, 5000]
    p10 = rng.randint(11, 5000)
    mandatory = {1, 11}
    # Sometimes add a dangerous runner
    if rng.random() < 0.5:
        m = rng.randint(2, 10)
        mandatory.add(10 * m)
    candidates = list(set(range(2, p10)) - mandatory)
    if len(candidates) < 8 - len(mandatory) + 2:
        continue
    n_fill = 10 - len(mandatory) - 1
    fill = rng.sample(candidates, n_fill)
    config = sorted(mandatory | set(fill) | {p10})
    if len(config) != 10:
        continue
    w, t_max, nsteps, trace = ile_stats(config)
    sweep_results.append((t_max, config, w, nsteps, trace))

sweep_results.sort(key=lambda x: -x[0])
print(f"\n  Distribution of t_max (5000 configs):")
A2_lo = float(Fraction(99*2-1, 110*2))
thresholds = [0.5, 0.7, 0.8, 0.85, 0.87, 0.89, A2_lo, 0.9, 0.91]
for thresh in thresholds:
    count = sum(1 for t, *_ in sweep_results if float(t) >= thresh)
    print(f"    t_max >= {thresh:.4f}: {count} configs ({100*count/len(sweep_results):.1f}%)")

print(f"\n  Top 20 by t_max:")
for t_max, config, w, nsteps, trace in sweep_results[:20]:
    status = f"w={float(w):.5f}" if w else "NO WITNESS"
    a2 = "IN_A2!" if float(t_max) > A2_lo else ""
    print(f"  t_max={float(t_max):.6f}  steps={nsteps}  {status}  {a2}  {config[:6]}...")

# ---- Detailed analysis of top-t_max configs ----
print("\n[D] Detailed analysis of configs with t_max > 0.85...")
A2_lo_frac = Fraction(99*2-1, 110*2)
high_configs = [(t, c, w, n, tr) for t, c, w, n, tr in sweep_results if t > Fraction(85, 100)]
print(f"  Found {len(high_configs)} configs with t_max > 0.85")
for t_max, config, w, nsteps, trace in high_configs[:5]:
    print(f"\n  Config: {config}")
    print(f"  t_max: {t_max} ≈ {float(t_max):.7f}")
    print(f"  Witness: {w} ≈ {float(w):.7f}" if w else "  No witness (violation?)")
    print(f"  Steps: {nsteps}")
    if trace:
        print(f"  Near-A_m states: {len(trace)}")
        for t_state, blk in trace[:3]:
            right_m10 = [(p, float(tau)) for p,(tp,tau) in blk.items() if tp=='R' and p%10==0]
            left_nm10 = [(p, float(tau)) for p,(tp,tau) in blk.items() if tp=='L' and p%10!=0]
            print(f"    t={float(t_state):.6f}: right_mult10={right_m10}, left_non10={left_nm10}")

# ---- Special investigation: exclude early witnesses ----
print("\n[E] Forcing no early witness: configs where all runners block at t=1/11...")
# At t=1/11:
# Runner p is left-blocking iff {p/11} < 1/11, i.e., p ≡ 0 (mod 11)
# Runner p is right-blocking iff {p/11} > 10/11, i.e., p ≡ 10 (mod 11) [i.e., p mod 11 = 10]
# For NO early witness at t=1/11: all runners must be blocking there.
# Only possible if all p ≡ 0 or ≡ 10 (mod 11).
# But p_j = 11 ≡ 0 (mod 11) is left-blocking at t=1/11. ✓
# Others: p ≡ 0 (mod 11): 22, 33, 44, ... | p ≡ 10 (mod 11): 10, 21, 32, 43, ...

def all_blocking_at_wlo_configs(n_runners=10, p_max=300):
    """Configs where every runner is blocking at t = W_lo = 1/11."""
    mod0 = [11*k for k in range(1, p_max//11 + 1)]  # 11, 22, 33,...
    mod10 = [10 + 11*k for k in range(0, (p_max-10)//11 + 1)]  # 10, 21, 32,...
    all_blocking_p = sorted(set(mod0 + mod10))
    # Must include 1? No, runner 1: {1/11} = 1/11, NOT < 1/11. So runner 1 is isolated at 1/11.
    # Skip runner 1 if it would be isolated.
    # Actually, p_1 = 1 is required by convention. Let's check: {1/11} = 1/11 exactly.
    # frac = 1/11. frac < 1/11? NO. So runner 1 is isolated at 1/11. A witness at 1/11 requires
    # ALL runners isolated, but runner 11 blocks. So 1/11 is not a witness regardless.
    # We want configs where the ILE has to step several times before finding a witness.
    # Build from all_blocking_p, always include {1, 11}.
    configs = []
    # Remove 1 from all_blocking_p (p=1 is isolated at 1/11)
    pool = [p for p in all_blocking_p if p > 1]
    # Generate all combos of size n_runners-1 from pool (include 1 always)
    import itertools
    for combo in itertools.combinations(pool[:20], n_runners - 1):
        c = sorted({1} | set(combo))
        if len(c) != n_runners:
            continue
        # Must satisfy Case R>: p_10 >= 11 * p_1 = 11
        if c[-1] >= 11:
            configs.append(c)
        if len(configs) >= 200:
            break
    return configs

all_blk_configs = all_blocking_at_wlo_configs()
print(f"  Generated {len(all_blk_configs)} all-blocking-at-W_lo configs")
ab_results = []
for config in all_blk_configs:
    w, t_max, nsteps, trace = ile_stats(config)
    ab_results.append((t_max, config, w, nsteps))
ab_results.sort(key=lambda x: -x[0])
print(f"  t_max distribution:")
for thresh in [0.5, 0.7, 0.8, 0.85, 0.87, 0.89, A2_lo]:
    count = sum(1 for t,*_ in ab_results if float(t) >= thresh)
    print(f"    >= {thresh:.4f}: {count}")
print(f"\n  Top 10 by t_max:")
for t_max, config, w, nsteps in ab_results[:10]:
    print(f"  t_max={float(t_max):.6f}  steps={nsteps}  witness={float(w):.5f}  {config}")

# ---- Summary ----
all_combined = all_results + [(t, c, w, n, []) for t,c,w,n in ab_results]
all_combined.sort(key=lambda x: -float(x[0]))
max_t = float(all_combined[0][0]) if all_combined else 0
print(f"\n{'='*70}")
print(f"SUMMARY: maximum t_max observed across ALL investigations:")
print(f"  t_max_global = {float(all_combined[0][0]):.7f}  (config: {all_combined[0][1]})")
print(f"  A_m thresholds: A_2 lo = {A2_lo:.7f}, 9/10 = {0.9:.7f}")
print(f"  Gap to A_2: {A2_lo - max_t:.6f}")
