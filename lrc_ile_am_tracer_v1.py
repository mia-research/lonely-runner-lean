"""
ILE A_m State Tracer — Containment Residual Investigation
==========================================================
For Case R> configs with p_j=11 (interior dangerous runner):
  - Traces the ILE (Iterated Left-Entry) algorithm with exact rational arithmetic
  - Detects ILE states in approach windows A_m = ((99m-1)/(110m), 9/10) for m in 2..10
  - For each A_m state: records which runners are blocking (left vs right) and their τ values
  - Flags "dangerous states" where the ONLY blocking runner is a right-blocking mult-of-10

Key theory:
  W_lo = 1/11, W_hi = 10/11, D_11 = (109/121, 10/11)
  A_m = ((99m-1)/(110m), 9/10)  for m = 2,...,10
  Runner 10m right-blocking in A_m → τ = (99m+1)/(110m) ∈ D_11 (dangerous)
  Any left-blocking non-mult-10 runner at t ∈ A_m → τ ≤ 9/10 < D_11_left (safe, by LBS2)
"""

from fractions import Fraction
import itertools
import random
from collections import defaultdict

# ---------- ILE core (exact rational arithmetic) ----------

def get_blocking(p, t):
    """Return (type, tau) if runner p is blocking at time t, else None.
    type: 'L' (left-blocking) or 'R' (right-blocking).
    """
    # fractional position
    # {p*t} = p*t - floor(p*t)
    pt = p * t
    j = int(pt)          # floor
    frac = pt - j        # {p*t}  (exact since Fraction)
    one_over_11 = Fraction(1, 11)
    ten_over_11 = Fraction(10, 11)
    if frac < one_over_11:
        # left-blocking: re-entry at (11j+1)/(11p)
        tau = Fraction(11 * j + 1, 11 * p)
        return ('L', tau)
    elif frac > ten_over_11:
        # right-blocking: advance index is j+1, re-entry at (11*(j+1)+1)/(11p)
        tau = Fraction(11 * (j + 1) + 1, 11 * p)
        return ('R', tau)
    else:
        return None  # isolated


def ile_trace(config, max_steps=50000, verbose=False):
    """
    Run ILE on config (list of positive integers, p_1 first).
    Returns dict with keys:
      'witness': Fraction or None
      'steps': list of (t_cur, blocking_info) dicts
      'am_states': list of states that fell in some A_m
      'dangerous_states': states in A_m with only right-blocking mult-of-10 runners
      'containment_violation': (t, p_b, tau) or None
    """
    n = 11
    W_lo = Fraction(1, 11)
    W_hi = Fraction(10, 11)
    D11_left = Fraction(109, 121)   # = (110*1-1)/(121*1)

    # Approach windows A_m for m=2..10
    # A_m = ((99m-1)/(110m), 9/10)
    A_windows = {}
    for m in range(2, 11):
        lo = Fraction(99 * m - 1, 110 * m)
        hi = Fraction(9, 10)
        A_windows[m] = (lo, hi)

    multiples_of_10 = set(p for p in config if p % 10 == 0)

    t = W_lo
    steps = []
    am_states = []
    dangerous_states = []
    containment_violation = None

    for step in range(max_steps):
        # Check for witness
        blocking = {}
        for p in config:
            b = get_blocking(p, t)
            if b is not None:
                blocking[p] = b

        if not blocking:
            return {
                'witness': t,
                'steps': steps,
                'am_states': am_states,
                'dangerous_states': dangerous_states,
                'containment_violation': None,
                'total_steps': step,
            }

        # Minimum re-entry time
        min_tau = min(b[1] for b in blocking.values())

        # Check containment
        if min_tau > W_hi:
            # Find which runner caused this
            viol_runners = [p for p, b in blocking.items() if b[1] == min_tau]
            containment_violation = (t, viol_runners[0], min_tau)
            return {
                'witness': None,
                'steps': steps,
                'am_states': am_states,
                'dangerous_states': dangerous_states,
                'containment_violation': containment_violation,
                'total_steps': step,
            }

        # Record step
        step_info = {
            't': t,
            'blocking': {p: blocking[p] for p in blocking},
            'min_tau': min_tau,
        }

        # Check if t is in any A_m
        for m, (lo, hi) in A_windows.items():
            if lo < t < hi:
                # Characterize blocking at this state
                left_blockers = [(p, b[1]) for p, b in blocking.items() if b[0] == 'L']
                right_blockers = [(p, b[1]) for p, b in blocking.items() if b[0] == 'R']
                left_non_mult10 = [(p, tau) for p, tau in left_blockers if p % 10 != 0]
                right_mult10 = [(p, tau) for p, tau in right_blockers if p % 10 == 0]

                am_state = {
                    'm': m,
                    't': t,
                    'left_blockers': left_blockers,
                    'right_blockers': right_blockers,
                    'left_non_mult10': left_non_mult10,
                    'right_mult10': right_mult10,
                    'min_tau': min_tau,
                    'is_dangerous': (len(left_non_mult10) == 0 and len(right_mult10) > 0),
                    'tau_in_D11': min_tau > D11_left,
                }
                am_states.append(am_state)

                if am_state['is_dangerous']:
                    dangerous_states.append(am_state)

                break  # t can only be in one A_m (they're nested but at most one matters)

        steps.append(step_info)
        t = min_tau

    return {
        'witness': None,
        'steps': steps,
        'am_states': am_states,
        'dangerous_states': dangerous_states,
        'containment_violation': None,
        'total_steps': max_steps,
        'note': 'max_steps exceeded',
    }


# ---------- Config generators ----------

def configs_with_pj11_and_mult10(
    n_runners=10,
    p10_min=11,     # Case R>: p_10 >= 11
    p10_max=500,
    dangerous_m_range=(2, 11),  # which mult-of-10 runners to include
    extra_runners=None,          # additional runners to force in
    n_configs=1000,
    seed=42,
):
    """Generate random Case R> configs with p_j=11 and at least one runner 10m."""
    rng = random.Random(seed)
    configs = []

    for _ in range(n_configs * 20):
        if len(configs) >= n_configs:
            break

        # Pick a dangerous runner 10m (m in dangerous_m_range)
        m = rng.randint(*dangerous_m_range[:2])
        if m >= dangerous_m_range[1]:
            continue
        dangerous_runner = 10 * m

        # Determine minimum p_10 needed: must be >= 110m for A_m to be reachable
        p10_min_eff = max(p10_min, 110 * m)
        if p10_min_eff > p10_max:
            continue

        # Build config: must include 1, 11, 10m, and p_10 >= 110m
        mandatory = {1, 11, dangerous_runner}
        if extra_runners:
            mandatory.update(extra_runners)

        # Pick p_10 >= p10_min_eff
        p10 = rng.randint(p10_min_eff, p10_max)
        mandatory.add(p10)

        # Fill remaining slots with random runners in (1, p10)
        candidates = list(set(range(2, p10)) - mandatory)
        if len(mandatory) > n_runners:
            continue
        n_fill = n_runners - len(mandatory)
        if n_fill > len(candidates):
            continue

        fill = rng.sample(candidates, n_fill)
        config = sorted(mandatory | set(fill))

        # Verify Case R> and n_runners
        if len(config) != n_runners:
            continue
        if config[-1] < 11 * config[0]:
            continue

        configs.append(config)

    return configs


def adversarial_configs(n_runners=10):
    """Handcrafted configs designed to maximize chance of dangerous A_m states."""
    configs = []

    # Family 1: minimal configs with p_j=11, runner 20, p_10=220 (just barely reachable)
    # + different filler runners
    for filler_set in [
        [2, 3, 4, 5, 6, 7, 8],
        [2, 3, 4, 5, 6, 7, 9],
        [2, 4, 6, 8, 13, 17, 19],
        [3, 7, 13, 17, 19, 21, 23],
    ]:
        c = sorted({1, 11, 20, 220} | set(filler_set))
        if len(c) == n_runners:
            configs.append(c)

    # Family 2: p_j=11, runner 20, p_10=221..300 (avoid guardian 220)
    for p10 in [221, 222, 230, 240, 250, 300]:
        filler = [2, 3, 4, 5, 6, 7]
        c = sorted({1, 11, 20, p10} | set(filler))
        if len(c) == n_runners:
            configs.append(c)

    # Family 3: runner 20 + runner 30 (cascading)
    for p10 in [330, 400, 500]:
        c = sorted({1, 11, 20, 30, p10, 2, 3, 4, 5})
        if len(c) == n_runners:
            configs.append(c)

    # Family 4: runner 100 (m=10, most dangerous), p_10 >= 1100
    for p10 in [1100, 1200, 1300]:
        c = sorted({1, 11, 100, p10, 2, 3, 4, 5, 6})
        if len(c) == n_runners:
            configs.append(c)

    # Family 5: the specific test case from the proof
    configs.append([1, 2, 3, 4, 5, 6, 11, 20, 220, 300])

    return configs


# ---------- Main investigation ----------

def run_investigation(configs, label=""):
    """Run ILE on all configs and summarize findings."""
    total = 0
    witnesses = 0
    violations = 0
    am_total = 0
    dangerous_total = 0
    am_by_m = defaultdict(int)
    dangerous_by_m = defaultdict(int)
    example_dangerous = {}  # m -> first dangerous example

    for config in configs:
        total += 1
        result = ile_trace(config)

        if result['witness'] is not None:
            witnesses += 1
        if result['containment_violation'] is not None:
            violations += 1
            print(f"  *** CONTAINMENT VIOLATION: config={config}")
            print(f"      at t={result['containment_violation'][0]}, "
                  f"runner={result['containment_violation'][1]}, "
                  f"tau={result['containment_violation'][2]}")

        for s in result['am_states']:
            am_total += 1
            am_by_m[s['m']] += 1

        for s in result['dangerous_states']:
            dangerous_total += 1
            dangerous_by_m[s['m']] += 1
            m = s['m']
            if m not in example_dangerous:
                example_dangerous[m] = (config, s)

    print(f"\n{'='*60}")
    print(f"Investigation: {label}")
    print(f"{'='*60}")
    print(f"Configs tested:      {total}")
    print(f"Witnesses found:     {witnesses}  ({100*witnesses/total:.1f}%)")
    print(f"Containment viol.:   {violations}")
    print(f"A_m states total:    {am_total}")
    print(f"DANGEROUS states:    {dangerous_total}  (A_m with only right-blocking mult-10)")
    print()
    print("A_m states by m:")
    for m in sorted(am_by_m):
        d = dangerous_by_m.get(m, 0)
        print(f"  m={m}: {am_by_m[m]} total, {d} dangerous")

    if example_dangerous:
        print("\nExample dangerous states (first per m):")
        for m, (config, state) in sorted(example_dangerous.items()):
            print(f"\n  m={m}: config={config}")
            t = state['t']
            print(f"    t = {t} ≈ {float(t):.6f}")
            print(f"    A_{m} = ({float(Fraction(99*m-1,110*m)):.6f}, {float(Fraction(9,10)):.6f})")
            print(f"    right_mult10 (dangerous): {[(p, float(tau)) for p,tau in state['right_mult10']]}")
            print(f"    left_non_mult10 (safe):   {[(p, float(tau)) for p,tau in state['left_non_mult10']]}")
            print(f"    all right_blockers:       {[(p, float(tau)) for p,tau in state['right_blockers']]}")
            print(f"    all left_blockers:        {[(p, float(tau)) for p,tau in state['left_blockers']]}")
            print(f"    min_tau = {state['min_tau']} ≈ {float(state['min_tau']):.6f}")
            print(f"    tau_in_D11 = {state['tau_in_D11']}")
            print(f"    D11_left = {float(Fraction(109,121)):.6f}")

    return {
        'violations': violations,
        'dangerous_total': dangerous_total,
        'example_dangerous': example_dangerous,
    }


def detailed_am_analysis(config, verbose=True):
    """Deep analysis: for a single config, show full A_m event log."""
    result = ile_trace(config)
    print(f"\nConfig: {config}")
    print(f"Witness: {result['witness']} ≈ {float(result['witness']):.6f}"
          if result['witness'] else f"No witness (violation={result['containment_violation']})")
    print(f"Total ILE steps: {result['total_steps']}")
    print(f"A_m states: {len(result['am_states'])}")
    print(f"Dangerous states: {len(result['dangerous_states'])}")

    if verbose and result['am_states']:
        print("\nA_m state log:")
        for i, s in enumerate(result['am_states']):
            t = s['t']
            m = s['m']
            flag = " *** DANGEROUS" if s['is_dangerous'] else ""
            print(f"  [{i}] m={m}, t={float(t):.7f}, "
                  f"left_non10={len(s['left_non_mult10'])}, right_10={len(s['right_mult10'])}"
                  f"{flag}")
            if s['is_dangerous']:
                print(f"       right_mult10={[(p, f'{float(tau):.6f}') for p,tau in s['right_mult10']]}")
                print(f"       left_blockers={[(p, f'{float(tau):.6f}') for p,tau in s['left_blockers']]}")


# =====================================================================
# SYSTEMATIC INVESTIGATION
# =====================================================================

print("=" * 70)
print("ILE A_m TRACER — Containment Residual Investigation")
print("=" * 70)

# --- Test 1: The specific proof example ---
print("\n[1] Specific proof example: {1,2,3,4,5,6,11,20,220,300}")
detailed_am_analysis([1, 2, 3, 4, 5, 6, 11, 20, 220, 300])

# --- Test 2: Adversarial configs ---
print("\n[2] Adversarial configs (designed to trigger dangerous states)...")
adv = adversarial_configs(10)
r2 = run_investigation(adv, "Adversarial configs (n_runners=10)")

# --- Test 3: Random configs with p_j=11, runner 20, p_10 in [220,500] ---
print("\n[3] Random configs: p_j=11, runner 20, p_10 in [220,500]...")
rnd1 = configs_with_pj11_and_mult10(
    n_runners=10, p10_min=220, p10_max=500,
    dangerous_m_range=(2, 3),  # runner 20 only
    n_configs=500, seed=1
)
r3 = run_investigation(rnd1, "Random: p_j=11, runner 20, p_10 in [220,500]")

# --- Test 4: Random configs with runner 20, p_10 in [220,2000] ---
print("\n[4] Random configs: p_j=11, runner 20 or 30, p_10 in [220,2000]...")
rnd2 = configs_with_pj11_and_mult10(
    n_runners=10, p10_min=220, p10_max=2000,
    dangerous_m_range=(2, 5),
    n_configs=500, seed=2
)
r4 = run_investigation(rnd2, "Random: p_j=11, runner 20 or 30, p_10 in [220,2000]")

# --- Test 5: Focus on largest m (runner 100, p_10 in [1100, 3000]) ---
print("\n[5] Focus m=10 (runner 100), p_10 in [1100,3000]...")
rnd3 = configs_with_pj11_and_mult10(
    n_runners=10, p10_min=1100, p10_max=3000,
    dangerous_m_range=(10, 11),
    n_configs=200, seed=3
)
r5 = run_investigation(rnd3, "Random: runner 100, p_10 in [1100,3000]")

# --- Test 6: Very sparse configs (few runners) to maximize dangerous chance ---
print("\n[6] Sparse configs (force: only {1,11,20,p10} + minimal filler)...")
sparse = []
for p10 in range(221, 700, 7):
    # Minimal filler to reach 10 runners
    filler = list(range(2, 2 + 6))  # {2,3,4,5,6,7}
    c = sorted({1, 11, 20, p10} | set(filler))
    if len(c) == 10:
        sparse.append(c)
r6 = run_investigation(sparse, "Sparse configs: {1,2,3,4,5,6,7,11,20,p10} for p10 in [221,700]")

# --- Test 7: Check if any dangerous state has tau > D11_left (actual violation) ---
print("\n[7] Checking tau_in_D11 across all dangerous states found...")
all_dangerous = []
for r in [r2, r3, r4, r5, r6]:
    for m, (config, state) in r.get('example_dangerous', {}).items():
        all_dangerous.append((m, config, state))

if all_dangerous:
    print(f"Found {len(all_dangerous)} dangerous states across investigations.")
    print("Checking if any have min_tau > D11_left:")
    D11_left = Fraction(109, 121)
    actual_violations = [(m, c, s) for m, c, s in all_dangerous if s['min_tau'] > D11_left]
    if actual_violations:
        print(f"  *** {len(actual_violations)} ACTUAL tau > D11_left found! ***")
        for m, c, s in actual_violations:
            print(f"    m={m}, config={c}, t={s['t']}, min_tau={s['min_tau']}")
    else:
        print("  None — all dangerous states have min_tau <= D11_left despite no left-blocker.")
        print("  (This would mean the ILE somehow avoids the actual advance into D11.)")
else:
    print("No dangerous states found in any investigation.")

# --- Test 8: If dangerous states exist, trace what happens next ---
if all_dangerous:
    print("\n[8] What happens AFTER a dangerous state? (full trace detail)")
    for m, config, state in all_dangerous[:3]:  # first 3 examples
        t_danger = state['t']
        # Trace the ILE and find this state, then show next 5 steps
        result = ile_trace(config)
        steps = result['steps']
        for i, step in enumerate(steps):
            if step['t'] == t_danger:
                print(f"\n  Config: {config}")
                print(f"  Dangerous state at step {i}: t={float(t_danger):.7f}")
                print(f"  Next steps:")
                for j in range(i, min(i+5, len(steps))):
                    s = steps[j]
                    bl = {p: (btype, float(tau)) for p,(btype,tau) in s['blocking'].items()}
                    print(f"    step {j}: t={float(s['t']):.7f}, min_tau={float(s['min_tau']):.7f}")
                    print(f"           blocking: {bl}")
                break
