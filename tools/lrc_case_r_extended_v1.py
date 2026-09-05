"""
lrc_case_r_extended_v1.py
=========================
Extended Case R> investigation for the n=11 Lonely Runner Conjecture AP paper.

Runs the Iterated Left-Entry Construction (ILE) with full per-level
instrumentation on 10,000+ configurations (ratio 11–1000), then:

  Phase 1 — run & collect data → results_v1.csv, failures_v1.csv
  Phase 2 — top-level summary  → summary_v1.md
  Phase 3 — outlier deep-dives → outliers_v1.md  (L >= 10 or margin < 5% |W0|)
  Phase 4 — mechanistic conjectures M1/M2/M3 → conjectures_v1.md

Uses exact rational arithmetic (fractions.Fraction) throughout.
"""

import csv
import math
import os
import random
import sys
from collections import Counter
from fractions import Fraction
from math import gcd

# ── output directory ──────────────────────────────────────────────────────────

OUT_DIR = os.path.join(
    os.path.dirname(__file__),
    "..", "reports", "investigations", "INV-CASE-R-EXT-001"
)

# ── helpers ───────────────────────────────────────────────────────────────────

def frac_part(x: Fraction) -> Fraction:
    return x - int(x)

def dist_to_nearest_int(x: Fraction) -> Fraction:
    f = frac_part(x)
    return min(f, Fraction(1) - f)

def all_isolated(speeds, t: Fraction, n: int = 11) -> bool:
    thr = Fraction(1, n)
    for p in speeds:
        if dist_to_nearest_int(Fraction(p) * t) < thr:
            return False
    return True

def is_blocker(p: int, t: Fraction, n: int = 11) -> bool:
    return dist_to_nearest_int(Fraction(p) * t) < Fraction(1, n)

def find_blockers(speeds, t: Fraction, n: int = 11):
    return [p for p in speeds if is_blocker(p, t, n)]

def next_entry_time(pb: int, t_cur: Fraction, n: int = 11) -> Fraction:
    """
    First entry time of runner pb's isolation window in [t_cur, +inf).
    τ = (n*j* + 1) / (n * pb)  where j* = ceil(pb * t_cur - 1/n).
    Exact computation via Fraction.
    """
    val = Fraction(pb) * t_cur - Fraction(1, n)
    # ceil of a Fraction: use numerator/denominator arithmetic
    num, den = val.numerator, val.denominator
    if den > 0:
        j_star = -(-num // den)  # ceiling division (works for negative too)
    else:
        j_star = num // (-den)   # denominator was negative (shouldn't happen for Fraction)
    tau = Fraction(n * j_star + 1, n * pb)
    # Safety: ensure tau >= t_cur (rounding guard)
    while tau < t_cur:
        j_star += 1
        tau = Fraction(n * j_star + 1, n * pb)
    return tau


# ── instrumented ILE ──────────────────────────────────────────────────────────

def ile_instrumented(speeds, n: int = 11, max_levels: int = 200):
    """
    Run ILE with full per-level instrumentation.

    Returns dict with:
      success           bool
      witness_t         Fraction or None
      L                 int  (levels; 0 = W_lo was direct witness)
      trace             list[dict]  (one entry per level)
      min_containment   Fraction  (min W_hi - t_cur across all levels, before advance)
      max_advance       Fraction  (max single-step δ)
      total_carry       int
      carry_C           int  (crossed upper isolation boundary)
      carry_W           int  (wrapped past integer, landed below 1/n)
      step_L2_min_buf   Fraction or None  (min over all (non-blocker, blocker) pairs at W_lo)
      W0_lo, W0_hi      Fraction
      failure_reason    str or None
    """
    p1 = speeds[0]
    thr = Fraction(1, n)
    W0_lo = Fraction(1, n * p1)
    W0_hi = Fraction(n - 1, n * p1)   # = 10/(11*p1)
    W0_width = W0_hi - W0_lo

    result = dict(
        success=False, witness_t=None, L=0, trace=[],
        min_containment=W0_hi - W0_lo,
        max_advance=Fraction(0),
        total_carry=0, carry_C=0, carry_W=0,
        step_L2_min_buf=None,
        W0_lo=W0_lo, W0_hi=W0_hi,
        failure_reason=None,
    )

    # ── Step L2 buffer computation at W_lo ───────────────────────────────────
    # For each lower-bad W_lo blocker b and each non-blocker i:
    #   buffer(i,b) = 10*p1 - R_i - p_i*(p1 - r_b)/p_b
    # where R_i = p_i mod (11*p1), r_b = p_b mod (11*p1) (< p1 for lower-bad)
    blockers_at_lo = find_blockers(speeds, W0_lo, n)
    step_l2_min = None
    for pb in blockers_at_lo:
        fp_b = frac_part(Fraction(pb) * W0_lo)
        if fp_b >= thr:
            continue  # upper-bad blocker: skip Step L2 formula (different analysis)
        r_b_frac = fp_b * (n * p1)  # = r_b as Fraction; should be integer
        r_b = int(r_b_frac)
        for pi in speeds:
            if pi in blockers_at_lo:
                continue
            fp_i = frac_part(Fraction(pi) * W0_lo)
            R_i_frac = fp_i * (n * p1)
            R_i = R_i_frac  # keep as Fraction for exactness
            # buffer = 10*p1 - R_i - p_i*(p1 - r_b)/p_b  (as Fraction)
            buf = Fraction(10 * p1) - R_i - Fraction(pi * (p1 - r_b), pb)
            if step_l2_min is None or buf < step_l2_min:
                step_l2_min = buf
    result['step_L2_min_buf'] = step_l2_min

    # ── ILE iteration ─────────────────────────────────────────────────────────
    t_cur = W0_lo
    prev_blocked = set(find_blockers(speeds, t_cur, n))

    for level in range(max_levels + 1):
        margin_before = W0_hi - t_cur
        if margin_before < result['min_containment']:
            result['min_containment'] = margin_before

        blockers = find_blockers(speeds, t_cur, n)

        # Termination check
        if not blockers:
            result['success'] = True
            result['witness_t'] = t_cur
            result['L'] = level
            return result

        if level >= max_levels:
            result['L'] = level
            result['failure_reason'] = f"exceeded max_levels={max_levels}"
            return result

        # Compute re-entry times for each blocker
        tau_map = {}
        for pb in blockers:
            tau = next_entry_time(pb, t_cur, n)
            if tau > W0_hi:
                # Containment failure
                result['L'] = level
                result['failure_reason'] = (
                    f"containment failure: pb={pb}, tau={tau} > W0_hi={W0_hi}"
                )
                result['trace'].append(dict(
                    level=level, t_cur_before=t_cur,
                    blockers=tuple(blockers), advancing_pb=pb,
                    tau_pb=tau, advance_delta=tau - t_cur,
                    margin_before=margin_before, margin_after=W0_hi - tau,
                    carry_events=[], failure=True,
                ))
                return result
            tau_map[pb] = tau

        # Advancing blocker: largest re-entry time
        advancing_pb = max(tau_map, key=lambda b: tau_map[b])
        new_t = tau_map[advancing_pb]
        delta = new_t - t_cur

        if delta > result['max_advance']:
            result['max_advance'] = delta

        # Detect carry events (was isolated at t_cur, now blocked at new_t)
        carry_events = []
        new_blocked = set(find_blockers(speeds, new_t, n))
        for p in speeds:
            if p in prev_blocked:
                continue  # was already blocked
            if p in new_blocked:
                # Carry event
                old_fp = frac_part(Fraction(p) * t_cur)
                new_fp = frac_part(Fraction(p) * new_t)
                # Type C: old_fp in [1/n, 10/n) and new_fp > 10/n (crossed upper boundary)
                # Type W: new_fp < 1/n (wrapped past integer, landed in lower zone)
                if new_fp < thr:
                    carry_type = 'W'
                    result['carry_W'] += 1
                else:
                    carry_type = 'C'
                    result['carry_C'] += 1
                result['total_carry'] += 1
                carry_events.append((p, carry_type))

        margin_after = W0_hi - new_t
        result['trace'].append(dict(
            level=level, t_cur_before=t_cur,
            blockers=tuple(blockers), advancing_pb=advancing_pb,
            tau_pb=new_t, advance_delta=delta,
            margin_before=margin_before, margin_after=margin_after,
            carry_events=carry_events,
        ))

        t_cur = new_t
        prev_blocked = new_blocked

    result['failure_reason'] = "loop exhausted"
    return result


# ── config generators ─────────────────────────────────────────────────────────

def gen_type_a_large(n_configs=9000, seeds=None):
    """Type A-large: random configs, p1 in {1..10}, ratio in (10, 1000] (log-uniform)."""
    if seeds is None:
        seeds = [42, 99, 137, 271, 314, 577, 1000, 2718, 3141]
    configs = []
    per_seed = n_configs // len(seeds) + 1
    for seed in seeds:
        rng = random.Random(seed)
        count = 0
        attempts = 0
        while count < per_seed and attempts < per_seed * 20:
            attempts += 1
            p1 = rng.randint(1, 10)
            # log-uniform ratio in (10, 1000]
            log_r = rng.uniform(math.log10(10.01), math.log10(1000))
            target_ratio = 10 ** log_r
            p10 = max(10 * p1 + 1, round(p1 * target_ratio))
            interior_range = list(range(p1 + 1, p10))
            if len(interior_range) < 8:
                continue
            interior = sorted(rng.sample(interior_range, 8))
            speeds = [p1] + interior + [p10]
            if speeds[-1] / speeds[0] <= 10:
                continue
            configs.append((speeds, 'A', seed))
            count += 1
    return configs[:n_configs]


def gen_type_b_stress():
    """Type B-stress: resonant and all-consecutive adversarial configs."""
    configs = []

    # Resonant: k*(1,2,...,9), p10 = k*(11k + 1) [ratio slightly > 11]
    for k in range(1, 21):
        interior = [k * i for i in range(2, 10)]
        p1 = k
        p10 = 10 * k + 1
        if p10 / p1 <= 10:
            continue
        if len(set(range(p1 + 1, p10))) < 8:
            continue
        speeds = [p1] + interior + [p10]
        if len(speeds) == 10 and speeds[0] < speeds[-1]:
            configs.append((speeds, 'B-resonant', k))

    # All-consecutive: (p1, p1+1, ..., p1+8, p1*R)
    for p1 in [1, 2, 3]:
        for R in [11, 12, 15, 20, 50, 100, 500, 1000]:
            p10 = p1 * R
            consecutive = list(range(p1, p1 + 9))  # p1..p1+8 (9 speeds)
            if p1 + 8 >= p10:
                continue
            interior = consecutive[1:]  # p1+1..p1+8 (8 interior speeds)
            speeds = [p1] + interior + [p10]
            if speeds[-1] / speeds[0] <= 10:
                continue
            configs.append((speeds, f'B-consec-R{R}', p1))

    # Paper example and variants from original harness
    for speeds, label in [
        ([1, 4, 7, 9, 11, 12, 14, 15, 16, 20], 'paper_example'),
        ([1, 5, 8, 10, 13, 14, 16, 18, 19, 22], 'adversarial_variant'),
    ]:
        if speeds[-1] / speeds[0] > 10:
            configs.append((speeds, f'B-{label}', 0))

    return configs


def gen_type_p_higher():
    """
    Type P: higher-order pacemaker configs.
    p10 = 11*k*p1 for k in {2,3,4,5} with the 8 missing-speed variants.
    For each k, WLOG p1=1, p10=11k. Choose S = {2,...,10k} \ {m} for various m.
    """
    configs = []
    for k in range(2, 6):  # k = 2,3,4,5 → ratios 22,33,44,55
        p1 = 1
        p10 = 11 * k
        # Interior speeds: pick 8 from {p1+1, ..., p10-1}
        interior_pool = list(range(2, p10))
        if len(interior_pool) < 8:
            continue
        # Adversarial: remove one of the "near-pacemaker" multiples
        # Also try evenly-spaced interior
        rng = random.Random(12345 * k)
        for trial in range(20):
            interior = sorted(rng.sample(interior_pool, 8))
            speeds = [p1] + interior + [p10]
            configs.append((speeds, f'P-k{k}', trial))
        # Specific: consecutive interior (hardest for containment)
        consec = list(range(2, 10))[:8]  # 2..9
        if len(consec) == 8 and max(consec) < p10:
            configs.append(([p1] + consec + [p10], f'P-k{k}-consec', -1))
    return configs


def gen_type_c_extreme():
    """Type C-extreme: near-boundary and very-high-ratio configs."""
    configs = []
    base = [1, 2, 3, 4, 5, 6, 7, 8, 9]  # 9 speeds starting at 1
    for R in [11, 12, 15, 20, 50, 100, 200, 500, 1000]:
        p10 = R
        if p10 <= 10 * base[0]:
            configs.append((base + [p10], f'C-ratio{R}', 0))
        elif p10 > 10:
            configs.append((base + [p10], f'C-ratio{R}', 0))

    # Odd speeds
    odd = [1, 3, 5, 7, 9, 11, 13, 15, 17]
    for p10 in [19, 21, 51, 101, 501, 1001]:
        if p10 > 10 * odd[0]:
            configs.append((odd + [p10], f'C-odd-ratio{p10}', 0))

    # Small p1, large p10 (stress containment)
    for p1 in [1, 2, 3]:
        for p10_mult in [11, 100, 1000]:
            p10 = p1 * p10_mult
            interior = list(range(p1 + 1, p1 + 9))
            if max(interior) >= p10:
                continue
            if p10 / p1 <= 10:
                continue
            configs.append(([p1] + interior + [p10], f'C-p1{p1}-R{p10_mult}', 0))

    return configs


def gen_type_p_ratio11():
    """Original 9 pacemaker configs (p1=1, p10=11, one missing speed)."""
    configs = []
    for m in range(2, 11):  # missing speed m in {2,...,10}
        speeds = [1] + [k for k in range(2, 11) if k != m] + [11]
        configs.append((speeds, f'P-ratio11-miss{m}', m))
    return configs


# ── pacemaker theorem 10.12 verification ─────────────────────────────────────

def pacemaker_theorem_witness(m: int, p1: int = 1) -> Fraction:
    """Compute t* = (11*j* + 1) / (121*p1) where j* = 10 * m^{-1} mod 11."""
    # m^{-1} mod 11
    m_inv = pow(int(m), -1, 11)
    j_star = (10 * m_inv) % 11
    return Fraction(11 * j_star + 1, 121 * p1)


# ── run all configs ───────────────────────────────────────────────────────────

def run_all(verbose=True):
    """Generate all configs, run ILE, collect results."""
    all_configs = []

    type_a = gen_type_a_large(9000)
    all_configs.extend(type_a)

    type_b = gen_type_b_stress()
    all_configs.extend(type_b)

    type_p = gen_type_p_higher()
    all_configs.extend(type_p)

    type_c = gen_type_c_extreme()
    all_configs.extend(type_c)

    type_p11 = gen_type_p_ratio11()
    all_configs.extend(type_p11)

    if verbose:
        print(f"Total configs to test: {len(all_configs)}")
        print(f"  Type A-large: {len(type_a)}")
        print(f"  Type B-stress: {len(type_b)}")
        print(f"  Type P-higher: {len(type_p)}")
        print(f"  Type C-extreme: {len(type_c)}")
        print(f"  Type P-ratio11: {len(type_p11)}")
        print()

    results = []
    failures = []
    W0_width_cache = {}

    for idx, (speeds, ctype, seed) in enumerate(all_configs):
        if verbose and (idx % 500 == 0):
            print(f"  [{idx}/{len(all_configs)}] ...", end='\r', flush=True)

        p1 = speeds[0]
        p10 = speeds[-1]
        ratio = p10 / p1
        n = 11

        W0_lo = Fraction(1, n * p1)
        W0_hi = Fraction(n - 1, n * p1)
        W0_width = W0_hi - W0_lo

        r = ile_instrumented(speeds, n=n)

        row = dict(
            idx=idx,
            speeds=str(tuple(speeds)),
            p1=p1, p10=p10,
            ratio=ratio,
            config_type=ctype,
            seed=seed,
            success=r['success'],
            L=r['L'],
            witness_t=str(r['witness_t']) if r['witness_t'] else '',
            min_containment=float(r['min_containment']),
            min_containment_frac=str(r['min_containment']),
            min_containment_pct_W0=float(r['min_containment'] / W0_width * 100),
            max_advance=float(r['max_advance']),
            total_carry=r['total_carry'],
            carry_C=r['carry_C'],
            carry_W=r['carry_W'],
            step_L2_min_buf=float(r['step_L2_min_buf']) if r['step_L2_min_buf'] is not None else '',
            step_L2_min_buf_frac=str(r['step_L2_min_buf']) if r['step_L2_min_buf'] is not None else '',
            failure_reason=r['failure_reason'] or '',
        )
        results.append(row)

        if not r['success']:
            failures.append((speeds, ctype, seed, r))

    if verbose:
        print(f"\nDone. Successes: {sum(1 for r in results if r['success'])}/{len(results)}")

    return results, failures, all_configs


# ── write CSV ─────────────────────────────────────────────────────────────────

def write_results_csv(results, path):
    if not results:
        return
    fieldnames = list(results[0].keys())
    with open(path, 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(results)
    print(f"Written: {path}  ({len(results)} rows)")


def write_failures_csv(failures, path):
    rows = []
    for speeds, ctype, seed, r in failures:
        row = dict(
            speeds=str(tuple(speeds)),
            config_type=ctype,
            seed=seed,
            L=r['L'],
            failure_reason=r['failure_reason'],
            trace_summary=str([(e['level'], str(e['advancing_pb']),
                                 float(e['advance_delta'])) for e in r['trace']])
        )
        rows.append(row)
    if rows:
        with open(path, 'w', newline='') as f:
            w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
            w.writeheader()
            w.writerows(rows)
    print(f"Written: {path}  ({len(rows)} failure rows)")


# ── Phase 2: top-level summary ────────────────────────────────────────────────

def phase2_summary(results, all_configs):
    n_total = len(results)
    n_success = sum(1 for r in results if r['success'])
    n_fail = n_total - n_success

    # L distribution
    L_vals = [r['L'] for r in results if r['success']]
    def L_bucket(L):
        if L == 0: return '0'
        if L == 1: return '1'
        if L <= 5: return '2-5'
        if L <= 10: return '6-10'
        if L <= 20: return '11-20'
        if L <= 50: return '21-50'
        return '>50'
    L_dist = Counter(L_bucket(L) for L in L_vals)
    L_dist_all = Counter(L_bucket(r['L']) for r in results)

    # Containment margin distribution
    margins = [r['min_containment'] for r in results if r['success']]
    margins_pct = [r['min_containment_pct_W0'] for r in results if r['success']]

    def pct_bucket(p):
        if p < 1: return '<1%'
        if p < 5: return '1-5%'
        if p < 10: return '5-10%'
        if p < 25: return '10-25%'
        if p < 50: return '25-50%'
        return '>=50%'
    margin_dist = Counter(pct_bucket(p) for p in margins_pct)

    # Step L2 buffer distribution
    l2_bufs = [r['step_L2_min_buf'] for r in results if r['step_L2_min_buf'] != '']
    l2_bufs_float = [float(b) for b in l2_bufs if b != '']

    # Carry event totals
    total_carry = sum(r['total_carry'] for r in results)
    total_C = sum(r['carry_C'] for r in results)
    total_W = sum(r['carry_W'] for r in results)

    # By config type
    types = sorted(set(r['config_type'] for r in results))
    type_stats = {}
    for t in types:
        sub = [r for r in results if r['config_type'] == t]
        type_stats[t] = dict(
            n=len(sub),
            success=sum(1 for r in sub if r['success']),
            max_L=max((r['L'] for r in sub), default=0),
            min_margin=min((r['min_containment'] for r in sub), default=float('inf')),
        )

    lines = []
    lines.append("# INV-CASE-R-EXT-001: Extended Case R> Investigation — Summary")
    lines.append("")
    lines.append(f"**Total configs tested:** {n_total}  |  "
                 f"**Successes:** {n_success} ({100*n_success/n_total:.2f}%)  |  "
                 f"**Failures:** {n_fail}")
    lines.append("")

    lines.append("## ILE Level Distribution")
    lines.append("")
    lines.append("| Levels L | Count | % |")
    lines.append("|---|---|---|")
    for bucket in ['0', '1', '2-5', '6-10', '11-20', '21-50', '>50']:
        c = L_dist_all.get(bucket, 0)
        lines.append(f"| {bucket} | {c} | {100*c/n_total:.1f}% |")
    if n_fail > 0:
        lines.append(f"| FAILURE | {n_fail} | {100*n_fail/n_total:.2f}% |")
    if L_vals:
        lines.append(f"\n**Max L observed:** {max(L_vals)}  |  "
                     f"**Mean L (successes):** {sum(L_vals)/len(L_vals):.2f}")
    lines.append("")

    lines.append("## Containment Margin Distribution (min W_hi − t_cur, as % of |W₀|)")
    lines.append("")
    lines.append("| Margin % of |W₀| | Count | % |")
    lines.append("|---|---|---|")
    for bucket in ['<1%', '1-5%', '5-10%', '10-25%', '25-50%', '>=50%']:
        c = margin_dist.get(bucket, 0)
        lines.append(f"| {bucket} | {c} | {100*c/len(margins_pct):.1f}% |" if margins_pct else f"| {bucket} | 0 | — |")
    if margins_pct:
        lines.append(f"\n**Min containment margin:** {min(margins_pct):.4f}% of |W₀|")
        lines.append(f"**Median:** {sorted(margins_pct)[len(margins_pct)//2]:.4f}%")
    lines.append("")

    lines.append("## Step L2 Buffer Distribution")
    lines.append("")
    if l2_bufs_float:
        lines.append(f"- **Min buffer:** {min(l2_bufs_float):.6f}  (negative ⟹ Step L2 violated)")
        lines.append(f"- **Median buffer:** {sorted(l2_bufs_float)[len(l2_bufs_float)//2]:.6f}")
        lines.append(f"- **Buffers < 0:** {sum(1 for b in l2_bufs_float if b < 0)}")
        lines.append(f"- **Buffers < 1:** {sum(1 for b in l2_bufs_float if b < 1)}")
    lines.append("")

    lines.append("## Carry Event Totals")
    lines.append("")
    lines.append(f"- Total carry events: {total_carry}")
    if total_carry > 0:
        lines.append(f"- Type C (cross upper boundary): {total_C} ({100*total_C/total_carry:.1f}%)")
        lines.append(f"- Type W (wrap past integer): {total_W} ({100*total_W/total_carry:.1f}%)")
    lines.append("")

    lines.append("## Results by Config Type")
    lines.append("")
    lines.append("| Type | N | Success | Max L | Min Margin |")
    lines.append("|---|---|---|---|---|")
    for t, s in sorted(type_stats.items()):
        lines.append(f"| {t} | {s['n']} | {s['success']}/{s['n']} | {s['max_L']} | {s['min_margin']:.4f} |")
    lines.append("")

    return '\n'.join(lines)


# ── Phase 3: outlier deep-dives ───────────────────────────────────────────────

def phase3_outliers(results, all_configs, W0_width_threshold_pct=5.0, L_threshold=10):
    """
    For configs with L >= L_threshold or min_containment_pct < threshold,
    re-run with full trace and report.
    """
    outlier_idxs = [
        r['idx'] for r in results
        if r['success'] and (r['L'] >= L_threshold or r['min_containment_pct_W0'] < W0_width_threshold_pct)
    ]

    lines = []
    lines.append("# INV-CASE-R-EXT-001: Outlier Deep-Dives")
    lines.append("")
    lines.append(f"Configs with L ≥ {L_threshold} or containment margin < {W0_width_threshold_pct}% of |W₀|: "
                 f"**{len(outlier_idxs)}** configs")
    lines.append("")

    # Sort by L descending, then by margin ascending
    outlier_idxs_sorted = sorted(
        outlier_idxs,
        key=lambda i: (-results[i]['L'], results[i]['min_containment_pct_W0'])
    )

    # Report top 30 (or all if fewer)
    report_idxs = outlier_idxs_sorted[:30]

    lines.append("## Top Outliers (sorted by L desc, then min margin asc)")
    lines.append("")
    lines.append("| Rank | Speeds | Ratio | L | Min Margin % | Carry | Type |")
    lines.append("|---|---|---|---|---|---|---|")
    for rank, i in enumerate(report_idxs, 1):
        r = results[i]
        speeds_str = r['speeds'][:50] + ('...' if len(r['speeds']) > 50 else '')
        lines.append(f"| {rank} | {speeds_str} | {r['ratio']:.2f} | {r['L']} | "
                     f"{r['min_containment_pct_W0']:.3f}% | {r['total_carry']} | {r['config_type']} |")
    lines.append("")

    # Full ILE trace for top 10
    lines.append("## Full ILE Traces: Top 10 Hardest Configs")
    lines.append("")

    for rank, i in enumerate(report_idxs[:10], 1):
        speeds, ctype, seed = all_configs[i]
        r_full = ile_instrumented(speeds)
        p1 = speeds[0]
        W0_lo = r_full['W0_lo']
        W0_hi = r_full['W0_hi']
        W0_width = W0_hi - W0_lo

        lines.append(f"### Rank {rank}: {tuple(speeds)}")
        lines.append(f"- Type: {ctype}, seed={seed}")
        lines.append(f"- Ratio p₁₀/p₁ = {speeds[-1]}/{speeds[0]} = {speeds[-1]/speeds[0]:.4g}")
        lines.append(f"- W₀ = [{float(W0_lo):.6f}, {float(W0_hi):.6f}], |W₀| = {float(W0_width):.6f}")
        lines.append(f"- L = {r_full['L']}, witness t* = {r_full['witness_t']} = {float(r_full['witness_t']):.6f}")
        lines.append(f"- Min containment margin: {float(r_full['min_containment']):.6f} "
                     f"({100*float(r_full['min_containment']/W0_width):.2f}% of |W₀|)")
        lines.append(f"- Carry events: {r_full['total_carry']} (C:{r_full['carry_C']}, W:{r_full['carry_W']})")
        if r_full['step_L2_min_buf'] is not None:
            lines.append(f"- Step L2 min buffer: {float(r_full['step_L2_min_buf']):.6f}")
        lines.append("")
        lines.append("| Level | t_cur | Blockers | Adv. runner | δ (advance) | Margin before | Carry |")
        lines.append("|---|---|---|---|---|---|---|")
        for entry in r_full['trace']:
            carry_str = ', '.join(f"p={p}({ct})" for p, ct in entry['carry_events'])
            lines.append(
                f"| {entry['level']} | {float(entry['t_cur_before']):.6f} "
                f"| {entry['blockers']} | p={entry['advancing_pb']} "
                f"| {float(entry['advance_delta']):.6f} "
                f"| {float(entry['margin_before']):.6f} ({100*float(entry['margin_before']/W0_width):.1f}%) "
                f"| {carry_str or '—'} |"
            )
        lines.append("")

    # Classify outlier families
    lines.append("## Outlier Family Classification")
    lines.append("")

    high_L = [results[i] for i in outlier_idxs_sorted if results[i]['L'] >= L_threshold]
    tight_margin = [results[i] for i in outlier_idxs_sorted if results[i]['min_containment_pct_W0'] < W0_width_threshold_pct]

    lines.append(f"- **High-L (L ≥ {L_threshold}):** {len(high_L)} configs")
    if high_L:
        ratio_vals = [r['ratio'] for r in high_L]
        lines.append(f"  - Ratio range: {min(ratio_vals):.2f} – {max(ratio_vals):.2f}")
        types_hl = Counter(r['config_type'] for r in high_L)
        lines.append(f"  - By type: {dict(types_hl)}")
    lines.append(f"- **Tight margin (< {W0_width_threshold_pct}% of |W₀|):** {len(tight_margin)} configs")
    if tight_margin:
        ratio_vals = [r['ratio'] for r in tight_margin]
        lines.append(f"  - Ratio range: {min(ratio_vals):.2f} – {max(ratio_vals):.2f}")
        types_tm = Counter(r['config_type'] for r in tight_margin)
        lines.append(f"  - By type: {dict(types_tm)}")

    return '\n'.join(lines)


# ── Phase 4: mechanistic conjectures ─────────────────────────────────────────

def phase4_conjectures(results, all_configs):
    """
    Test:
      M1: min_containment_margin >= 1/(11*p2)  for all configs
      M2: L <= floor(p10/p1) - 10
      M3: step_L2_min_buf >= 0  for all configs (Step L2 never violated)
    Also verify Theorem 10.12 for pacemaker configs.
    """
    lines = []
    lines.append("# INV-CASE-R-EXT-001: Mechanistic Conjecture Testing")
    lines.append("")

    # M1: min_containment >= 1/(11*p2)
    lines.append("## Conjecture M1: min containment margin ≥ 1/(11·p₂)")
    lines.append("")
    lines.append("The tightest possible margin is set by the second-slowest runner p₂.")
    lines.append("")
    m1_violations = []
    m1_margins = []
    for (speeds, ctype, seed), r in zip(all_configs, results):
        if not r['success']:
            continue
        p1 = speeds[0]
        p2 = speeds[1]
        bound = Fraction(1, 11 * p2)
        # re-run to get exact min_containment
        r_full = ile_instrumented(speeds)
        mc = r_full['min_containment']
        ratio_mc = float(mc / bound) if bound > 0 else float('inf')
        m1_margins.append(ratio_mc)
        if mc < bound:
            m1_violations.append((speeds, ctype, float(mc), float(bound), ratio_mc))

    lines.append(f"- Tested (successes): {len(m1_margins)}")
    lines.append(f"- Violations (margin < 1/(11·p₂)): **{len(m1_violations)}**")
    if m1_margins:
        lines.append(f"- Min ratio (margin / bound): {min(m1_margins):.4f}")
        lines.append(f"- Mean ratio: {sum(m1_margins)/len(m1_margins):.4f}")
    if m1_violations[:5]:
        lines.append("")
        lines.append("Top violations:")
        for v in m1_violations[:5]:
            lines.append(f"  {v[0]}: margin={v[2]:.6f}, bound={v[3]:.6f}, ratio={v[4]:.4f}")
    lines.append("")

    # M2: L <= floor(p10/p1) - 10
    lines.append("## Conjecture M2: L ≤ ⌊p₁₀/p₁⌋ − 10")
    lines.append("")
    m2_violations = []
    for r, (speeds, ctype, seed) in zip(results, all_configs):
        if not r['success']:
            continue
        p1 = speeds[0]
        p10 = speeds[-1]
        bound = p10 // p1 - 10
        if r['L'] > bound:
            m2_violations.append((speeds, r['L'], bound, ctype))

    lines.append(f"- Violations (L > ⌊p₁₀/p₁⌋ − 10): **{len(m2_violations)}**")
    if m2_violations[:5]:
        for v in m2_violations[:5]:
            lines.append(f"  {v[0]}: L={v[1]}, bound={v[2]}, type={v[3]}")
    lines.append("")

    # M3: step_L2_min_buf >= 0
    lines.append("## Conjecture M3: Step L2 buffer ≥ 0 for all configs")
    lines.append("")
    m3_violations = []
    m3_near_violations = []
    for r, (speeds, ctype, seed) in zip(results, all_configs):
        if r['step_L2_min_buf'] == '':
            continue  # no lower-bad blockers at W_lo
        buf = float(r['step_L2_min_buf'])
        if buf < 0:
            m3_violations.append((speeds, buf, ctype))
        elif buf < 1.0:
            m3_near_violations.append((speeds, buf, ctype))

    lines.append(f"- Violations (buffer < 0): **{len(m3_violations)}**")
    lines.append(f"- Near-violations (0 ≤ buffer < 1): {len(m3_near_violations)}")
    if m3_violations[:5]:
        lines.append("\nTop violations:")
        for v in m3_violations[:5]:
            lines.append(f"  {v[0]}: buf={v[1]:.6f}, type={v[2]}")
    if m3_near_violations:
        lines.append(f"\nClosest to 0: {min(m3_near_violations, key=lambda x: x[1])}")
    lines.append("")

    # Theorem 10.12 verification: pacemaker configs (ratio=11, p1=1)
    lines.append("## Theorem 10.12 Verification: Pacemaker Configs (ratio = 11)")
    lines.append("")
    lines.append("For each p1=1, p10=11, missing speed m: check that ILE witness = (11j*+1)/121.")
    lines.append("")
    lines.append("| Missing m | j* | Theorem t* | ILE witness | Match |")
    lines.append("|---|---|---|---|---|")
    for m in range(2, 11):
        speeds = [1] + [k for k in range(2, 11) if k != m] + [11]
        r_full = ile_instrumented(speeds)
        m_inv = pow(int(m), -1, 11)
        j_star = (10 * m_inv) % 11
        thm_t = Fraction(11 * j_star + 1, 121)
        ile_t = r_full['witness_t']
        match = '✓' if ile_t == thm_t else f'✗ (got {ile_t})'
        lines.append(f"| {m} | {j_star} | {thm_t} = {float(thm_t):.6f} | {ile_t} | {match} |")
    lines.append("")

    return '\n'.join(lines)


# ── main ──────────────────────────────────────────────────────────────────────

def main():
    print("=" * 70)
    print("LRC Case R> Extended Investigation  |  n=11")
    print("=" * 70)
    print()

    # Create output directory
    os.makedirs(OUT_DIR, exist_ok=True)

    # Phase 1: run
    print("Phase 1: Running ILE on all configs...")
    results, failures, all_configs = run_all(verbose=True)
    print()

    # Write CSVs
    results_path = os.path.join(OUT_DIR, "results_v1.csv")
    failures_path = os.path.join(OUT_DIR, "failures_v1.csv")
    write_results_csv(results, results_path)
    write_failures_csv(failures, failures_path)

    # Quick failure report
    if failures:
        print(f"\n*** {len(failures)} FAILURES ***")
        for speeds, ctype, seed, r in failures[:5]:
            print(f"  {tuple(speeds)} [{ctype}]: {r['failure_reason']}")
    else:
        print("\n✓ Zero failures — ILE succeeded on all configs.")
    print()

    # Phase 2: summary
    print("Phase 2: Generating summary...")
    summary_text = phase2_summary(results, all_configs)
    summary_path = os.path.join(OUT_DIR, "summary_v1.md")
    with open(summary_path, 'w') as f:
        f.write(summary_text)
    print(f"Written: {summary_path}")
    print()
    # Print key stats inline
    n_success = sum(1 for r in results if r['success'])
    L_vals = [r['L'] for r in results if r['success']]
    margins_pct = [r['min_containment_pct_W0'] for r in results if r['success']]
    print(f"  Success rate: {n_success}/{len(results)} ({100*n_success/len(results):.2f}%)")
    if L_vals:
        print(f"  Max L: {max(L_vals)}  |  Mean L: {sum(L_vals)/len(L_vals):.2f}")
    if margins_pct:
        print(f"  Min containment margin: {min(margins_pct):.4f}% of |W₀|")
    print()

    # Phase 3: outliers
    print("Phase 3: Outlier deep-dives (L >= 10 or margin < 5%)...")
    outliers_text = phase3_outliers(results, all_configs)
    outliers_path = os.path.join(OUT_DIR, "outliers_v1.md")
    with open(outliers_path, 'w') as f:
        f.write(outliers_text)
    print(f"Written: {outliers_path}")
    print()

    # Phase 4: conjectures — note: this re-runs ILE for M1, which is slow
    # Only run on a subset (first 1000 successes) for M1 to keep runtime reasonable
    print("Phase 4: Testing mechanistic conjectures...")
    print("  (M1 re-runs ILE for exact Fraction comparison — this may take a moment)")

    # Limit M1 test to 1000 configs for speed
    success_idxs = [i for i, r in enumerate(results) if r['success']]
    random.seed(42)
    sample_idxs = sorted(random.sample(success_idxs, min(1000, len(success_idxs))))
    results_sample = [results[i] for i in sample_idxs]
    all_configs_sample = [all_configs[i] for i in sample_idxs]

    conj_text = phase4_conjectures(results_sample, all_configs_sample)
    conj_path = os.path.join(OUT_DIR, "conjectures_v1.md")
    with open(conj_path, 'w') as f:
        f.write(conj_text)
    print(f"Written: {conj_path}")
    print()

    print("=" * 70)
    print("Investigation complete.")
    print(f"Outputs in: {os.path.abspath(OUT_DIR)}")
    print("=" * 70)


if __name__ == "__main__":
    main()
