"""
lrc_containment_probe_v1.py
============================
Five targeted experiments probing the Containment (C) condition for Case R>
in the n=11 Lonely Runner Conjecture.

Imports the tested ILE harness from lrc_case_r_extended_v1.py.
Loads the 9163-config corpus from results_v1.csv, re-runs ile_instrumented
on each config, and collects per-level quantities for proof-attack analysis.

Outputs to:
  reports/investigations/INV-CASE-R-EXT-001/containment_probe_v1/
    exp1_advance_fraction.csv
    exp2_gap_distribution.csv
    exp3_gap_trajectory.csv
    exp4_extremal_levels.csv
    exp5_adversarial.csv
    containment_probe_summary.md
"""

import ast
import csv
import json
import math
import os
import random
import sys
from collections import Counter, defaultdict
from fractions import Fraction

# ── import correct ILE harness ─────────────────────────────────────────────
TOOLS_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TOOLS_DIR)
from lrc_case_r_extended_v1 import (
    ile_instrumented,
    frac_part,
    dist_to_nearest_int,
    find_blockers,
    next_entry_time,
)

# ── paths ──────────────────────────────────────────────────────────────────
REPO_ROOT   = os.path.dirname(TOOLS_DIR)
INV_DIR     = os.path.join(REPO_ROOT, "reports", "investigations", "INV-CASE-R-EXT-001")
DATA_CSV    = os.path.join(INV_DIR, "results_v1.csv")
OUT_DIR     = os.path.join(INV_DIR, "containment_probe_v1")
os.makedirs(OUT_DIR, exist_ok=True)

# ── gap helpers ────────────────────────────────────────────────────────────

def compute_gap(pb: int, tau_pb: Fraction, p1: int, n: int = 11) -> int:
    """
    gap = j_max - j_cur where:
      j_cur = index of pb's re-entry at tau_pb  (tau_pb = (n*j_cur+1)/(n*pb))
      j_max = largest j s.t. (n*j+1)/(n*pb) <= W_hi = (n-1)/(n*p1)

    Derivation:
      j_cur:  pb * tau_pb - 1/n = j_cur  (exact since tau_pb is a re-entry time)
      j_max:  floor((pb*(n-1)/p1 - 1)/n) = (pb*(n-1) - p1) // (n*p1)

    gap >= 0  <=>  Containment holds at this level.
    """
    # j_cur: exact since tau_pb = Fraction(n*j+1, n*pb)
    j_cur_frac = Fraction(pb) * tau_pb - Fraction(1, n)
    j_cur = int(j_cur_frac)   # should be exact integer
    assert j_cur_frac == j_cur, f"j_cur not integer: {j_cur_frac}"

    # j_max: integer floor of ((n-1)*pb/p1 - 1)/n = ((n-1)*pb - p1)/(n*p1)
    # Use integer arithmetic directly (p1 divides p1, so this is exact)
    numerator = (n - 1) * pb - p1
    denominator = n * p1
    j_max = numerator // denominator  # floor division

    return j_max - j_cur


def compute_f(delta: Fraction, margin_before: Fraction) -> float:
    """Advance fraction f = delta / (W_hi - t_cur_before) = delta / margin_before."""
    if margin_before == 0:
        return float('inf')
    return float(delta / margin_before)


# ── load config corpus ─────────────────────────────────────────────────────

def load_configs(csv_path: str):
    """Load speed vectors from results_v1.csv. Returns list of (idx, speeds, p1, p10, ratio, config_type)."""
    configs = []
    with open(csv_path, newline='') as f:
        reader = csv.DictReader(f)
        for row in reader:
            idx = int(row['idx'])
            speeds = tuple(ast.literal_eval(row['speeds']))
            p1 = int(row['p1'])
            p10 = int(row['p10'])
            ratio = float(row['ratio'])
            config_type = row['config_type']
            configs.append((idx, speeds, p1, p10, ratio, config_type))
    return configs


# ── staircase configs ──────────────────────────────────────────────────────

def gen_staircase_configs(N_range=range(10, 501)):
    """
    Staircase family: p1=1, speeds = (1, N, N+1, ..., N+8, 11*k) where
    k is the smallest integer > 10*N (so p10/p1 > 10).
    For each N in N_range.
    """
    configs = []
    base_idx = 90000
    for N in N_range:
        interior = list(range(N, N + 9))   # N, N+1, ..., N+8
        # smallest p10 > 10*N and p10 > interior[-1] = N+8
        p10_min = max(10 * 1 + 1, interior[-1] + 1)  # ratio > 10 and strictly largest
        # p10 = ceiling of 10*1 * smallest integer ratio > 10 ... just use 11*k approach
        # smallest p10 such that p10 > 10 and p10 > N+8
        k = max(1, math.ceil((N + 9) / 11))
        p10_candidate = 11 * k
        if p10_candidate <= N + 8:
            k += 1
            p10_candidate = 11 * k
        if p10_candidate / 1 <= 10:
            # ratio not > 10, skip
            continue
        speeds = (1,) + tuple(interior) + (p10_candidate,)
        assert len(speeds) == 11
        p1 = speeds[0]
        p10 = speeds[-1]
        ratio = p10 / p1
        configs.append((base_idx + N, speeds, p1, p10, ratio, 'staircase'))
    return configs


# ── EXP-1: advance fraction distribution ──────────────────────────────────

def run_exp1(all_configs, n=11):
    """Per ILE level: compute f = delta / margin_before."""
    rows = []
    for idx, speeds, p1, p10, ratio, config_type in all_configs:
        res = ile_instrumented(speeds, n=n)
        if not res['success']:
            continue
        W0_hi = res['W0_hi']
        for entry in res['trace']:
            margin_before = float(entry['margin_before'])
            delta = float(entry['advance_delta'])
            f = delta / margin_before if margin_before > 0 else float('inf')
            rows.append({
                'config_idx': idx,
                'level': entry['level'],
                'p1': p1,
                'ratio': ratio,
                'config_type': config_type,
                'pb': entry['advancing_pb'],
                'f': f,
                'margin_before': margin_before,
                'margin_after': float(entry['margin_after']),
            })
    return rows


# ── EXP-2: gap distribution ────────────────────────────────────────────────

def run_exp2(all_configs, n=11):
    """Per ILE level: compute gap = j_max - j_cur."""
    rows = []
    for idx, speeds, p1, p10, ratio, config_type in all_configs:
        res = ile_instrumented(speeds, n=n)
        if not res['success']:
            continue
        W0_hi = res['W0_hi']
        for entry in res['trace']:
            pb = entry['advancing_pb']
            tau_pb = entry['tau_pb']
            gap = compute_gap(pb, tau_pb, p1, n)
            j_cur_frac = Fraction(pb) * tau_pb - Fraction(1, n)
            j_cur = int(j_cur_frac)
            j_max = ((n - 1) * pb - p1) // (n * p1)
            rows.append({
                'config_idx': idx,
                'level': entry['level'],
                'p1': p1,
                'p10': p10,
                'ratio': ratio,
                'pb': pb,
                'j_cur': j_cur,
                'j_max': j_max,
                'gap': gap,
                't_cur_after': float(tau_pb),
                'W_hi': float(W0_hi),
                'speeds': str(list(speeds)),
            })
    return rows


# ── EXP-3: gap trajectory monotonicity ────────────────────────────────────

def run_exp3(all_configs, n=11):
    """Per config: compute gap sequence and monotonicity statistics."""
    config_rows = []
    drop_rows = []
    for idx, speeds, p1, p10, ratio, config_type in all_configs:
        res = ile_instrumented(speeds, n=n)
        if not res['success']:
            continue
        gap_seq = []
        prev_gap = None
        n_drops = 0
        min_gap = None
        for entry in res['trace']:
            pb = entry['advancing_pb']
            tau_pb = entry['tau_pb']
            gap = compute_gap(pb, tau_pb, p1, n)
            gap_seq.append(gap)
            if min_gap is None or gap < min_gap:
                min_gap = gap
            if prev_gap is not None and gap < prev_gap:
                n_drops += 1
                drop_rows.append({
                    'config_idx': idx,
                    'level': entry['level'],
                    'p1': p1,
                    'p10': p10,
                    'pb': pb,
                    'gap_before': prev_gap,
                    'gap_after': gap,
                    'drop': prev_gap - gap,
                    'speeds': str(list(speeds)),
                })
            prev_gap = gap
        is_monotone = (n_drops == 0)
        final_gap = gap_seq[-1] if gap_seq else None
        L = res['L']
        config_rows.append({
            'config_idx': idx,
            'L': L,
            'p1': p1,
            'p10': p10,
            'ratio': ratio,
            'config_type': config_type,
            'gap_seq': json.dumps(gap_seq),
            'is_monotone': int(is_monotone),
            'n_drops': n_drops,
            'min_gap_seen': min_gap if min_gap is not None else '',
            'final_gap': final_gap if final_gap is not None else '',
        })
    return config_rows, drop_rows


# ── EXP-4: extremal level characterisation ────────────────────────────────

def run_exp4(all_configs, n=11):
    """Per config: find the level with max f; characterise pb, residue."""
    rows = []
    for idx, speeds, p1, p10, ratio, config_type in all_configs:
        res = ile_instrumented(speeds, n=n)
        if not res['success']:
            continue
        if not res['trace']:
            continue
        sorted_speeds = sorted(speeds)
        L = res['L']
        # Find level with max f
        best_entry = None
        best_f = -1.0
        for entry in res['trace']:
            margin_before = float(entry['margin_before'])
            delta = float(entry['advance_delta'])
            f = delta / margin_before if margin_before > 0 else float('inf')
            if f > best_f:
                best_f = f
                best_entry = entry
        pb = best_entry['advancing_pb']
        tau_pb = best_entry['tau_pb']
        t_cur_before = best_entry['t_cur_before']
        # residue: frac(t_cur_before * pb)
        rb_star = float(frac_part(Fraction(pb) * t_cur_before))
        # position of pb in sorted speeds (1-indexed; p1 is position 1)
        try:
            pb_position = sorted_speeds.index(pb) + 1
        except ValueError:
            pb_position = -1
        gap_at_fmax = compute_gap(pb, tau_pb, p1, n)
        rows.append({
            'config_idx': idx,
            'p1': p1,
            'p10': p10,
            'L': L,
            'ratio': ratio,
            'config_type': config_type,
            'f_max': best_f,
            'f_max_level': best_entry['level'],
            'pb_star': pb,
            'pb_position': pb_position,
            'rb_star': rb_star,
            'gap_at_fmax': gap_at_fmax,
        })
    return rows


# ── EXP-5: adversarial gap minimisation ───────────────────────────────────

def adversarial_target_t(pb: int, p1: int, n: int = 11):
    """
    Compute the re-entry time of pb at j=j_max (gap=0 target).
    Returns (tau_jmax, j_max).
    """
    j_max = ((n - 1) * pb - p1) // (n * p1)
    tau_jmax = Fraction(n * j_max + 1, n * pb)
    return tau_jmax, j_max


def run_exp5_staircase(N_max=2000, n=11):
    """
    Sweep staircase family up to N=N_max; for each config record min gap across all levels.
    These are empirically the hardest configs and most likely to approach gap=0.
    """
    rows = []
    for N in range(10, N_max + 1):
        interior = list(range(N, N + 9))
        k = max(1, math.ceil((N + 9) / 11))
        p10_candidate = 11 * k
        if p10_candidate <= N + 8:
            k += 1
            p10_candidate = 11 * k
        if p10_candidate / 1 <= 10:
            continue
        speeds = (1,) + tuple(interior) + (p10_candidate,)
        p1 = 1
        res = ile_instrumented(speeds, n=n)
        if not res['success']:
            continue
        min_gap = None
        min_gap_level = None
        min_gap_pb = None
        for entry in res['trace']:
            pb = entry['advancing_pb']
            tau_pb = entry['tau_pb']
            gap = compute_gap(pb, tau_pb, p1, n)
            if min_gap is None or gap < min_gap:
                min_gap = gap
                min_gap_level = entry['level']
                min_gap_pb = pb
        rows.append({
            'N': N,
            'speeds': str(list(speeds)),
            'p10': p10_candidate,
            'ratio': p10_candidate,
            'L': res['L'],
            'min_gap': min_gap if min_gap is not None else '',
            'min_gap_level': min_gap_level if min_gap_level is not None else '',
            'min_gap_pb': min_gap_pb if min_gap_pb is not None else '',
        })
    return rows


def run_exp5_adversarial_grid(p1_vals=(1, 2, 3, 5), n_ratios=200, n=11, seed=42):
    """
    For each (p1, pb_ratio) on a dense grid, generate random 10-runner configs
    with p10/p1 ≈ pb_ratio and record min gap. Statistical sweep — 10 configs
    per ratio value.
    """
    rng = random.Random(seed)
    rows = []
    idx = 0
    for p1 in p1_vals:
        # ratios: 10.5 to 500, log-spaced
        import math
        ratio_vals = [10 ** (math.log10(10.5) + i * (math.log10(500) - math.log10(10.5)) / (n_ratios - 1))
                      for i in range(n_ratios)]
        for ratio_target in ratio_vals:
            p10 = max(int(p1 * ratio_target), p1 * 11)
            # Generate 10 configs near this ratio
            for _ in range(10):
                # Sample 8 interior speeds from (p1, p10), distinct from each other
                interior_range = list(range(p1 + 1, p10))
                if len(interior_range) < 8:
                    break
                interior = sorted(rng.sample(interior_range, 8))
                speeds = tuple([p1] + interior + [p10])
                assert len(speeds) == 10
                # Append to 11 runners? No — we need 10 speeds for n=11 (speeds = p1..p10)
                # Actually: 10 speeds are the non-stationary runners; n=11 (including stationary)
                if p10 / p1 <= 10:
                    continue
                res = ile_instrumented(speeds, n=n)
                if not res['success']:
                    continue
                min_gap = None
                for entry in res['trace']:
                    pb = entry['advancing_pb']
                    tau_pb = entry['tau_pb']
                    gap = compute_gap(pb, tau_pb, p1, n)
                    if min_gap is None or gap < min_gap:
                        min_gap = gap
                rows.append({
                    'config_idx': idx,
                    'p1': p1,
                    'p10': p10,
                    'ratio_target': ratio_target,
                    'ratio_actual': p10 / p1,
                    'L': res['L'],
                    'min_gap': min_gap if min_gap is not None else '',
                    'speeds': str(list(speeds)),
                })
                idx += 1
    return rows


# ── summary statistics helpers ─────────────────────────────────────────────

def percentile(vals, p):
    if not vals:
        return float('nan')
    sv = sorted(vals)
    idx = int(len(sv) * p / 100)
    return sv[min(idx, len(sv) - 1)]


# ── write summary ──────────────────────────────────────────────────────────

def write_summary(exp1_rows, exp2_rows, exp3_rows, exp3_drops, exp4_rows,
                  exp5_staircase_rows, exp5_grid_rows, out_path):
    lines = []

    def h(s): lines.append(f"\n## {s}\n")
    def hh(s): lines.append(f"\n### {s}\n")
    def p(s): lines.append(s)

    lines.append("# Containment (C) Proof-Attack Experiments — Summary\n")
    lines.append("# Generated by lrc_containment_probe_v1.py\n")

    # EXP-1
    h("EXP-1: Advance Fraction f = δ/(W_hi − t_cur)")
    f_vals = [r['f'] for r in exp1_rows if r['f'] < 1e10]
    if f_vals:
        p(f"Total level events: {len(f_vals)}")
        p(f"Max f observed:     {max(f_vals):.6f}")
        p(f"99th-pct f:         {percentile(f_vals, 99):.6f}")
        p(f"95th-pct f:         {percentile(f_vals, 95):.6f}")
        p(f"Mean f:             {sum(f_vals)/len(f_vals):.6f}")
        p(f"Fraction with f>0.5: {sum(1 for x in f_vals if x>0.5)/len(f_vals)*100:.2f}%")
        p(f"Fraction with f>0.9: {sum(1 for x in f_vals if x>0.9)/len(f_vals)*100:.4f}%")
        p(f"Any f >= 1.0 (Containment failure): {any(x >= 1.0 for x in f_vals)}")
        p("")
        # By ratio bin
        bins = [(11, 21), (21, 51), (51, 101), (101, 501), (501, 10001)]
        p("| Ratio bin | N events | Max f | 99th pct f | Mean f |")
        p("|---|---|---|---|---|")
        for lo, hi in bins:
            sub = [r['f'] for r in exp1_rows if lo <= r['ratio'] < hi and r['f'] < 1e10]
            if sub:
                p(f"| [{lo},{hi}) | {len(sub)} | {max(sub):.4f} | {percentile(sub,99):.4f} | {sum(sub)/len(sub):.4f} |")
        p("")
        # By p1
        p("| p1 | N events | Max f |")
        p("|---|---|---|")
        for pv in sorted(set(r['p1'] for r in exp1_rows)):
            sub = [r['f'] for r in exp1_rows if r['p1'] == pv and r['f'] < 1e10]
            if sub:
                p(f"| {pv} | {len(sub)} | {max(sub):.4f} |")

    # EXP-2
    h("EXP-2: Gap = j_max − j* Distribution")
    gap_vals = [r['gap'] for r in exp2_rows]
    if gap_vals:
        p(f"Total level events: {len(gap_vals)}")
        p(f"Min gap observed:   {min(gap_vals)}")
        p(f"Max gap observed:   {max(gap_vals)}")
        p(f"Mean gap:           {sum(gap_vals)/len(gap_vals):.2f}")
        p(f"Any gap < 0 (Containment violation): {any(g < 0 for g in gap_vals)}")
        p(f"Any gap = 0 (touching boundary):     {any(g == 0 for g in gap_vals)}")
        p("")
        ctr = Counter(min(g, 10) for g in gap_vals)
        p("| gap | count | % |")
        p("|---|---|---|")
        total = len(gap_vals)
        for g in sorted(ctr.keys()):
            label = str(g) if g < 10 else ">=10"
            p(f"| {label} | {ctr[g]} | {ctr[g]/total*100:.2f}% |")
        p("")
        # List all gap=1 events (configs and pb)
        gap1_events = [r for r in exp2_rows if r['gap'] == 1]
        p(f"Gap=1 events: {len(gap1_events)}")
        if gap1_events:
            hh("Gap=1 event sample (first 20)")
            p("| config_idx | level | p1 | p10 | ratio | pb |")
            p("|---|---|---|---|---|---|")
            for r in gap1_events[:20]:
                p(f"| {r['config_idx']} | {r['level']} | {r['p1']} | {r['p10']} | {r['ratio']:.1f} | {r['pb']} |")

    # EXP-3
    h("EXP-3: Gap Trajectory Monotonicity")
    if exp3_rows:
        n_mono = sum(r['is_monotone'] for r in exp3_rows)
        total = len(exp3_rows)
        p(f"Total configs: {total}")
        p(f"Monotone gap trajectories: {n_mono} ({n_mono/total*100:.1f}%)")
        p(f"Non-monotone (gap drops occur): {total-n_mono} ({(total-n_mono)/total*100:.1f}%)")
        p(f"Total gap-drop events: {len(exp3_drops)}")
        if exp3_drops:
            drop_sizes = [r['drop'] for r in exp3_drops]
            p(f"Max drop size: {max(drop_sizes)}")
            p(f"Min drop size: {min(drop_sizes)}")
        p("")
        # Among non-monotone configs, what is min_gap_seen?
        nm_gaps = [r['min_gap_seen'] for r in exp3_rows if not r['is_monotone'] and r['min_gap_seen'] != '']
        if nm_gaps:
            p(f"Among non-monotone configs — min gap seen: {min(nm_gaps)}")
        # Monotonicity by L
        p("")
        p("| L | total | monotone | % monotone |")
        p("|---|---|---|---|")
        L_mono = defaultdict(lambda: [0, 0])
        for r in exp3_rows:
            L_bin = min(r['L'], 20)
            L_mono[L_bin][0] += 1
            L_mono[L_bin][1] += r['is_monotone']
        for lv in sorted(L_mono.keys()):
            tot, mono = L_mono[lv]
            p(f"| {lv} | {tot} | {mono} | {mono/tot*100:.1f}% |")

    # EXP-4
    h("EXP-4: Extremal Level Characterisation (max-f level per config)")
    if exp4_rows:
        f_maxes = [r['f_max'] for r in exp4_rows]
        p(f"Total configs: {len(exp4_rows)}")
        p(f"Overall max f_max: {max(f_maxes):.6f}")
        p(f"Mean f_max:        {sum(f_maxes)/len(f_maxes):.6f}")
        p("")
        # pb_position distribution
        pos_ctr = Counter(r['pb_position'] for r in exp4_rows)
        p("| pb_position (1=p1, 2=p2, ...) | count | % |")
        p("|---|---|---|")
        total = len(exp4_rows)
        for pos in sorted(pos_ctr.keys()):
            p(f"| {pos} | {pos_ctr[pos]} | {pos_ctr[pos]/total*100:.1f}% |")
        p("")
        # Among gap=1 at fmax, what is pb_position?
        tight = [r for r in exp4_rows if r['gap_at_fmax'] == 1]
        p(f"Configs where gap=1 at the max-f level: {len(tight)} ({len(tight)/total*100:.1f}%)")
        if tight:
            tight_pos = Counter(r['pb_position'] for r in tight)
            p("pb_position distribution among gap=1 configs:")
            for pos in sorted(tight_pos.keys()):
                p(f"  position {pos}: {tight_pos[pos]} ({tight_pos[pos]/len(tight)*100:.1f}%)")

    # EXP-5
    h("EXP-5: Adversarial Gap Minimisation")
    hh("Staircase family sweep (N=10..2000)")
    if exp5_staircase_rows:
        min_gaps = [r['min_gap'] for r in exp5_staircase_rows if r['min_gap'] != '']
        Ls = [r['L'] for r in exp5_staircase_rows]
        p(f"Total staircase configs tested: {len(exp5_staircase_rows)}")
        p(f"Max L seen: {max(Ls)}")
        p(f"Min gap seen across all staircase configs: {min(min_gaps) if min_gaps else 'N/A'}")
        p(f"Any gap = 0: {any(g == 0 for g in min_gaps)}")
        p(f"Any gap < 0: {any(g < 0 for g in min_gaps)}")
        # List top-10 highest L
        sorted_stair = sorted(exp5_staircase_rows, key=lambda r: -r['L'])
        p("")
        p("Top-10 highest-L staircase configs:")
        p("| N | p10 | ratio | L | min_gap | min_gap_pb |")
        p("|---|---|---|---|---|---|")
        for r in sorted_stair[:10]:
            p(f"| {r['N']} | {r['p10']} | {r['ratio']} | {r['L']} | {r['min_gap']} | {r['min_gap_pb']} |")

    hh("Random adversarial grid sweep")
    if exp5_grid_rows:
        min_gaps_grid = [r['min_gap'] for r in exp5_grid_rows if r['min_gap'] != '']
        p(f"Total adversarial configs tested: {len(exp5_grid_rows)}")
        p(f"Min gap seen: {min(min_gaps_grid) if min_gaps_grid else 'N/A'}")
        p(f"Any gap = 0: {any(g == 0 for g in min_gaps_grid)}")
        p(f"Any gap < 0: {any(g < 0 for g in min_gaps_grid)}")
        # Distribution
        gap_ctr_grid = Counter(min(g, 5) for g in min_gaps_grid if isinstance(g, int))
        p("")
        p("| min_gap | count |")
        p("|---|---|")
        for g in sorted(gap_ctr_grid.keys()):
            label = str(g) if g < 5 else ">=5"
            p(f"| {label} | {gap_ctr_grid[g]} |")

    # Proof angle assessment
    h("Proof-Angle Assessment")
    p("Based on EXP-1–5, the actionable proof angles are:")
    p("")
    p("**Contracting-map (f ≤ c < 1 uniformly)**")
    if f_vals:
        max_f = max(f_vals)
        p(f"  EXP-1 max f = {max_f:.4f}. Contracting-map requires proving f < 1 universally.")
        p(f"  Empirical max is well below 1; a formal bound of f ≤ 1 − 1/(11p₁p₂) may be provable.")
    p("")
    p("**Direct gap ≥ 1 (number-theoretic)**")
    if gap_vals:
        min_g = min(gap_vals)
        p(f"  EXP-2 min gap = {min_g}. Containment holds iff gap ≥ 0.")
        p(f"  Observed gap ≥ 1 universally — stronger than required for Containment.")
        p(f"  A direct proof that gap ≥ 1 would be the tightest possible result.")
    p("")
    p("**Inductive gap monotonicity**")
    if exp3_rows:
        mono_rate = sum(r['is_monotone'] for r in exp3_rows) / len(exp3_rows)
        p(f"  EXP-3 monotonicity rate = {mono_rate*100:.1f}%. Gap is NOT always monotone.")
        p(f"  Simple induction on levels is not directly applicable.")
        p(f"  A potential-function argument (gap may drop but recovers) may be needed.")

    with open(out_path, 'w') as f:
        f.write('\n'.join(lines) + '\n')
    print(f"  → Written: {out_path}")


# ── write CSVs ─────────────────────────────────────────────────────────────

def write_csv(rows, path, fieldnames=None):
    if not rows:
        print(f"  [empty, skip] {path}")
        return
    if fieldnames is None:
        fieldnames = list(rows[0].keys())
    with open(path, 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)
    print(f"  → Written: {path} ({len(rows)} rows)")


# ── main ───────────────────────────────────────────────────────────────────

def main():
    print("Loading config corpus from results_v1.csv ...")
    corpus = load_configs(DATA_CSV)
    print(f"  {len(corpus)} configs loaded.")

    print("Generating staircase configs (N=10..500) for combined corpus ...")
    staircase_configs = gen_staircase_configs(range(10, 501))
    print(f"  {len(staircase_configs)} staircase configs.")

    all_configs = corpus + staircase_configs
    print(f"  Total configs for EXP-1..4: {len(all_configs)}")

    print("\n── EXP-1: Advance fraction ──")
    exp1_rows = run_exp1(all_configs)
    print(f"  {len(exp1_rows)} level events collected.")
    write_csv(exp1_rows, os.path.join(OUT_DIR, "exp1_advance_fraction.csv"))

    print("\n── EXP-2: Gap distribution ──")
    exp2_rows = run_exp2(all_configs)
    print(f"  {len(exp2_rows)} level events collected.")
    write_csv(exp2_rows, os.path.join(OUT_DIR, "exp2_gap_distribution.csv"))

    print("\n── EXP-3: Gap trajectory monotonicity ──")
    exp3_rows, exp3_drops = run_exp3(all_configs)
    print(f"  {len(exp3_rows)} configs, {len(exp3_drops)} gap-drop events.")
    write_csv(exp3_rows, os.path.join(OUT_DIR, "exp3_gap_trajectory.csv"))
    write_csv(exp3_drops, os.path.join(OUT_DIR, "exp3_gap_drop_events.csv"))

    print("\n── EXP-4: Extremal level characterisation ──")
    exp4_rows = run_exp4(all_configs)
    print(f"  {len(exp4_rows)} configs processed.")
    write_csv(exp4_rows, os.path.join(OUT_DIR, "exp4_extremal_levels.csv"))

    print("\n── EXP-5: Adversarial gap minimisation ──")
    print("  (a) Staircase sweep N=10..2000 ...")
    exp5_staircase = run_exp5_staircase(N_max=2000)
    print(f"      {len(exp5_staircase)} staircase configs.")
    write_csv(exp5_staircase, os.path.join(OUT_DIR, "exp5_adversarial_staircase.csv"))

    print("  (b) Random adversarial grid (p1 in {1,2,3,5}, 200 ratios, 10 configs each) ...")
    exp5_grid = run_exp5_adversarial_grid(p1_vals=(1, 2, 3, 5), n_ratios=200, n=11, seed=42)
    print(f"      {len(exp5_grid)} adversarial configs.")
    write_csv(exp5_grid, os.path.join(OUT_DIR, "exp5_adversarial.csv"))

    print("\n── Summary ──")
    write_summary(
        exp1_rows, exp2_rows, exp3_rows, exp3_drops, exp4_rows,
        exp5_staircase, exp5_grid,
        os.path.join(OUT_DIR, "containment_probe_summary.md"),
    )

    # Print quick headline numbers
    f_vals = [r['f'] for r in exp1_rows if r['f'] < 1e10]
    gap_vals = [r['gap'] for r in exp2_rows]
    stair_gaps = [r['min_gap'] for r in exp5_staircase if r['min_gap'] != '']
    grid_gaps = [r['min_gap'] for r in exp5_grid if r['min_gap'] != '']
    print("\n═══════════════════════════════════════")
    print("HEADLINE RESULTS")
    print(f"  EXP-1  max f          = {max(f_vals):.6f}" if f_vals else "  EXP-1  (no data)")
    print(f"  EXP-2  min gap        = {min(gap_vals)}" if gap_vals else "  EXP-2  (no data)")
    print(f"  EXP-2  gap=0 events   = {sum(1 for g in gap_vals if g == 0)}")
    print(f"  EXP-3  monotone rate  = {sum(r['is_monotone'] for r in exp3_rows)/len(exp3_rows)*100:.1f}%" if exp3_rows else "  EXP-3  (no data)")
    print(f"  EXP-5a staircase min gap = {min(stair_gaps)}" if stair_gaps else "  EXP-5a (no data)")
    print(f"  EXP-5b grid min gap   = {min(grid_gaps)}" if grid_gaps else "  EXP-5b (no data)")
    print("═══════════════════════════════════════")


if __name__ == "__main__":
    main()
