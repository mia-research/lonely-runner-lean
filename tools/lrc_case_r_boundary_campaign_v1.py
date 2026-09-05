"""
lrc_case_r_boundary_campaign_v1.py
===================================
Referee-facing corroboration campaign for LRC Case R> (n=11).

Uses the exact boundary-set method from lrc_case_r_harness.py.
Runs as a resumable, chunked, low-priority background campaign.

This file is NOT part of the logical proof chain. It is a corroboration
bundle for referee review.

CLI:
    python3 tools/lrc_case_r_boundary_campaign_v1.py \\
        --target-configs 1000000 \\
        --workers 6 \\
        --chunk-size 5000 \\
        --seed 20260330 \\
        --output-root reports/investigations/INV-CASE-R-BOUNDARY-001 \\
        --resume

Optional:
    --full-metrics      Compute joint-window max_gap_J (slower)
    --family A|B|C|P    Run a single family (for debugging)
    --max-chunks N      Stop after N chunks (smoke test)
"""

import argparse
import gzip
import json
import math
import multiprocessing
import os
import random
import sys
import time
from collections import defaultdict
from fractions import Fraction

# ─────────────────────────────────────────────────────────────────────────────
# Exact arithmetic helpers  (self-contained; mirrors lrc_case_r_harness.py)
# ─────────────────────────────────────────────────────────────────────────────

N = 11  # runner count


def _frac_part(x: Fraction) -> Fraction:
    return x - int(x)


def _dist(x: Fraction) -> Fraction:
    """||x|| = min({x}, 1-{x})"""
    f = _frac_part(x)
    return min(f, Fraction(1) - f)


def _min_isolation(speeds, t: Fraction) -> Fraction:
    thr = Fraction(1, N)
    best = Fraction(1)
    for p in speeds:
        d = _dist(Fraction(p) * t)
        if d < best:
            best = d
        if d < thr:
            return d  # early exit once we know it's below threshold
    return best


def _all_isolated(speeds, t: Fraction) -> bool:
    thr = Fraction(1, N)
    for p in speeds:
        if _dist(Fraction(p) * t) < thr:
            return False
    return True


# ─────────────────────────────────────────────────────────────────────────────
# Campaign-fast boundary-set check
# Returns a compact dict; skips joint-window analysis unless full_metrics=True
# ─────────────────────────────────────────────────────────────────────────────

def campaign_check(speeds, full_metrics: bool = False) -> dict:
    """
    Boundary-set witness search for one config.

    Returns:
        success          bool
        witness_t        str (exact Fraction) or None
        min_isolation    float  (at witness, or best achieved)
        p1, p10, ratio   int / float
        boundary_count   int
        config_family    str  (populated by caller)
        seed             int  (populated by caller)
        ratio_band       str  (populated by caller)
        max_gap_J        float or None  (only if full_metrics)
    """
    p1 = speeds[0]
    p10 = speeds[-1]
    T_cap = Fraction(2, p1)
    thr = Fraction(1, N)

    # 1. Critical times
    critical_times = set()
    for p in speeds:
        j = 0
        while True:
            t_entry = Fraction(N * j + 1, N * p)
            if t_entry > T_cap:
                break
            critical_times.add(t_entry)
            t_exit = Fraction(N * j + (N - 1), N * p)
            if t_exit <= T_cap:
                critical_times.add(t_exit)
            j += 1

    sorted_times = sorted(critical_times)
    boundary_count = len(sorted_times)

    # 2. Build candidate list: critical times + midpoints
    candidates = []
    if sorted_times:
        mid0 = sorted_times[0] / 2
        if mid0 > Fraction(0):
            candidates.append(mid0)
        candidates.extend(sorted_times)
        for i in range(len(sorted_times) - 1):
            candidates.append((sorted_times[i] + sorted_times[i + 1]) / 2)
        mid_last = (sorted_times[-1] + T_cap) / 2
        if mid_last <= T_cap:
            candidates.append(mid_last)

    # 3. Witness search
    witness_t = None
    best_min_iso = Fraction(0)

    for t in sorted(set(candidates)):
        if t <= Fraction(0) or t > T_cap:
            continue
        m_iso = _min_isolation(speeds, t)
        if m_iso >= thr:
            if witness_t is None:
                witness_t = t
                best_min_iso = m_iso
                break   # first witness is enough for corroboration
        else:
            if witness_t is None and m_iso > best_min_iso:
                best_min_iso = m_iso

    result = dict(
        success=witness_t is not None,
        witness_t=str(witness_t) if witness_t is not None else None,
        min_isolation=float(best_min_iso),
        p1=p1,
        p10=p10,
        ratio=p10 / p1,
        boundary_count=boundary_count,
        max_gap_J=None,
    )

    if full_metrics and sorted_times:
        # Joint-window analysis for max_gap_J
        breakpoints = sorted(set([Fraction(0)] + list(critical_times) + [T_cap]))
        joint_windows = []
        window_start = None
        for i in range(len(breakpoints) - 1):
            a = breakpoints[i]
            b = breakpoints[i + 1]
            mid = (a + b) / 2
            if mid <= Fraction(0) or mid > T_cap:
                continue
            if _all_isolated(speeds, mid):
                if window_start is None:
                    window_start = a
            else:
                if window_start is not None:
                    joint_windows.append((window_start, a))
                    window_start = None
        if window_start is not None:
            joint_windows.append((window_start, T_cap))

        max_gap_J = Fraction(0)
        if not joint_windows:
            max_gap_J = T_cap
        else:
            max_gap_J = max(max_gap_J, joint_windows[0][0])
            for k in range(len(joint_windows) - 1):
                gap = joint_windows[k + 1][0] - joint_windows[k][1]
                max_gap_J = max(max_gap_J, gap)
            max_gap_J = max(max_gap_J, T_cap - joint_windows[-1][1])

        result['max_gap_J'] = float(max_gap_J)

    return result


# ─────────────────────────────────────────────────────────────────────────────
# Ratio band helper
# ─────────────────────────────────────────────────────────────────────────────

RATIO_BANDS = [
    (10, 20,   "10-20"),
    (20, 50,   "20-50"),
    (50, 100,  "50-100"),
    (100, 250, "100-250"),
    (250, 1000,"250-1000"),
]

def ratio_band(ratio: float) -> str:
    for lo, hi, label in RATIO_BANDS:
        if lo < ratio <= hi:
            return label
    return f"other-{ratio:.0f}"


# ─────────────────────────────────────────────────────────────────────────────
# Deterministic stratified config generator
# ─────────────────────────────────────────────────────────────────────────────

def _validate_speeds(speeds) -> bool:
    if len(speeds) != 10:
        return False
    if speeds[0] >= speeds[-1]:
        return False
    if speeds[-1] / speeds[0] <= 10:
        return False
    return True


def gen_type_a_large_campaign(n_per_band: int, base_seed: int):
    """
    Type A-large: log-uniform ratio sampling, split evenly across 5 ratio bands.
    Each band uses deterministic seed derived from base_seed + band index.
    Yields (speeds, 'A', seed_used, ratio_band_label).
    """
    for band_idx, (lo, hi, label) in enumerate(RATIO_BANDS):
        band_seed = base_seed + band_idx * 1_000_000
        rng = random.Random(band_seed)
        produced = 0
        attempts = 0
        max_attempts = n_per_band * 50
        while produced < n_per_band and attempts < max_attempts:
            attempts += 1
            p1 = rng.randint(1, 10)
            log_r = rng.uniform(math.log10(lo + 1e-9), math.log10(hi))
            target_ratio = 10 ** log_r
            p10 = max(p1 * lo + 1, round(p1 * target_ratio))
            interior_range = list(range(p1 + 1, p10))
            if len(interior_range) < 8:
                continue
            interior = sorted(rng.sample(interior_range, 8))
            speeds = [p1] + interior + [p10]
            if not _validate_speeds(speeds):
                continue
            actual_ratio = speeds[-1] / speeds[0]
            if actual_ratio <= lo or actual_ratio > hi:
                continue
            yield (speeds, 'A', band_seed + produced, label)
            produced += 1


def gen_type_b_stress_campaign(n_total: int, base_seed: int):
    """
    Type B-stress: resonant + consecutive adversarial families, expanded with
    deterministic seed-driven variants. Yields up to n_total configs.
    """
    catalog = []

    # Base resonant skeleton: k*(1..9) + [10k+1]
    for k in range(1, 31):
        p1 = k
        interior = [k * i for i in range(2, 10)]
        p10 = 10 * k + 1
        speeds = [p1] + interior + [p10]
        if _validate_speeds(speeds):
            catalog.append((speeds, 'B-resonant'))

    # Consecutive: (p1..p1+8, p1*R)
    for p1 in [1, 2, 3, 5]:
        for R in [11, 12, 15, 20, 50, 100, 200, 500, 1000]:
            p10 = p1 * R
            interior = list(range(p1 + 1, p1 + 9))
            if max(interior) >= p10:
                continue
            speeds = [p1] + interior + [p10]
            if _validate_speeds(speeds):
                catalog.append((speeds, 'B-consec'))

    # Paper examples
    for speeds in [
        [1, 4, 7, 9, 11, 12, 14, 15, 16, 20],
        [1, 5, 8, 10, 13, 14, 16, 18, 19, 22],
    ]:
        if _validate_speeds(speeds):
            catalog.append((speeds, 'B-paper'))

    produced = 0
    # First pass: yield base catalog entries
    for speeds, fam in catalog:
        if produced >= n_total:
            return
        label = ratio_band(speeds[-1] / speeds[0])
        yield (speeds, fam, base_seed + produced, label)
        produced += 1

    # Expansion: deterministic seed-driven perturbations of resonant skeletons
    rng = random.Random(base_seed + 99_999)
    while produced < n_total:
        k = rng.randint(1, 30)
        p1 = k
        p10_base = 10 * k + 1
        # Jitter p10 slightly (preserve ratio > 10)
        p10 = p10_base + rng.randint(0, 5 * k)
        interior_pool = list(range(p1 + 1, p10))
        if len(interior_pool) < 8:
            continue
        # Near-resonant interior (start from k multiples, then perturb)
        resonant_interior = [k * i for i in range(2, 10) if p1 < k * i < p10]
        if len(resonant_interior) < 4:
            interior = sorted(rng.sample(interior_pool, 8))
        else:
            # Keep some resonant, replace others
            keep = rng.sample(resonant_interior, min(4, len(resonant_interior)))
            remaining = [x for x in interior_pool if x not in keep]
            if len(remaining) < 8 - len(keep):
                continue
            extra = rng.sample(remaining, 8 - len(keep))
            interior = sorted(keep + extra)
        speeds = [p1] + interior + [p10]
        if not _validate_speeds(speeds):
            continue
        label = ratio_band(speeds[-1] / speeds[0])
        yield (speeds, 'B-resonant-var', base_seed + produced, label)
        produced += 1


def gen_type_c_extreme_campaign(n_total: int, base_seed: int):
    """
    Type C-extreme: near-boundary and very-high-ratio configs, expanded.
    """
    catalog = []

    base9 = [1, 2, 3, 4, 5, 6, 7, 8, 9]
    for R in [11, 12, 13, 15, 20, 30, 50, 100, 200, 500, 1000]:
        speeds = base9 + [R]
        if _validate_speeds(speeds):
            catalog.append((speeds, 'C-ratio'))

    odd9 = [1, 3, 5, 7, 9, 11, 13, 15, 17]
    for p10 in [19, 21, 51, 101, 201, 501, 1001]:
        speeds = odd9 + [p10]
        if _validate_speeds(speeds):
            catalog.append((speeds, 'C-odd'))

    for p1 in [1, 2, 3, 5]:
        for mult in [11, 50, 100, 500, 1000]:
            p10 = p1 * mult
            interior = list(range(p1 + 1, p1 + 9))
            if max(interior) >= p10:
                continue
            speeds = [p1] + interior + [p10]
            if _validate_speeds(speeds):
                catalog.append((speeds, 'C-extreme'))

    produced = 0
    for speeds, fam in catalog:
        if produced >= n_total:
            return
        label = ratio_band(speeds[-1] / speeds[0])
        yield (speeds, fam, base_seed + produced, label)
        produced += 1

    rng = random.Random(base_seed + 77_777)
    while produced < n_total:
        p1 = rng.randint(1, 5)
        # Extreme ratio: bias toward 50-1000
        log_r = rng.uniform(math.log10(50), math.log10(1000))
        p10 = max(p1 * 51, round(p1 * (10 ** log_r)))
        interior_pool = list(range(p1 + 1, p10))
        if len(interior_pool) < 8:
            continue
        # Near-boundary: prefer low interior speeds (stress containment)
        low_pool = interior_pool[:max(8, len(interior_pool) // 3)]
        if len(low_pool) < 8:
            low_pool = interior_pool
        interior = sorted(rng.sample(low_pool, 8))
        speeds = [p1] + interior + [p10]
        if not _validate_speeds(speeds):
            continue
        label = ratio_band(speeds[-1] / speeds[0])
        yield (speeds, 'C-extreme-var', base_seed + produced, label)
        produced += 1


def gen_type_p_campaign(n_total: int, base_seed: int):
    """
    Type P: pacemaker configs (p10 = 11*k*p1) plus ratio-11 missing-speed family.
    """
    catalog = []

    # P-ratio11: p1=1, p10=11, missing one interior speed
    for m in range(2, 11):
        speeds = [1] + [k for k in range(2, 11) if k != m] + [11]
        if _validate_speeds(speeds):
            catalog.append((speeds, 'P-ratio11'))

    # P-higher: p10 = 11*k for k in 2..10
    for k in range(2, 11):
        p1 = 1
        p10 = 11 * k
        interior_pool = list(range(2, p10))
        if len(interior_pool) < 8:
            continue
        rng0 = random.Random(12345 * k)
        for trial in range(10):
            interior = sorted(rng0.sample(interior_pool, 8))
            speeds = [p1] + interior + [p10]
            if _validate_speeds(speeds):
                catalog.append((speeds, f'P-k{k}'))
        # Consecutive interior (hardest)
        consec = list(range(2, 10))
        if max(consec) < p10:
            speeds = [p1] + consec + [p10]
            if _validate_speeds(speeds):
                catalog.append((speeds, f'P-k{k}-consec'))

    produced = 0
    for speeds, fam in catalog:
        if produced >= n_total:
            return
        label = ratio_band(speeds[-1] / speeds[0])
        yield (speeds, fam, base_seed + produced, label)
        produced += 1

    # Expansion: p10 = 11*k*p1, preserve p10 = 11k structure
    rng = random.Random(base_seed + 55_555)
    while produced < n_total:
        k = rng.randint(2, 20)
        p1 = rng.randint(1, 5)
        p10 = 11 * k * p1
        interior_pool = list(range(p1 + 1, p10))
        if len(interior_pool) < 8:
            continue
        # Prefer multiples of p1 in interior to preserve pacemaker motif
        multiples = [m * p1 for m in range(2, p10 // p1) if p1 < m * p1 < p10]
        if len(multiples) >= 4:
            keep = rng.sample(multiples, min(4, len(multiples)))
            remaining = [x for x in interior_pool if x not in keep]
            if len(remaining) < 8 - len(keep):
                continue
            extra = rng.sample(remaining, 8 - len(keep))
            interior = sorted(keep + extra)
        else:
            interior = sorted(rng.sample(interior_pool, 8))
        speeds = [p1] + interior + [p10]
        if not _validate_speeds(speeds):
            continue
        label = ratio_band(speeds[-1] / speeds[0])
        yield (speeds, 'P-higher-var', base_seed + produced, label)
        produced += 1


# ─────────────────────────────────────────────────────────────────────────────
# Master config plan builder
# Builds the full ordered plan as (speeds, family, seed, ratio_band) tuples.
# Each config has a deterministic global index (config_id).
# ─────────────────────────────────────────────────────────────────────────────

def build_config_plan(target_configs: int, master_seed: int, family_filter=None):
    """
    Returns a list of (config_id, speeds, family, seed, band) for the full plan.
    If family_filter is set ('A','B','C','P'), returns only that family.
    """
    # Default mix for 1_000_000:  A=900k, B=50k, C=30k, P=20k
    # Scale proportionally for other targets.
    scale = target_configs / 1_000_000
    n_a = max(1, round(900_000 * scale))
    n_b = max(1, round(50_000 * scale))
    n_c = max(1, round(30_000 * scale))
    n_p = max(1, round(20_000 * scale))

    n_per_band = n_a // len(RATIO_BANDS)

    plan = []
    config_id = 0

    def add(gen, fam_letter):
        nonlocal config_id
        if family_filter and family_filter != fam_letter:
            return
        for item in gen:
            speeds, fam, seed, band = item
            plan.append((config_id, speeds, fam, seed, band))
            config_id += 1

    add(gen_type_a_large_campaign(n_per_band, master_seed + 0), 'A')
    add(gen_type_b_stress_campaign(n_b, master_seed + 10_000_000), 'B')
    add(gen_type_c_extreme_campaign(n_c, master_seed + 20_000_000), 'C')
    add(gen_type_p_campaign(n_p, master_seed + 30_000_000), 'P')

    return plan


# ─────────────────────────────────────────────────────────────────────────────
# Worker: processes one chunk of config_ids
# ─────────────────────────────────────────────────────────────────────────────

def _process_chunk(args):
    """
    Worker function (runs in subprocess via multiprocessing).
    args = (chunk_id, chunk_items, full_metrics)
    chunk_items = list of (config_id, speeds, family, seed, band)
    Returns list of result dicts.
    """
    chunk_id, chunk_items, full_metrics = args
    records = []
    for config_id, speeds, family, seed, band in chunk_items:
        t0 = time.perf_counter()
        try:
            r = campaign_check(speeds, full_metrics=full_metrics)
            elapsed = time.perf_counter() - t0
            rec = dict(
                config_id=config_id,
                config_family=family,
                seed=seed,
                speeds=list(speeds),
                p1=r['p1'],
                p10=r['p10'],
                ratio=r['ratio'],
                ratio_band=band,
                witness_found=r['success'],
                witness_t=r['witness_t'],
                min_isolation=r['min_isolation'],
                boundary_count=r['boundary_count'],
                max_gap_J=r['max_gap_J'],
                runtime_s=round(elapsed, 6),
                error=None,
            )
        except Exception as exc:
            elapsed = time.perf_counter() - t0
            rec = dict(
                config_id=config_id,
                config_family=family,
                seed=seed,
                speeds=list(speeds),
                p1=speeds[0],
                p10=speeds[-1],
                ratio=speeds[-1] / speeds[0],
                ratio_band=band,
                witness_found=False,
                witness_t=None,
                min_isolation=None,
                boundary_count=None,
                max_gap_J=None,
                runtime_s=round(elapsed, 6),
                error=str(exc),
            )
        records.append(rec)
    return records


# ─────────────────────────────────────────────────────────────────────────────
# Output directory helpers
# ─────────────────────────────────────────────────────────────────────────────

def _ensure_dirs(output_root: str):
    for sub in ["chunks", "checkpoints"]:
        os.makedirs(os.path.join(output_root, sub), exist_ok=True)


def _manifest_path(output_root):
    return os.path.join(output_root, "manifest.json")


def _progress_path(output_root):
    return os.path.join(output_root, "checkpoints", "progress.json")


def _chunk_path(output_root, chunk_id):
    return os.path.join(output_root, "chunks", f"chunk_{chunk_id:06d}.jsonl.gz")


def _failures_path(output_root):
    return os.path.join(output_root, "failures.jsonl.gz")


def _load_manifest(output_root):
    p = _manifest_path(output_root)
    if os.path.exists(p):
        with open(p) as f:
            return json.load(f)
    return {}


def _save_manifest(output_root, manifest):
    with open(_manifest_path(output_root), "w") as f:
        json.dump(manifest, f, indent=2)


def _load_progress(output_root):
    p = _progress_path(output_root)
    if os.path.exists(p):
        with open(p) as f:
            return json.load(f)
    return {"completed_chunk_ids": [], "configs_done": 0}


def _save_progress(output_root, progress):
    with open(_progress_path(output_root), "w") as f:
        json.dump(progress, f, indent=2)


def _write_chunk(output_root, chunk_id, records):
    path = _chunk_path(output_root, chunk_id)
    with gzip.open(path, "wt", encoding="utf-8") as f:
        for rec in records:
            f.write(json.dumps(rec) + "\n")


def _append_failures(output_root, failures):
    if not failures:
        return
    path = _failures_path(output_root)
    with gzip.open(path, "at", encoding="utf-8") as f:
        for rec in failures:
            f.write(json.dumps(rec) + "\n")


# ─────────────────────────────────────────────────────────────────────────────
# Summary generator
# ─────────────────────────────────────────────────────────────────────────────

def _generate_summary(output_root, manifest, all_records):
    total = len(all_records)
    if total == 0:
        return

    witnesses = [r for r in all_records if r.get("witness_found")]
    failures_err = [r for r in all_records if r.get("error")]
    witness_rate = len(witnesses) / total * 100 if total else 0.0

    # Per-family counts
    fam_counts = defaultdict(int)
    fam_witnesses = defaultdict(int)
    for r in all_records:
        fam = r.get("config_family", "?")
        fam_counts[fam] += 1
        if r.get("witness_found"):
            fam_witnesses[fam] += 1

    # Per-band counts
    band_counts = defaultdict(int)
    band_witnesses = defaultdict(int)
    for r in all_records:
        band = r.get("ratio_band", "?")
        band_counts[band] += 1
        if r.get("witness_found"):
            band_witnesses[band] += 1

    # Slowest configs
    slowest = sorted(all_records, key=lambda r: r.get("runtime_s", 0), reverse=True)[:20]

    # Smallest witness margin
    witness_margins = [
        (r["min_isolation"], r["config_id"], r["config_family"])
        for r in witnesses
        if r.get("min_isolation") is not None
    ]
    witness_margins.sort()

    # Top hard configs (most boundary points)
    hard = sorted(
        [r for r in all_records if r.get("boundary_count") is not None],
        key=lambda r: r["boundary_count"],
        reverse=True
    )[:20]

    # Build Markdown
    now = time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime())
    lines = [
        "# LRC Case R> Boundary Campaign — Summary",
        "",
        f"**Generated**: {now}  ",
        f"**Campaign seed**: {manifest.get('master_seed', '?')}  ",
        f"**Target configs**: {manifest.get('target_configs', '?')}  ",
        f"**Chunk size**: {manifest.get('chunk_size', '?')}  ",
        "",
        "## Results",
        "",
        f"| Metric | Value |",
        f"|---|---|",
        f"| Total configs completed | {total:,} |",
        f"| Witnesses found | {len(witnesses):,} ({witness_rate:.4f}%) |",
        f"| No witness found | {total - len(witnesses):,} |",
        f"| Error records | {len(failures_err):,} |",
        "",
        "## Per-Family Coverage",
        "",
        "| Family | Configs | Witnesses | Rate |",
        "|---|---|---|---|",
    ]
    for fam in sorted(fam_counts):
        cnt = fam_counts[fam]
        wct = fam_witnesses[fam]
        rate = wct / cnt * 100 if cnt else 0.0
        lines.append(f"| {fam} | {cnt:,} | {wct:,} | {rate:.2f}% |")

    lines += [
        "",
        "## Per-Ratio-Band Coverage",
        "",
        "| Band | Configs | Witnesses | Rate |",
        "|---|---|---|---|",
    ]
    for band in sorted(band_counts):
        cnt = band_counts[band]
        wct = band_witnesses[band]
        rate = wct / cnt * 100 if cnt else 0.0
        lines.append(f"| {band} | {cnt:,} | {wct:,} | {rate:.2f}% |")

    lines += ["", "## Smallest Witness Margins", "", "| Margin | Config ID | Family |", "|---|---|---|"]
    for margin, cid, fam in witness_margins[:20]:
        lines.append(f"| {margin:.8f} | {cid} | {fam} |")

    lines += ["", "## Slowest Configs (by runtime)", "", "| Config ID | Family | Runtime (s) | Boundary Count |", "|---|---|---|---|"]
    for r in slowest:
        lines.append(f"| {r['config_id']} | {r.get('config_family','?')} | {r.get('runtime_s',0):.4f} | {r.get('boundary_count','?')} |")

    lines += ["", "## Hardest Configs (most boundary points)", "", "| Config ID | Family | Boundary Count | Witness |", "|---|---|---|---|"]
    for r in hard:
        lines.append(f"| {r['config_id']} | {r.get('config_family','?')} | {r.get('boundary_count','?')} | {r.get('witness_found','?')} |")

    lines += [
        "",
        "## Reproducibility Note",
        "",
        "This campaign uses deterministic seeds, exact `fractions.Fraction` arithmetic,",
        "and chunked resumable execution. It is **not** part of the logical proof chain.",
        "It is a referee-facing corroboration bundle.",
        "",
        "To reproduce: re-run with the same `--seed`, `--target-configs`, and `--chunk-size`.",
    ]

    md_path = os.path.join(output_root, "summary.md")
    with open(md_path, "w") as f:
        f.write("\n".join(lines) + "\n")

    # CSV summary
    import csv as csv_mod
    csv_path = os.path.join(output_root, "summary.csv")
    if all_records:
        fieldnames = [k for k in all_records[0].keys() if k != "speeds"]
        with open(csv_path, "w", newline="") as cf:
            writer = csv_mod.DictWriter(cf, fieldnames=fieldnames, extrasaction="ignore")
            writer.writeheader()
            writer.writerows(all_records)

    return md_path, csv_path


# ─────────────────────────────────────────────────────────────────────────────
# Main campaign runner
# ─────────────────────────────────────────────────────────────────────────────

def run_campaign(args):
    output_root = os.path.abspath(args.output_root)
    _ensure_dirs(output_root)

    # Load or initialise manifest
    manifest = _load_manifest(output_root)
    if not manifest:
        manifest = dict(
            master_seed=args.seed,
            target_configs=args.target_configs,
            chunk_size=args.chunk_size,
            workers=args.workers,
            full_metrics=args.full_metrics,
            family_filter=args.family,
            created_at=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        )
        _save_manifest(output_root, manifest)
    else:
        print(f"[resume] Found existing manifest. master_seed={manifest['master_seed']}")

    # Build full config plan
    print(f"Building config plan (target={args.target_configs:,}, seed={args.seed}) …", flush=True)
    plan = build_config_plan(args.target_configs, args.seed, family_filter=args.family)
    print(f"Plan built: {len(plan):,} configs", flush=True)

    # Chunk the plan
    chunk_size = args.chunk_size
    chunks = []
    for start in range(0, len(plan), chunk_size):
        chunks.append(plan[start:start + chunk_size])
    total_chunks = len(chunks)
    print(f"Total chunks: {total_chunks:,}", flush=True)

    # Apply --max-chunks
    if args.max_chunks:
        chunks = chunks[:args.max_chunks]
        print(f"[smoke] Limiting to {len(chunks)} chunks", flush=True)

    # Load progress (resume)
    progress = _load_progress(output_root)
    completed_ids = set(progress.get("completed_chunk_ids", []))
    configs_done = progress.get("configs_done", 0)

    pending_chunk_ids = [i for i in range(len(chunks)) if i not in completed_ids]
    print(
        f"Chunks pending: {len(pending_chunk_ids)}, "
        f"already done: {len(completed_ids)}, "
        f"configs done: {configs_done:,}",
        flush=True
    )

    if not pending_chunk_ids:
        print("All chunks already complete. Regenerating summary …")
    else:
        # Run pending chunks with multiprocessing pool
        n_workers = max(1, args.workers)
        print(f"Launching {n_workers} worker(s) …", flush=True)

        campaign_start = time.perf_counter()
        processed_this_run = 0

        with multiprocessing.Pool(processes=n_workers) as pool:
            work_items = [
                (chunk_id, chunks[chunk_id], args.full_metrics)
                for chunk_id in pending_chunk_ids
            ]
            for chunk_id, records in zip(
                pending_chunk_ids,
                pool.imap_unordered(_process_chunk, work_items, chunksize=1)
            ):
                # Write chunk artifact
                _write_chunk(output_root, chunk_id, records)

                # Track failures
                fail_records = [r for r in records if r.get("error")]
                _append_failures(output_root, fail_records)

                # Update progress
                completed_ids.add(chunk_id)
                configs_done += len(records)
                processed_this_run += len(records)
                progress["completed_chunk_ids"] = sorted(completed_ids)
                progress["configs_done"] = configs_done
                progress["last_updated"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
                _save_progress(output_root, progress)

                # Print status
                elapsed = time.perf_counter() - campaign_start
                rate = processed_this_run / elapsed if elapsed > 0 else 0.0
                remaining = len(plan) - configs_done
                eta_s = remaining / rate if rate > 0 else float("inf")
                eta_str = f"{eta_s/3600:.1f}h" if eta_s < 1e9 else "?"
                print(
                    f"  chunk {chunk_id:05d} done | "
                    f"configs done: {configs_done:,}/{len(plan):,} | "
                    f"rate: {rate:.1f}/s | ETA: {eta_str}",
                    flush=True
                )

    # Generate summary from all chunk files
    print("Aggregating all chunk records for summary …", flush=True)
    all_records = []
    for chunk_id in sorted(completed_ids):
        path = _chunk_path(output_root, chunk_id)
        if os.path.exists(path):
            with gzip.open(path, "rt", encoding="utf-8") as f:
                for line in f:
                    line = line.strip()
                    if line:
                        all_records.append(json.loads(line))

    print(f"Aggregated {len(all_records):,} records. Writing summary …", flush=True)
    md_path, csv_path = _generate_summary(output_root, manifest, all_records)
    print(f"Summary: {md_path}")
    print(f"CSV:     {csv_path}")
    print("Campaign complete.")


# ─────────────────────────────────────────────────────────────────────────────
# CLI
# ─────────────────────────────────────────────────────────────────────────────

def _parse_args():
    parser = argparse.ArgumentParser(
        description="LRC Case R> boundary-set background campaign runner"
    )
    parser.add_argument("--target-configs", type=int, default=1_000_000,
                        help="Total number of configs to check (default 1,000,000)")
    parser.add_argument("--workers", type=int,
                        default=max(1, multiprocessing.cpu_count() - 4),
                        help="Number of parallel workers")
    parser.add_argument("--chunk-size", type=int, default=5_000,
                        help="Configs per chunk file (default 5,000)")
    parser.add_argument("--seed", type=int, default=20260330,
                        help="Master random seed (default 20260330)")
    parser.add_argument("--output-root", type=str,
                        default="reports/investigations/INV-CASE-R-BOUNDARY-001",
                        help="Output directory root")
    parser.add_argument("--resume", action="store_true",
                        help="Resume from existing progress checkpoint")
    parser.add_argument("--full-metrics", action="store_true",
                        help="Compute max_gap_J (slower, more data)")
    parser.add_argument("--family", type=str, default=None,
                        choices=["A", "B", "C", "P"],
                        help="Run only one config family (for debugging)")
    parser.add_argument("--max-chunks", type=int, default=None,
                        help="Stop after N chunks (smoke test)")
    return parser.parse_args()


if __name__ == "__main__":
    args = _parse_args()

    # If not resuming and output already exists with progress, warn
    progress_p = _progress_path(args.output_root)
    if not args.resume and os.path.exists(progress_p):
        print(
            f"[WARNING] {args.output_root} already has progress. "
            "Use --resume to continue, or delete the directory to start fresh."
        )
        sys.exit(1)

    run_campaign(args)
