#!/usr/bin/env python3
# v1.0 — 2026-04-15 — Benchmark MIAI ride_v37_tsp_directed on Math Ex rungs 0-1.
"""
RIDE V41 — MIAI v37 Benchmark Harness

Runs MIAI's ride_v37_tsp_directed on the Math Ex rung set (rungs 0+1 only in
this session; rungs 2/3 are next-session per source-of-truth Q8).

Per target, per run we record:
  - step count N (= v37's best_k)
  - log2(N)
  - traversal length L (upper bound on N)
  - final hash match boolean
  - wallclock seconds
  - log2(M) = log2(N! / prod(freq_i!))   — the Lehmer-rank wall from v50
  - ratio log2(N) / log2(M)

Baseline: log2(M) (the v50 information-theoretic wall). We do NOT run a raw-FY
baseline per plan (the 87% wall is already settled; raw-FY on text slices
would not add a data point the state doc needs).

v37 is deterministic (no rng_seed input), so the 3 runs per cell exist only
to measure wallclock variance. If N varies across runs for the same target,
that indicates a bug and we halt.

Output: JSONL at outputs/ride_v41_v37_benchmark_<timestamp>.jsonl
        plus a Markdown summary table.
"""
from __future__ import annotations
import os, sys, json, time, math, hashlib, statistics
from pathlib import Path
from collections import Counter
from datetime import datetime

MATH_EX = Path(__file__).resolve().parent
MIAI = Path("/Users/trentpalelei/MIAI")
if str(MIAI) not in sys.path:
    sys.path.insert(0, str(MIAI))
if str(MATH_EX) not in sys.path:
    sys.path.insert(0, str(MATH_EX))

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(50_000_000)

import ride_v37_tsp_directed as v37
from ride_v37_tsp_directed import (
    build_canonical_from_raw, rebuild_canonical, build_traversal,
    encode_packet, decode_packet,
)
from ride_v13_canterbury_recipe_bench import (
    materialize_bytes_from_decimal, leading_zero_bytes,
)


OUT_DIR = MATH_EX / "experiments" / "outputs"
OUT_DIR.mkdir(parents=True, exist_ok=True)

RUNS_PER_CELL = 3


# ──────────────────────────────────────────────────────────────────────────
# Rung fixtures
# ──────────────────────────────────────────────────────────────────────────

def load_rung0_synthetic_small() -> tuple[str, bytes]:
    # Fixed-seed synthetic bytes, reproducible across runs.
    rng = _seeded_bytes(seed=0xA17E, n=256)
    return ("rung0_synth_256B", rng)

def load_rung0_synthetic_medium() -> tuple[str, bytes]:
    rng = _seeded_bytes(seed=0xA17E, n=1024)
    return ("rung0_synth_1024B", rng)

def _seeded_bytes(seed: int, n: int) -> bytes:
    # Deterministic byte stream from a SHA256-expanded seed.
    out = bytearray()
    counter = 0
    while len(out) < n:
        out += hashlib.sha256(seed.to_bytes(8, "big") + counter.to_bytes(8, "big")).digest()
        counter += 1
    return bytes(out[:n])

def load_rung1_text_slice(slice_len: int = 3000) -> tuple[str, bytes] | None:
    # Prefer a real text file in Math Ex; fall back to alice29 if present.
    candidates = [
        MATH_EX / "alice29.txt",
        MATH_EX / "lrc_synchronized_states_summary.txt",
        MATH_EX / "prime_power_n125_log.txt",
    ]
    for p in candidates:
        if p.exists():
            raw = p.read_bytes()[:slice_len]
            return (f"rung1_text_{p.name}_{len(raw)}B", raw)
    return None


# ──────────────────────────────────────────────────────────────────────────
# Lehmer-rank wall (v50 formula)
# ──────────────────────────────────────────────────────────────────────────

def log2_multiset_permutations(digits: list[int]) -> float:
    """log2(N! / prod(freq_i!)) via lgamma."""
    N = len(digits)
    log2_M = math.lgamma(N + 1) / math.log(2)
    for cnt in Counter(digits).values():
        log2_M -= math.lgamma(cnt + 1) / math.log(2)
    return log2_M


# ──────────────────────────────────────────────────────────────────────────
# Single benchmark run
# ──────────────────────────────────────────────────────────────────────────

def run_v37_once(raw: bytes) -> dict:
    """Run v37 sender_encode + receiver_decode once. Return metrics."""
    n_raw = len(raw)
    leading_zeros = leading_zero_bytes(raw)
    target_hash = hashlib.sha256(raw).digest()

    t0 = time.time()
    v0, a, b, v9, l1, delta, patched_source = build_canonical_from_raw(raw)
    n_digits = len(patched_source)
    t_canonical = time.time() - t0

    t1 = time.time()
    swaps = build_traversal(patched_source)
    traversal_length = len(swaps)
    t_traversal = time.time() - t1

    # Search for hash match along the deterministic path.
    t2 = time.time()
    state = list(patched_source)
    step_count = -1  # -1 means not found

    # Check initial state (step 0).
    try:
        mat = materialize_bytes_from_decimal(bytearray(state), n_raw, leading_zeros)
        if hashlib.sha256(mat).digest() == target_hash:
            step_count = 0
    except (OverflowError, ValueError):
        pass

    if step_count < 0:
        for step, (i, j) in enumerate(swaps, 1):
            state[i], state[j] = state[j], state[i]
            try:
                mat = materialize_bytes_from_decimal(bytearray(state), n_raw, leading_zeros)
                if hashlib.sha256(mat).digest() == target_hash:
                    step_count = step
                    break
            except (OverflowError, ValueError):
                pass
    t_search = time.time() - t2
    wallclock = time.time() - t0

    hash_match = step_count >= 0

    # log2(M) — the v50 wall for this target's multiset.
    log2_M = log2_multiset_permutations(patched_source)

    # Round-trip verification when hash matched.
    round_trip_ok = None
    if hash_match:
        packet = encode_packet(v0, a, b, v9, delta, n_raw, leading_zeros,
                               step_count, target_hash, int(wallclock * 1000))
        try:
            from ride_v37_tsp_directed import receiver_decode
            # receiver_decode prints; capture its result.
            import io, contextlib
            with contextlib.redirect_stdout(io.StringIO()):
                decoded = receiver_decode(packet)
            round_trip_ok = (decoded == raw)
        except Exception as e:
            round_trip_ok = False

    return {
        "n_raw_bytes": n_raw,
        "n_digits": n_digits,
        "traversal_length": traversal_length,
        "step_count_N": step_count,
        "log2_N": (math.log2(step_count) if step_count > 0 else None),
        "log2_M": log2_M,
        "log2_M_over_file_bits": log2_M / (n_raw * 8) if n_raw else None,
        "ratio_log2N_over_log2M": (math.log2(step_count) / log2_M
                                    if step_count > 0 and log2_M > 0 else None),
        "hash_match": hash_match,
        "round_trip_ok": round_trip_ok,
        "t_canonical_s": t_canonical,
        "t_traversal_s": t_traversal,
        "t_search_s": t_search,
        "wallclock_s": wallclock,
    }


# ──────────────────────────────────────────────────────────────────────────
# Harness
# ──────────────────────────────────────────────────────────────────────────

def benchmark_target(target_name: str, raw: bytes, runs: int = RUNS_PER_CELL) -> list[dict]:
    print(f"\n{'─'*70}")
    print(f"  {target_name}  ({len(raw):,} bytes)")
    print(f"{'─'*70}")
    results = []
    for run_id in range(runs):
        print(f"  run {run_id+1}/{runs} ...", end=" ", flush=True)
        t0 = time.time()
        try:
            m = run_v37_once(raw)
            m["run_id"] = run_id
            m["target"] = target_name
            m["space"] = "miai_v37_tsp_directed"
            m["rng_seed"] = None
            m["theta"] = None
            m["error"] = None
            print(f"N={m['step_count_N']}  match={m['hash_match']}  "
                  f"rt={m['round_trip_ok']}  {time.time()-t0:.2f}s")
        except Exception as e:
            import traceback
            m = {
                "run_id": run_id, "target": target_name,
                "space": "miai_v37_tsp_directed",
                "rng_seed": None, "theta": None,
                "error": f"{type(e).__name__}: {e}",
                "traceback": traceback.format_exc(),
                "wallclock_s": time.time() - t0,
            }
            print(f"ERROR {type(e).__name__}: {e}")
        results.append(m)
    # Determinism check: N should be identical across runs for a given target.
    Ns = [r.get("step_count_N") for r in results if r.get("error") is None]
    if len(set(Ns)) > 1:
        print(f"  !!! NON-DETERMINISTIC: step_count_N differs across runs: {Ns}")
        print(f"  !!! This indicates a bug in v37 or the harness. Halting this target.")
    return results


def summarize(all_results: list[dict]) -> str:
    lines = [
        "# ride_v41 — MIAI v37 benchmark summary",
        f"Generated: {datetime.now().isoformat()}",
        "",
        "| target | bytes | digits | N | log2(N) | log2(M) | N/M ratio | match | round-trip | median wallclock (s) |",
        "|---|---:|---:|---:|---:|---:|---:|---|---|---:|",
    ]
    by_target: dict[str, list[dict]] = {}
    for r in all_results:
        by_target.setdefault(r["target"], []).append(r)
    for target, rs in by_target.items():
        good = [r for r in rs if r.get("error") is None]
        if not good:
            lines.append(f"| {target} | — | — | — | — | — | — | ERROR | — | — |")
            continue
        r0 = good[0]
        wallclocks = [r["wallclock_s"] for r in good]
        med = statistics.median(wallclocks)
        N = r0.get("step_count_N")
        log2N = f"{r0['log2_N']:.1f}" if r0.get("log2_N") else "—"
        log2M = f"{r0['log2_M']:.1f}" if r0.get("log2_M") else "—"
        ratio = f"{r0['ratio_log2N_over_log2M']:.3f}" if r0.get("ratio_log2N_over_log2M") else "—"
        match = "✓" if r0.get("hash_match") else "✗"
        rt = "✓" if r0.get("round_trip_ok") else ("—" if r0.get("round_trip_ok") is None else "✗")
        lines.append(f"| {target} | {r0['n_raw_bytes']:,} | {r0['n_digits']:,} | "
                     f"{N:,} | {log2N} | {log2M} | {ratio} | {match} | {rt} | {med:.3f} |")
    return "\n".join(lines) + "\n"


def main():
    targets: list[tuple[str, bytes]] = []

    # Rung 0: synthetic
    targets.append(load_rung0_synthetic_small())
    targets.append(load_rung0_synthetic_medium())

    # Rung 1: text slice
    r1 = load_rung1_text_slice(slice_len=3000)
    if r1 is None:
        print("WARNING: no rung 1 text fixture found. Skipping rung 1.")
    else:
        targets.append(r1)

    ts = datetime.now().strftime("%Y%m%dT%H%M%S")
    jsonl_path = OUT_DIR / f"ride_v41_v37_benchmark_{ts}.jsonl"
    md_path = OUT_DIR / f"ride_v41_v37_benchmark_{ts}.md"

    all_results: list[dict] = []
    with open(jsonl_path, "w") as f:
        for name, raw in targets:
            rs = benchmark_target(name, raw)
            for r in rs:
                f.write(json.dumps(r, default=str) + "\n")
                all_results.append(r)
            f.flush()

    summary = summarize(all_results)
    md_path.write_text(summary)
    print("\n" + "="*70)
    print(summary)
    print(f"JSONL: {jsonl_path}")
    print(f"MD:    {md_path}")


if __name__ == "__main__":
    main()
