#!/usr/bin/env python3
"""
n_psquared_adversarial_harness_v1.py  —  Phase B
=================================================
Empirical adversarial harness for n = p² open case.

CONFIGURATION  (exactly n = p² runners total)
──────────────────────────────────────────────
  Runner 0       : speed 0 (stationary)
  Unit runners   : one per ρ ∈ U(p²),  φ(p²) = p(p-1) runners
                   actual speed = ρ + q_ρ · p²   (q_ρ ≥ 0)
  NUD runners    : speeds jp for j ∈ {1,…,p-1} \ {d₁/p, d₂/p}  → p-3 runners
                   actual speed = jp + q_j · p²  (q_j ≥ 0)
  Divisible (×2) : speeds q₁·p², q₂·p²   (q₁ < q₂, both ≥ 1)

  Count: 1 + p(p-1) + (p-3) + 2 = p²  ✓   threshold = 1/p²

"Dropped" residues d₁, d₂ ∈ H\{0}: no runner has residue ≡ d₁ or d₂ mod p².

PERFORMANCE
───────────
  Grid: r / n²  for r ∈ candidates (off-integer fibres, k ∈ {1,…,p-1})
  Loneliness threshold: integer n (exact, since denom = n²)
  Hot path: pure Python int arithmetic — no Fraction, no LCM.
  Speed: ~50 000 tuples/s for n=25, exhaustive q_unit ∈ {0,1}^{φ(p²)}.

USAGE
  python3 n_psquared_adversarial_harness_v1.py [--quick] [--n N] [--verbose]
  --quick    n=25 only, speed_cap=1  (~2 min)
  --n N      only this n
  --verbose  per-tuple prints

OUTPUT
  n_psquared_n{N}_adversarial.jsonl      (compact per-tuple records)
  prime_power_n{N}_actual_speeds.csv     (summary)
"""

import sys, json, csv, time, random, itertools
from fractions import Fraction
from math import gcd, isqrt
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from lrc_proof import units, mod_inv, bad_set_unit

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# §0  DOMAIN OBJECTS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def H_nz(p):
    """H\{0} = {p, 2p, …, (p-1)p}  (sorted list)."""
    return [j * p for j in range(1, p)]

def nud_residues(p, n, d1, d2):
    """H\{0, d1, d2} — residues for non-unit non-div (NUD) runners."""
    return sorted(jp for jp in H_nz(p) if jp not in (d1, d2))


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# §1  INTEGER-ARITHMETIC LONELINESS  (hot path — no Fraction)
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# Fibre is r / n²   (fraction of the period).
# Position of runner with speed s:
#     pos_int = (s * r) % n²          (in {0, …, n²-1})
#     dist_int = min(pos_int, n²-pos_int)
#     threshold_int = n   (= n² / n)
# Lonely iff all non-zero runners have dist_int ≥ n.
#
# Divisible runner (speed q·n) at off-integer fibre r = k·n + j  (j ≠ 0):
#     pos_int = (q·n·r) % n² = n·(q·j % n)
#     dist_int = n · min(q·j%n,  n - q·j%n)  ≥ n   iff  q·j ≢ 0  (mod n)
# For q < p, this holds for ALL j ∈ {1,…,n-1}. Safe to skip div runner checks
# when q_div < p. We check them anyway for safety (cheap given early exit).

def _dist_int(s, r, n2):
    """Integer circular distance of runner s at fibre r/n²."""
    pos = (s * r) % n2
    return pos if pos + pos <= n2 else n2 - pos

def is_lonely_int(nondiv_speeds, div_speeds, r, n, n2):
    """Fast loneliness check at fibre r / n².  Returns bool."""
    thr = n
    for s in nondiv_speeds:
        d = (s * r) % n2
        if d + d > n2:
            d = n2 - d
        if d < thr:
            return False
    for s in div_speeds:
        d = (s * r) % n2
        if d + d > n2:
            d = n2 - d
        if d < thr:
            return False
    return True


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# §2  CANDIDATE FIBRES  (off-integer, k ∈ {1,…,p-1})
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def candidate_fibres(p, n):
    """Off-integer fibres r ∈ {k·n + j : k∈{1,…,p-1}, j∈{1,…,n-1}}.

    denom = n².  Threshold = n.  Only the candidate-safe zone.
    """
    fibres = []
    for k in range(1, p):
        for j in range(1, n):
            fibres.append(k * n + j)
    return fibres


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# §3  PER-TUPLE ANALYSIS  (compact — no Fraction in hot path)
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def analyse_tuple(p, n, n2, d1, d2, q_unit, q_nud, q_div1, q_div2,
                  fibres, U_list, H_nz_list, verbose=False):
    """Analyse one adversarial tuple.  Returns compact record dict."""

    # Build speed lists (two categories for hot path)
    nondiv = []
    for rho in U_list:
        nondiv.append(rho + q_unit[rho] * n)
    for jp in nud_residues(p, n, d1, d2):
        nondiv.append(jp + q_nud.get(jp, 0) * n)

    div_speeds = [q_div1 * n, q_div2 * n]

    # Search candidate fibres
    first_safe_r = None
    for r in fibres:
        if is_lonely_int(nondiv, div_speeds, r, n, n2):
            first_safe_r = r
            break

    no_safe = first_safe_r is None

    # Characterise first safe fibre (for pattern mining)
    sf_info = {}
    if first_safe_r is not None:
        r = first_safe_r
        k_base = r // n       # = floor(r / n)   ∈ {1,…,p-1}
        j_off  = r %  n       # = fractional offset j ∈ {1,…,n-1}
        # Unit runner bad-sets (using floor T_ρ = floor(ρ_act * r / n²))
        unit_covered = set()
        for rho in U_list:
            e = rho + q_unit[rho] * n
            T = (e * r) // n2          # floor(e * r / n²) exactly
            bs = bad_set_unit(rho, T, n)
            unit_covered |= bs
        miss_H = [x for x in H_nz_list if x not in unit_covered]
        sf_info = {
            "r": r, "k_base": k_base, "j_off": j_off,
            "b_frac_num": r, "b_frac_den": n2,
            "b_float": r / n2,
            "d1_covered": d1 in unit_covered,
            "d2_covered": d2 in unit_covered,
            "miss_H": miss_H,
        }

    if verbose:
        flag = " <<< POTENTIAL CX" if no_safe else ""
        k = sf_info.get("k_base", "?")
        j = sf_info.get("j_off", "?")
        print(f"  d1={d1} d2={d2} qdiv=({q_div1},{q_div2}) "
              f"first_safe: k={k} j={j}{flag}")

    # Potential counterexample = no safe fibre found in candidate grid.
    # (Not definitive: might need wider fibre search.  Flag for investigation.)
    return {
        "n": n, "p": p, "d1": d1, "d2": d2,
        "q_div1": q_div1, "q_div2": q_div2,
        "no_safe_fibre": no_safe,
        **sf_info,
        # Full q_unit only stored for potential CX (keeps normal records tiny)
        "q_unit": ({str(k): v for k, v in q_unit.items()} if no_safe else None),
    }


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# §4  TUPLE GENERATOR
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def gen_tuples(p, n, speed_cap, mode="exhaustive", rng=None, max_random=3000):
    """Yield (d1, d2, q_unit, q_nud, q_div1, q_div2) tuples."""
    H = H_nz(p)
    U = sorted(units(n))
    d_pairs = [(a, b) for a in H for b in H if a < b]

    if mode == "exhaustive":
        # q_div1 < q_div2 (distinct divisible speeds)
        q_div_pairs = [(a, b) for a in range(1, speed_cap + 1)
                               for b in range(a + 1, speed_cap + 2)]
        q_unit_vals = list(range(0, min(speed_cap, 2) + 1))

        for d1, d2 in d_pairs:
            nud = nud_residues(p, n, d1, d2)
            for qd1, qd2 in q_div_pairs:
                for q_combo in itertools.product(q_unit_vals, repeat=len(U)):
                    q_unit = dict(zip(U, q_combo))
                    q_nud  = {jp: 0 for jp in nud}
                    yield d1, d2, q_unit, q_nud, qd1, qd2

    elif mode == "random":
        count = 0
        while count < max_random:
            d1, d2 = sorted(rng.sample(H, 2))
            nud = nud_residues(p, n, d1, d2)
            qd1, qd2 = sorted(rng.sample(range(1, speed_cap + 2), 2))
            q_unit = {rho: rng.randint(0, speed_cap) for rho in U}
            q_nud  = {jp: rng.randint(0, speed_cap) for jp in nud}
            yield d1, d2, q_unit, q_nud, qd1, qd2
            count += 1


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# §5  PER-n RUNNER
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

CONFIG = {
    # n=25: φ(25)=20, exhaustive q∈{0,1,2}^20 is ~3.5B — use random
    25:  {"p": 5,  "speed_cap": 3, "mode": "random",  "max_random": 50000},
    49:  {"p": 7,  "speed_cap": 3, "mode": "random",  "max_random": 30000},
    121: {"p": 11, "speed_cap": 2, "mode": "random",  "max_random": 10000},
    169: {"p": 13, "speed_cap": 2, "mode": "random",  "max_random": 10000},
}
QUICK_CONFIG = {
    # φ(25)=20: exhaustive {0,1}^20 = 1M × 6 d-pairs × 1 div-pair = 6.3M ✓
    25: {"p": 5, "speed_cap": 1, "mode": "exhaustive", "max_random": None},
}


def run_n(n_val, cfg, out_dir, verbose=False):
    p          = cfg["p"]
    speed_cap  = cfg["speed_cap"]
    mode       = cfg["mode"]
    max_random = cfg.get("max_random")

    n2 = n_val * n_val
    U_list   = sorted(units(n_val))
    H_list   = H_nz(p)
    fibres   = candidate_fibres(p, n_val)
    n_fibres = len(fibres)

    print(f"\n{'='*62}")
    print(f"  n={n_val}  p={p}  mode={mode}  speed_cap={speed_cap}")
    print(f"  candidate fibres: {n_fibres}  "
          f"(k∈{{1,…,{p-1}}}, j∈{{1,…,{n_val-1}}})")
    print(f"  threshold_int = n = {n_val},  denom = n² = {n2}")
    print(f"{'='*62}")

    jsonl_path = out_dir / f"n_psquared_n{n_val}_adversarial.jsonl"
    csv_path   = out_dir / f"prime_power_n{n_val}_actual_speeds.csv"

    rng = random.Random(42)
    total = 0
    potential_cx = 0
    csv_rows = []
    t0 = time.time()

    with open(jsonl_path, "w") as jf:
        gen = gen_tuples(p, n_val, speed_cap, mode=mode, rng=rng,
                         max_random=max_random or 1000)
        for d1, d2, q_unit, q_nud, qd1, qd2 in gen:
            rec = analyse_tuple(
                p, n_val, n2, d1, d2, q_unit, q_nud, qd1, qd2,
                fibres, U_list, H_list, verbose=verbose,
            )
            jf.write(json.dumps(rec) + "\n")
            total += 1

            if rec["no_safe_fibre"]:
                potential_cx += 1
                print(f"\n  *** POTENTIAL CX: no safe fibre in candidate grid ***")
                print(f"  n={n_val} d1={d1} d2={d2} qd=({qd1},{qd2})")
                print(f"  q_unit sample: {dict(list(q_unit.items())[:6])}…")
                print(f"  → Check wider k range or increase speed_cap.\n")

            csv_rows.append({
                "n": n_val, "p": p, "d1": d1, "d2": d2,
                "q_div1": qd1, "q_div2": qd2,
                "no_safe_fibre": rec["no_safe_fibre"],
                "sf_k_base": rec.get("k_base"),
                "sf_j_off":  rec.get("j_off"),
                "sf_b_float": rec.get("b_float"),
                "sf_d1_covered": rec.get("d1_covered"),
                "sf_d2_covered": rec.get("d2_covered"),
                "sf_miss_H":    str(rec.get("miss_H", [])),
            })

            if total % 500 == 0:
                elapsed = time.time() - t0
                rate = total / elapsed if elapsed > 0 else 0
                print(f"  {total:8d} tuples  ({rate:,.0f}/s)  "
                      f"potential_cx={potential_cx}", flush=True)

    if csv_rows:
        with open(csv_path, "w", newline="") as cf:
            w = csv.DictWriter(cf, fieldnames=list(csv_rows[0].keys()))
            w.writeheader()
            w.writerows(csv_rows)

    elapsed = time.time() - t0
    print(f"\n  SUMMARY  n={n_val}")
    print(f"  Tuples tested    : {total:,}")
    print(f"  Potential CX     : {potential_cx}"
          f"  ({'✅ none' if potential_cx == 0 else '⚠  INVESTIGATE'})")
    print(f"  Time             : {elapsed:.1f}s")
    print(f"  JSONL            : {jsonl_path}")
    print(f"  CSV              : {csv_path}")
    return {"n": n_val, "total": total, "cx": potential_cx, "elapsed": elapsed}


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# §6  MAIN
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def main():
    args       = sys.argv[1:]
    quick      = "--quick"   in args
    verbose    = "--verbose" in args
    specific_n = None
    if "--n" in args:
        specific_n = int(args[args.index("--n") + 1])

    out_dir = Path(__file__).parent
    config  = QUICK_CONFIG if quick else CONFIG
    if specific_n is not None:
        config = {specific_n: config[specific_n]}

    print("n_psquared_adversarial_harness_v1.py  —  Phase B")
    print(f"Mode: {'QUICK' if quick else 'FULL'}  |  "
          f"n ∈ {list(config.keys())}")

    summaries = []
    for n_val, cfg in config.items():
        s = run_n(n_val, cfg, Path(out_dir), verbose=verbose)
        summaries.append(s)

    print("\n" + "="*62)
    print("OVERALL SUMMARY")
    total_cx = sum(s["cx"]    for s in summaries)
    total_t  = sum(s["total"] for s in summaries)
    for s in summaries:
        flag = "✅" if s["cx"] == 0 else f"⚠  {s['cx']} potential CX"
        print(f"  n={s['n']:3d}  {s['total']:>8,} tuples  {flag}  ({s['elapsed']:.1f}s)")
    print(f"\n  Grand total: {total_t:,} tuples, {total_cx} potential CX")
    if total_cx == 0:
        print("  ✅ Zero potential counterexamples.")
        print("     Proceed to Phase C: pattern miner over JSONL.")
    else:
        print("  ⚠  Investigate potential CX before Phase C.")


if __name__ == "__main__":
    main()
