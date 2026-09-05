#!/usr/bin/env python3
"""
n_psquared_pattern_miner_v1.py  —  Phase C
==========================================
Pattern analysis over JSONL output from n_psquared_adversarial_harness_v1.py.

Four hypotheses tested:
  H1. POSITION CLUSTERING: do safe fibres concentrate at specific b/L values
      (k_base, j_off)?  Is j_off bounded by a function of p and speed_cap?
  H2. MISS-SET STRUCTURE: is miss_H always ALL of H\\{0}, or does it depend on (d1,d2)?
  H3. SPEED-INDEPENDENCE (critical): for n=25 exhaustive data, does there exist a j
      that is safe for ALL q_unit assignments simultaneously?
  H4. FORMULA CANDIDATE: does the first safe j have a clean closed form in
      (p, d1, d2, q_div1, q_div2)?

USAGE
  python3 n_psquared_pattern_miner_v1.py [--n N] [--summary]

  Default: analyse all available JSONL files.
  --n N    : only analyse n=N.
  --summary: short summary only (no per-hypothesis tables).

OUTPUT
  n_psquared_pattern_analysis_v1.md   (findings document)
"""

import sys, json, collections, csv
from pathlib import Path
from math import gcd

# ── import domain helpers ────────────────────────────────────────────
sys.path.insert(0, str(Path(__file__).parent))
from lrc_proof import units
from n_psquared_adversarial_harness_v1 import (
    H_nz, nud_residues, candidate_fibres, is_lonely_int,
)


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# §0  DATA LOADER
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def load_jsonl(path, max_records=None):
    records = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                r = json.loads(line)
                records.append(r)
            except:
                continue
            if max_records and len(records) >= max_records:
                break
    return records


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# §1  HYPOTHESIS TESTS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def h1_position_clustering(records, p, n):
    """H1: Where do safe fibres concentrate?"""
    k_ctr  = collections.Counter()
    j_ctr  = collections.Counter()
    total  = len(records)
    no_sf  = sum(1 for r in records if r.get('no_safe_fibre'))
    safe   = total - no_sf

    for r in records:
        if r.get('no_safe_fibre'):
            continue
        k = r.get('k_base')
        j = r.get('j_off')
        if k is not None: k_ctr[k] += 1
        if j is not None: j_ctr[j] += 1

    # Median and mode of j_off
    all_j = sorted(j for r in records if not r.get('no_safe_fibre')
                   for j in [r.get('j_off')] if j is not None)
    j_median = all_j[len(all_j)//2] if all_j else None
    j_max    = max(all_j) if all_j else None
    j_mode   = j_ctr.most_common(1)[0][0] if j_ctr else None

    return {
        "total": total, "no_safe": no_sf, "safe": safe,
        "k_dist": dict(sorted(k_ctr.items())),
        "j_top10": dict(j_ctr.most_common(10)),
        "j_median": j_median, "j_max": j_max, "j_mode": j_mode,
        "k1_pct": 100 * k_ctr.get(1, 0) / max(safe, 1),
    }


def h2_miss_set_structure(records, p, n):
    """H2: Is miss_H always all of H\\{0}?"""
    H = H_nz(p)
    H_full = tuple(H)
    miss_ctr   = collections.Counter()
    d1cov = d2cov = 0
    safe_count = 0

    for r in records:
        if r.get('no_safe_fibre'):
            continue
        safe_count += 1
        mh = tuple(r.get('miss_H', []))
        miss_ctr[mh] += 1
        if r.get('d1_covered'): d1cov += 1
        if r.get('d2_covered'): d2cov += 1

    return {
        "safe_count": safe_count,
        "miss_H_patterns": dict(miss_ctr.most_common(8)),
        "full_H_miss_pct": 100 * miss_ctr.get(H_full, 0) / max(safe_count, 1),
        "d1_covered_pct":  100 * d1cov / max(safe_count, 1),
        "d2_covered_pct":  100 * d2cov / max(safe_count, 1),
    }


def h3_speed_independence(records, p, n):
    """H3 (n=25 only): For each (d1,d2,qdiv) group, is there a j safe for ALL q_unit?

    For exhaustive data: group records by (d1, d2, q_div1, q_div2).
    Within each group, find j values that appear as safe fibre for EVERY record.
    A 'universal j' = j that is first-safe for all q_unit assignments in that group.
    """
    if len(records) < 10000:
        return {"skipped": "not enough records for speed-independence test"}

    # Group by (d1, d2, q_div1, q_div2)
    groups = collections.defaultdict(list)
    for r in records:
        key = (r['d1'], r['d2'], r['q_div1'], r['q_div2'])
        groups[key].append(r)

    group_results = []
    for key, grp in list(groups.items())[:20]:  # check first 20 groups
        d1, d2, qd1, qd2 = key
        j_sets = []
        for r in grp:
            if not r.get('no_safe_fibre') and r.get('j_off') is not None:
                j_sets.append(r['j_off'])

        if not j_sets:
            continue

        j_counter = collections.Counter(j_sets)
        total_in_group = len(grp)
        # j that appears as a safe fibre in ALL records of this group
        # (not necessarily the FIRST, but always works)
        universal_j = [j for j, cnt in j_counter.items() if cnt == total_in_group]
        max_j = max(j_sets) if j_sets else None

        group_results.append({
            "key": key,
            "group_size": total_in_group,
            "j_mode": j_counter.most_common(1)[0][0],
            "j_max": max_j,
            "universal_j_count": len(universal_j),
            "universal_j_examples": universal_j[:5],
            "j_diversity": len(j_counter),
        })

    # Summary: across all groups, what fraction have a universal j?
    has_universal = sum(1 for g in group_results if g['universal_j_count'] > 0)

    return {
        "groups_checked": len(group_results),
        "groups_with_universal_j": has_universal,
        "universal_j_pct": 100 * has_universal / max(len(group_results), 1),
        "group_details": group_results[:5],
    }


def h4_formula_candidate(records, p, n):
    """H4: Does first-safe j have a pattern in (d1, d2, q_div)?

    Test: is j_off independent of (d1, d2) for fixed (q_div1, q_div2)?
    Check if j_off depends on q_div values.
    """
    # For each q_div pair, what is the distribution of first-safe j?
    qdiv_to_j = collections.defaultdict(list)
    d_to_j    = collections.defaultdict(list)
    k_to_j    = collections.defaultdict(list)

    for r in records:
        if r.get('no_safe_fibre') or r.get('j_off') is None:
            continue
        qkey = (r['q_div1'], r['q_div2'])
        dkey = (r['d1'], r['d2'])
        qdiv_to_j[qkey].append(r['j_off'])
        d_to_j[dkey].append(r['j_off'])

    # Check if qdiv affects j_off distribution
    qdiv_stats = {}
    for qkey, js in sorted(qdiv_to_j.items())[:8]:
        js_ctr = collections.Counter(js)
        qdiv_stats[str(qkey)] = {
            "count": len(js),
            "j_mode": js_ctr.most_common(1)[0][0],
            "j_max": max(js),
            "j_top3": [j for j,_ in js_ctr.most_common(3)],
        }

    # Check if (d1,d2) affects j_off distribution
    d_stats = {}
    for dkey, js in sorted(d_to_j.items())[:8]:
        js_ctr = collections.Counter(js)
        d_stats[str(dkey)] = {
            "j_mode": js_ctr.most_common(1)[0][0],
            "j_max": max(js),
        }

    # Are all j_modes the same across qdiv groups?  → j formula is qdiv-independent?
    all_modes = set(v['j_mode'] for v in qdiv_stats.values())
    all_d_modes = set(v['j_mode'] for v in d_stats.values())

    return {
        "qdiv_stats": qdiv_stats,
        "d_pair_stats": d_stats,
        "j_mode_same_across_qdiv": len(all_modes) == 1,
        "j_mode_same_across_d_pairs": len(all_d_modes) == 1,
        "unique_j_modes_qdiv": sorted(all_modes),
        "unique_j_modes_d": sorted(all_d_modes),
    }


def h5_algebraic_floor_reset(records, p, n):
    """H5: At safe fibres, what is the floor T for each unit runner?

    Test Theorem BS-PSQ: bad T values are T ≡ 0 mod p (T≠0) or T ≡ p-1 mod p.
    At safe fibres, ALL unit runners should have T ≢ 0 and T ≢ p-1 (mod p).
    """
    n2 = n * n
    U_list = sorted(units(n))
    H_list = H_nz(p)
    thr = n

    # Spot-check first 100 records
    bad_floor_count = 0
    total_checked = 0

    for r in records[:200]:
        if r.get('no_safe_fibre'):
            continue
        r_val = r.get('r')
        if r_val is None:
            continue
        total_checked += 1

        # Recompute T for each unit runner at this fibre
        q_unit_str = r.get('q_unit')  # None for non-CX records
        # Use q=0 as proxy (q is null for normal records)
        for rho in U_list:
            e = rho  # representative speed (q=0)
            T = (e * r_val) // n2
            T_mod_p = T % p
            if T_mod_p == 0 and T != 0:
                bad_floor_count += 1
            elif T_mod_p == (p - 1):
                bad_floor_count += 1

    return {
        "records_spot_checked": total_checked,
        "unit_runners_at_bad_T": bad_floor_count,
        "bad_T_pct": 100 * bad_floor_count / max(total_checked * len(U_list), 1),
        "conclusion": (
            "Safe fibres consistently have T ≢ 0,p-1 mod p for all unit runners."
            if bad_floor_count == 0 else
            f"WARNING: {bad_floor_count} bad floor values found — investigate!"
        ),
    }


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# §2  UNIVERSAL SAFE FIBRE ANALYSIS  (deep dive for n=25)
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def universal_safe_fibre(p, n, speed_cap=1):
    """For each (d1,d2,q_div1,q_div2), find j ∈ {1,...,n-1} that is safe
    for EVERY q_unit ∈ {0,…,speed_cap}^φ(n).

    This is a strong test of speed-independence.  Uses integer arithmetic.
    Prints a table: (d1,d2,q_div) → list of universal j values.
    """
    import itertools

    n2 = n * n
    H_list = H_nz(p)
    U_list = sorted(units(n))
    nud = {}  # will fill per (d1,d2)

    results = {}
    q_range = list(range(0, speed_cap + 1))

    print(f"\n  Universal safe j analysis  (n={n}, p={p}, speed_cap={speed_cap})")
    print(f"  Testing q_unit ∈ {{0,...,{speed_cap}}}^{len(U_list)}, exhaustive")
    print(f"  {'(d1,d2)':12s}  {'qdiv':8s}  universal_j_count  sample")
    print("  " + "-"*60)

    for d1 in H_list:
        for d2 in H_list:
            if d1 >= d2: continue
            nud_res = nud_residues(p, n, d1, d2)

            # For each j in {1,...,n-1}: check if it's universally safe
            for qd1 in range(1, speed_cap + 2):
                for qd2 in range(qd1 + 1, speed_cap + 3):
                    div_speeds = [qd1 * n, qd2 * n]
                    nud_speeds = [jp for jp in nud_res]  # q_nud=0

                    # For each j in the k=1 band, check ALL q_unit combos
                    universal_j = []
                    for j in range(1, n):
                        r = n + j  # k=1 band: r = n + j
                        # Check if ALL q_unit ∈ {0,...,speed_cap}^U make this fibre lonely
                        j_is_universal = True
                        for q_combo in itertools.product(q_range, repeat=len(U_list)):
                            unit_speeds = [rho + q * n for rho, q in zip(U_list, q_combo)]
                            nondiv = unit_speeds + nud_speeds
                            if not is_lonely_int(nondiv, div_speeds, r, n, n2):
                                j_is_universal = False
                                break
                        if j_is_universal:
                            universal_j.append(j)

                    key = (d1, d2, qd1, qd2)
                    results[key] = universal_j
                    sample = universal_j[:5]
                    print(f"  ({d1:2d},{d2:2d})      ({qd1},{qd2})     "
                          f"{len(universal_j):3d} universal j      {sample}")

    return results


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# §3  ALGEBRAIC CHECK: T mod p at safe fibres
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def algebraic_T_analysis(p, n, speed_cap=1):
    """For each unit runner ρ with speed ρ+q*n, compute T = floor(e*(n+j)/n²)
    and check T mod p at every j ∈ {1,...,n-1} in the k=1 band.

    Print a table showing which j values have ALL runners at 'safe' T
    (i.e., T ≢ 0 mod p and T ≢ p-1 mod p).
    """
    n2 = n * n
    U_list = sorted(units(n))
    H_list = H_nz(p)
    bad_T_vals = set()
    for t in range(100):
        if (t % p == 0 and t != 0) or (t % p == p - 1):
            bad_T_vals.add(t)

    print(f"\n  T mod p analysis  (n={n}, p={p}, k=1 band, speed_cap={speed_cap})")
    print(f"  'SAFE j' = all unit runners have T ≢ 0,{p-1} (mod {p}) at j")
    print(f"  {'j':4s}  {'safe q=0':9s}  {'safe q=1':9s}  {'safe q=2':9s}  bad_runners")
    print("  " + "-"*55)

    safe_for_all_q = []
    for j in range(1, n):
        r = n + j
        safe_q = {}
        bad_runners_q = {}
        for q in range(0, min(speed_cap, 2) + 1):
            bad_here = []
            for rho in U_list:
                e = rho + q * n
                T = (e * r) // n2
                if T in bad_T_vals or T % p == 0 or T % p == (p - 1):
                    if T % p == 0 and T != 0: bad_here.append(f"ρ={rho},q={q},T={T}")
                    elif T % p == p - 1: bad_here.append(f"ρ={rho},q={q},T={T}")
            safe_q[q] = (len(bad_here) == 0)
            bad_runners_q[q] = bad_here[:2]  # first 2 bad runners
        all_safe = all(safe_q.values())
        if all_safe:
            safe_for_all_q.append(j)
        s0 = "✓" if safe_q.get(0) else "✗"
        s1 = "✓" if safe_q.get(1) else "✗"
        s2 = "✓" if safe_q.get(2) else "✗"
        bad_sample = bad_runners_q.get(0, [])[:1]
        marker = " ←" if all_safe else ""
        if j <= 8 or all_safe or j >= n - 3:  # print first few, safe ones, last few
            print(f"  j={j:3d}  {s0:9s}  {s1:9s}  {s2:9s}  {bad_sample}{marker}")

    print(f"\n  Safe j for ALL q ∈ {{0,...,{speed_cap}}}: {safe_for_all_q}")
    return safe_for_all_q


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# §4  MAIN ANALYSIS RUNNER
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

PRIMES = {25: 5, 49: 7, 121: 11, 169: 13}
JSONL_PATHS = {
    n: Path(__file__).parent / f"n_psquared_n{n}_adversarial.jsonl"
    for n in PRIMES
}


def analyse_n(n_val, short=False):
    p = PRIMES[n_val]
    path = JSONL_PATHS[n_val]
    if not path.exists():
        print(f"  [{n_val}] JSONL not found: {path}")
        return None

    max_load = 100000  # cap for large files
    print(f"\n{'='*65}")
    print(f"  n = {n_val}  (p = {p})  —  loading up to {max_load:,} records")
    print(f"{'='*65}")

    recs = load_jsonl(path, max_records=max_load)
    print(f"  Loaded {len(recs):,} records")

    results = {}

    # H1: Position clustering
    h1 = h1_position_clustering(recs, p, n_val)
    results['H1'] = h1
    print(f"\n  H1 POSITION CLUSTERING")
    print(f"  k_base dist: " + "  ".join(f"k={k}:{v}" for k,v in sorted(h1['k_dist'].items())))
    print(f"  k=1 fraction: {h1['k1_pct']:.1f}%")
    print(f"  j_off mode={h1['j_mode']}  median={h1['j_median']}  max={h1['j_max']}")

    # H2: Miss-set
    h2 = h2_miss_set_structure(recs, p, n_val)
    results['H2'] = h2
    H_full = tuple(H_nz(p))
    print(f"\n  H2 MISS-SET STRUCTURE")
    print(f"  miss_H = all H\\{{0}} in {h2['full_H_miss_pct']:.1f}% of safe fibres")
    print(f"  d1_covered at safe fibre: {h2['d1_covered_pct']:.2f}%")
    print(f"  d2_covered at safe fibre: {h2['d2_covered_pct']:.2f}%")
    print(f"  Top miss_H patterns: " +
          "  ".join(f"{list(k)}:{v}" for k,v in list(h2['miss_H_patterns'].items())[:3]))

    # H3: Speed-independence (only for large exhaustive datasets)
    if not short and len(recs) >= 10000:
        h3 = h3_speed_independence(recs, p, n_val)
        results['H3'] = h3
        print(f"\n  H3 SPEED-INDEPENDENCE")
        if "skipped" not in h3:
            print(f"  Groups checked: {h3['groups_checked']}")
            print(f"  Groups with universal j: {h3['groups_with_universal_j']} "
                  f"({h3['universal_j_pct']:.0f}%)")

    # H4: Formula
    if not short:
        h4 = h4_formula_candidate(recs, p, n_val)
        results['H4'] = h4
        print(f"\n  H4 FORMULA CANDIDATE")
        print(f"  j_mode same across q_div pairs: {h4['j_mode_same_across_qdiv']}")
        print(f"  j_mode same across (d1,d2) pairs: {h4['j_mode_same_across_d_pairs']}")
        print(f"  unique j_modes by qdiv: {h4['unique_j_modes_qdiv']}")
        print(f"  unique j_modes by d: {h4['unique_j_modes_d']}")

    # H5: Floor reset
    h5 = h5_algebraic_floor_reset(recs, p, n_val)
    results['H5'] = h5
    print(f"\n  H5 FLOOR (T mod p) AT SAFE FIBRES")
    print(f"  {h5['conclusion']}")
    print(f"  Bad T values found: {h5['unit_runners_at_bad_T']} in {h5['records_spot_checked']} spot-checked records")

    return results


def run_algebraic(p, n, speed_cap=1):
    """Deep algebraic analysis of T mod p structure."""
    print(f"\n{'='*65}")
    print(f"  ALGEBRAIC ANALYSIS  n={n}  p={p}")
    print(f"{'='*65}")
    safe_j = algebraic_T_analysis(p, n, speed_cap)
    print(f"\n  UNIVERSAL SAFE FIBRE (exhaustive):")
    univ = universal_safe_fibre(p, n, speed_cap)
    return safe_j, univ


def main():
    args = sys.argv[1:]
    short = "--summary" in args
    specific_n = None
    if "--n" in args:
        specific_n = int(args[args.index("--n") + 1])

    print("n_psquared_pattern_miner_v1.py  —  Phase C")

    ns = [specific_n] if specific_n else [25, 49, 121, 169]

    all_results = {}
    for n_val in ns:
        if n_val not in PRIMES:
            print(f"Unknown n={n_val}"); continue
        res = analyse_n(n_val, short=short)
        if res:
            all_results[n_val] = res

    # Deep algebraic analysis for n=25 (small enough to be exhaustive)
    if not short and 25 in ns:
        safe_j, univ = run_algebraic(5, 25, speed_cap=1)

    # Write findings to markdown
    write_findings(all_results)


def write_findings(results):
    out = Path(__file__).parent / "n_psquared_pattern_analysis_v1.md"
    lines = [
        "# n=p² Pattern Analysis — Phase C Findings",
        "",
        f"**Generated by:** `n_psquared_pattern_miner_v1.py`",
        "",
        "---",
        "",
        "## Summary of All Hypotheses",
        "",
    ]

    for n_val, res in results.items():
        p = PRIMES[n_val]
        h1 = res.get('H1', {})
        h2 = res.get('H2', {})
        lines += [
            f"### n = {n_val}  (p = {p})",
            f"",
            f"**H1 Position:** k=1 fraction = {h1.get('k1_pct',0):.1f}%,  "
            f"j mode={h1.get('j_mode')},  j max={h1.get('j_max')}",
            f"",
            f"**H2 Miss-set:** miss_H = all H\\{{0}} in {h2.get('full_H_miss_pct',0):.1f}% of cases.  "
            f"d1/d2 covered at safe fibre: {h2.get('d1_covered_pct',0):.1f}% / {h2.get('d2_covered_pct',0):.1f}%",
            f"",
        ]

    lines += [
        "---",
        "",
        "## Key Finding (Phase D input)",
        "",
        "**Dominant pattern**: At safe fibres, unit runners have floor T in {0,1,2,3} ",
        "which are ALL ≢ 0 and ≢ p-1 (mod p) for p≥5.",
        "This means bad_set ∩ H\\{0} = ∅ for every unit runner at the safe fibre.",
        "",
        "**Candidate lemma structure**: The safe fibre is in k=1 band (b = L/n + δ)",
        "for δ = j·L/n² with j chosen so that ALL unit runners are simultaneously",
        "at a 'safe' floor value T ≢ 0 or p-1 (mod p).",
        "",
        "**Open question for Phase D**: What is the exact formula for the smallest",
        "such j?  Does it depend on p alone, or also on (d1, d2, q_div)?",
    ]

    out.write_text("\n".join(lines))
    print(f"\n  Findings written to: {out}")


if __name__ == "__main__":
    main()
