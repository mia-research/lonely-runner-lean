#!/usr/bin/env python3
"""verify_tie_handling_v1.py -- re-rank v1 Probe B-inv with mid-rank tie handling.

The v1 ranking used strict inequality (abs(null) < abs(obs)), which is biased
toward rank=0 for discrete-valued statistics at small L. This script re-computes
the Probe B d^{-1} involution autocorrelation ranks with proper mid-rank tie handling:

    rank = count(|T_null| < |T_obs|) + count(|T_null| == |T_obs|) // 2

and compares to the strict-inequality ranks from the original run.

EXACT-INTEGER signal path.  Float nowhere.
"""
import random, math                                                   # noqa: float  (math for gcd only)
import mu3_subspace_residual_v1 as M

R = 3000  # match v1

def midrank(obs_abs, null_abs_list):
    """Mid-rank: strict-less count + half the ties."""
    strict_less = sum(1 for t in null_abs_list if t < obs_abs)
    ties = sum(1 for t in null_abs_list if t == obs_abs)
    return strict_less + ties // 2

def strict_rank(obs_abs, null_abs_list):
    """Original strict-inequality rank."""
    return sum(1 for t in null_abs_list if t < obs_abs)

def run_prime(p):
    q6 = M.build_q6(p)
    if q6 is None or q6["L"] < 4:
        return None
    n = q6["n"]; m = q6["m"]; L = q6["L"]; u = q6["u"]
    reps = q6["reps"]; d2i = q6["d_to_q6idx"]

    iota = M.build_q6_involution(n, m, reps, d2i)
    T_obs = sum(u[j] * u[iota[j]] for j in range(L))
    obs_abs = abs(T_obs)

    rng = random.Random(M.SEED + p)
    vals = list(u)
    null_abs = []
    for _ in range(R):
        rng.shuffle(vals)
        null_T = sum(vals[j] * vals[iota[j]] for j in range(L))
        null_abs.append(abs(null_T))

    r_strict = strict_rank(obs_abs, null_abs)
    r_mid = midrank(obs_abs, null_abs)
    n_ties = sum(1 for t in null_abs if t == obs_abs)
    n_fixed = sum(1 for j in range(L) if iota[j] == j)
    return dict(p=p, L=L, T_obs=T_obs, obs_abs=obs_abs,
                rank_strict=r_strict, rank_mid=r_mid, n_ties=n_ties,
                n_fixed=n_fixed,
                pct_strict=r_strict*100//R, pct_mid=r_mid*100//R)

if __name__ == "__main__":
    print("=== Tie-handling verification: v1 Probe B d^{-1} involution ===")
    print("R = %d.  Mid-rank = strict_less + ties//2" % R)
    print()
    print("%-6s %-5s | %s | %s | %s" %
          ("p", "L", "T_obs  strict  midrank  ties  fixed", "strict%", "midrank%"))
    print("-" * 75)
    for p in (43, 67, 79, 127, 163, 211, 547,
              823, 907, 967, 991, 1051, 1303, 1831, 2143, 2251, 2503,
              577, 733, 1237, 1249, 1669):
        r = run_prime(p)
        if r is None:
            continue
        changed = "  <-- CHANGED" if r["pct_strict"] != r["pct_mid"] else ""
        print("%-6d %-5d | %+5d  %4d    %4d     %4d  %4d  |  %3d%%    %3d%%%s" %
              (r["p"], r["L"], r["T_obs"], r["rank_strict"], r["rank_mid"],
               r["n_ties"], r["n_fixed"],
               r["pct_strict"], r["pct_mid"], changed))
