"""
lrc_case_r_residual_harness_v1.py
===================================
Computational verification of the Theorem R1 residuals for n=11 LRC.

Residuals from lrc_n11_route3_residual_analysis_v1.md:
  - MILD  [89, 100]: Chain A configs where GF(I₈)≥1/50 but runner 1 blocks I₈.
  - HARD   >100   : Runner 1 blocks all of W₀; witness must live in W₁.

Strategy: use EXACT rational arithmetic (fractions.Fraction) and the
boundary-set method (enumerate all critical times in (0, T_cap]).
T_cap = 10/p₁ covers W₀ ∪ W₁ ∪ W₂, so witnesses in W₁ are found automatically.

Slot definitions (n=11, runner 10 = AP pacemaker at speed p₁₀):
  I_k = [(11k+1)/110, (11k+10)/110]  for k=1,...,9
  W₀  = [1/11, 10/11]                (runner-1 isolation window in relative coords)
  W₁  = [1/(11·a₁), 10/(11·a₁)]     (first full isolation window of runner 1)
       = [p₁₀/(11·10), 10·p₁₀/(11·10)] for integer speeds with a₁=10/p₁₀

Canonical configuration tested: speeds = {1, 2, 3, 4, 5, 6, 7, 8, 9, p₁₀}.
"""

import json
import sys
from fractions import Fraction


# ─── helpers (exact arithmetic) ─────────────────────────────────────────────

def frac_part(x: Fraction) -> Fraction:
    return x - int(x)


def dist_to_int(x: Fraction) -> Fraction:
    f = frac_part(x)
    return min(f, Fraction(1) - f)


def is_isolated(speed, t: Fraction, n: int = 11) -> bool:
    return dist_to_int(Fraction(speed) * t) >= Fraction(1, n)


def all_isolated(speeds, t: Fraction, n: int = 11) -> bool:
    thr = Fraction(1, n)
    for p in speeds:
        if dist_to_int(Fraction(p) * t) < thr:
            return False
    return True


def min_iso(speeds, t: Fraction) -> Fraction:
    return min(dist_to_int(Fraction(p) * t) for p in speeds)


# ─── slot / window classification ────────────────────────────────────────────

# Slot I_k = [(11k+1)/110, (11k+10)/110]  for k=1,...,9
SLOTS = {k: (Fraction(11*k+1, 110), Fraction(11*k+10, 110)) for k in range(1, 10)}

# Chain A gap in I₈
CHAIN_A_GAP_LO = Fraction(89, 110)   # = I₈ left
CHAIN_A_GAP_HI = Fraction(228, 275)  # = B₆,₄[0] exact


def slot_of(t: Fraction):
    """Return slot index k if t ∈ I_k, else None."""
    for k, (lo, hi) in SLOTS.items():
        if lo <= t <= hi:
            return k
    return None


def classify_witness(t: Fraction, a1: Fraction, p10: int):
    """
    Classify a witness time t into:
      W0_I9   : t in I₉ within W₀
      W0_I8   : t in I₈ within W₀ (and in runner-1-isolated zone)
      W0_other: t in W₀, other slot
      W1      : t in W₁ = [1/(11a₁), 10/(11a₁)]  (outside W₀)
      W2plus  : t beyond W₁
    Also flags if t is in the Chain A gap [89/110, 228/275].
    """
    W0_lo = Fraction(1, 11)
    W0_hi = Fraction(10, 11)
    # W₁ = [1/(11·a₁), 10/(11·a₁)]
    # a₁ = 10/p₁₀, so 1/(11·a₁) = p₁₀/110
    W1_lo = Fraction(p10, 110)          # = 1/(11·a₁) = p₁₀/(11·10)
    W1_hi = Fraction(10 * p10, 110)     # = 10/(11·a₁)

    in_W0 = (W0_lo <= t <= W0_hi)
    in_W1 = (W1_lo <= t <= W1_hi)
    in_chain_a_gap = (CHAIN_A_GAP_LO <= t <= CHAIN_A_GAP_HI)

    k = slot_of(t)

    if in_W0:
        if k == 9:
            label = "W0_I9"
        elif k == 8:
            label = "W0_I8"
        else:
            label = f"W0_I{k}" if k else "W0_inter-slot"
    elif in_W1:
        label = "W1"
    else:
        label = "W2plus"

    return label, in_chain_a_gap, k, in_W0, in_W1


# ─── core: boundary-set witness search ───────────────────────────────────────

def find_witnesses(speeds, n: int = 11, T_cap_multiplier: int = 12):
    """
    Find ALL joint isolation windows in (0, T_cap] using exact arithmetic.

    T_cap = T_cap_multiplier / p₁  (default: 12/p₁, covering W₀,W₁,W₂ for ratio≤200)
    Returns list of (start, end) Fraction pairs — joint isolation windows.
    """
    p1 = speeds[0]
    T_cap = Fraction(T_cap_multiplier, p1)
    thr = Fraction(1, n)

    # Generate all critical times: entry/exit for each runner in each cycle
    crit = set()
    for p in speeds:
        j = 0
        while True:
            t_entry = Fraction(n * j + 1, n * p)
            if t_entry > T_cap:
                break
            crit.add(t_entry)
            t_exit = Fraction(n * j + (n - 1), n * p)
            if t_exit <= T_cap:
                crit.add(t_exit)
            j += 1

    breakpoints = sorted(set([Fraction(0)] + list(crit) + [T_cap]))

    windows = []
    w_start = None
    for i in range(len(breakpoints) - 1):
        a = breakpoints[i]
        b = breakpoints[i + 1]
        mid = (a + b) / 2
        if mid <= Fraction(0):
            continue
        if all_isolated(speeds, mid, n):
            if w_start is None:
                w_start = a
        else:
            if w_start is not None:
                windows.append((w_start, b))
                w_start = None
    if w_start is not None:
        windows.append((w_start, T_cap))

    return windows, T_cap


# ─── per-config analysis ──────────────────────────────────────────────────────

def analyse_config(p10: int, verbose: bool = True):
    """
    Full analysis for canonical config {1,2,...,9,p10}.
    Returns a result dict.
    """
    speeds = list(range(1, 10)) + [p10]
    a1 = Fraction(10, p10)       # a₁ = 10/p₁₀ in EFN normalisation
    ratio = p10                  # = p₁₀/p₁ since p₁=1

    W0_lo = Fraction(1, 11)
    W0_hi = Fraction(10, 11)
    W1_lo = Fraction(p10, 110)          # 1/(11·a₁)
    W1_hi = Fraction(10 * p10, 110)     # 10/(11·a₁)

    # Chain A gap runner-1-free sub-interval: [max(W0_lo, W1_lo), CHAIN_A_GAP_HI]
    # Runner 1 is isolated for t >= W1_lo within W₀
    ca_free_lo = max(W0_lo, W1_lo)
    ca_free_hi = CHAIN_A_GAP_HI
    ca_free_width = max(Fraction(0), ca_free_hi - ca_free_lo)

    windows, T_cap = find_witnesses(speeds)

    # Classify each window
    W0_witnesses = []
    W1_witnesses = []
    W2_witnesses = []
    chain_a_witnesses = []

    first_witness_t = None
    first_label = None

    for (ws, we) in windows:
        mid = (ws + we) / 2
        lbl, in_ca, k, in_W0, in_W1 = classify_witness(mid, a1, p10)
        m_iso = min_iso(speeds, mid)

        entry = {
            "window": (str(ws), str(we)),
            "width": str(we - ws),
            "width_float": float(we - ws),
            "label": lbl,
            "slot": k,
            "in_chain_a_gap": in_ca,
            "min_iso": str(m_iso),
            "min_iso_float": float(m_iso),
        }

        if in_W0:
            W0_witnesses.append(entry)
        if in_W1:
            W1_witnesses.append(entry)
        if not in_W0 and not in_W1:
            W2_witnesses.append(entry)
        if in_ca:
            chain_a_witnesses.append(entry)

        if first_witness_t is None:
            first_witness_t = mid
            first_label = lbl

    result = {
        "p10": p10,
        "ratio": ratio,
        "a1": str(a1),
        "a1_float": float(a1),
        "W0": (str(W0_lo), str(W0_hi)),
        "W1": (str(W1_lo), str(W1_hi)),
        "chain_a_gap": (str(CHAIN_A_GAP_LO), str(CHAIN_A_GAP_HI)),
        "chain_a_runner1_free_width": str(ca_free_width),
        "chain_a_runner1_free_width_float": float(ca_free_width),
        "T_cap": str(T_cap),
        "total_windows": len(windows),
        "W0_windows": len(W0_witnesses),
        "W1_windows": len(W1_witnesses),
        "W2plus_windows": len(W2_witnesses),
        "chain_a_gap_windows": len(chain_a_witnesses),
        "first_witness_label": first_label,
        "first_witness_t": str(first_witness_t) if first_witness_t else None,
        "W0_witness_details": W0_witnesses[:3],   # first 3
        "W1_witness_details": W1_witnesses[:3],
        "chain_a_witness_details": chain_a_witnesses[:3],
        "CLOSED": len(windows) > 0,
    }

    if verbose:
        _print_result(result, p10, speeds)

    return result


def _print_result(r, p10, speeds):
    closed = r["CLOSED"]
    status = "✓ WITNESS FOUND" if closed else "✗ NO WITNESS"

    print(f"\n{'─'*60}")
    print(f"  ratio={r['ratio']:4d}  a₁={r['a1_float']:.5f}  {status}")
    print(f"  W₀ = {r['W0'][0]} .. {r['W0'][1]}")
    print(f"  W₁ = {r['W1'][0]} .. {r['W1'][1]}")
    print(f"  Chain A gap [89/110, 228/275]  runner-1-free width = {r['chain_a_runner1_free_width_float']:.6f}")

    if r["first_witness_t"]:
        print(f"  First witness at t={r['first_witness_t']}  location={r['first_witness_label']}")
    print(f"  Windows: total={r['total_windows']}  in_W0={r['W0_windows']}  in_W1={r['W1_windows']}  in_ChainA={r['chain_a_gap_windows']}")

    if r["W0_witness_details"]:
        w = r["W0_witness_details"][0]
        print(f"  Best W₀ witness: slot=I{w['slot']}  min_iso={w['min_iso_float']:.6f}  width={w['width_float']:.2e}")
    if r["W1_witness_details"]:
        w = r["W1_witness_details"][0]
        print(f"  Best W₁ witness: slot=I{w['slot']}  min_iso={w['min_iso_float']:.6f}  width={w['width_float']:.2e}")
    if not closed:
        print(f"  *** ALERT: NO WITNESS FOUND — potential counterexample! ***")


# ─── main ─────────────────────────────────────────────────────────────────────

def main():
    print("=" * 60)
    print("LRC Case R> Residual Harness  |  n=11  |  Exact Arithmetic")
    print("=" * 60)
    print(f"Canonical configs: speeds = {{1,2,...,9,p₁₀}}")
    print(f"Chain A gap: [{CHAIN_A_GAP_LO}, {CHAIN_A_GAP_HI}]  width={float(CHAIN_A_GAP_HI - CHAIN_A_GAP_LO):.6f}")

    results = {}
    failures = []

    # ── MILD RESIDUAL: ratio ∈ [89, 100] ──────────────────────────────────────
    print("\n" + "=" * 60)
    print("MILD RESIDUAL: ratio ∈ [89, 100]")
    print("=" * 60)
    mild_results = {}
    for p10 in range(89, 101):
        r = analyse_config(p10, verbose=True)
        mild_results[p10] = r
        if not r["CLOSED"]:
            failures.append(p10)
    results["mild"] = mild_results

    # ── HARD RESIDUAL: ratio ∈ [101, 200] ────────────────────────────────────
    print("\n" + "=" * 60)
    print("HARD RESIDUAL: ratio ∈ [101, 200]")
    print("=" * 60)
    hard_results = {}
    for p10 in range(101, 201):
        r = analyse_config(p10, verbose=(p10 <= 115 or p10 % 10 == 0))
        hard_results[p10] = r
        if not r["CLOSED"]:
            failures.append(p10)
    results["hard"] = hard_results

    # ── SUMMARY ───────────────────────────────────────────────────────────────
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)

    mild_closed = sum(1 for r in mild_results.values() if r["CLOSED"])
    hard_closed = sum(1 for r in hard_results.values() if r["CLOSED"])

    print(f"Mild residual [89,100]: {mild_closed}/12 closed")
    print(f"Hard residual [101,200]: {hard_closed}/100 closed")

    if failures:
        print(f"\n*** FAILURES (no witness found): {failures} ***")
    else:
        print(f"\nAll {mild_closed + hard_closed} configs have witnesses. ✓")

    # Location breakdown for mild residual
    print("\nMild residual — witness location breakdown:")
    loc_counts = {}
    for r in mild_results.values():
        lbl = r["first_witness_label"] or "NONE"
        loc_counts[lbl] = loc_counts.get(lbl, 0) + 1
    for lbl, cnt in sorted(loc_counts.items()):
        print(f"  {lbl}: {cnt}")

    print("\nHard residual — witness location breakdown:")
    loc_counts_h = {}
    for r in hard_results.values():
        lbl = r["first_witness_label"] or "NONE"
        loc_counts_h[lbl] = loc_counts_h.get(lbl, 0) + 1
    for lbl, cnt in sorted(loc_counts_h.items()):
        print(f"  {lbl}: {cnt}")

    # ── SAVE JSON ─────────────────────────────────────────────────────────────
    out_path = "reports/lrc_case_r_residual_results_v1.json"
    # Convert Fraction objects to strings for JSON serialisation
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nResults saved to {out_path}")

    return failures


if __name__ == "__main__":
    failures = main()
    sys.exit(1 if failures else 0)
