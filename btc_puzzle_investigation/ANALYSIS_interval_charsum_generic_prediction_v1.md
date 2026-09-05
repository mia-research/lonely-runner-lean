# The generic prediction for the interval character sum — committed BEFORE the L=80000 row

**Date:** 2026-08-02. **Written while `bq4af5tea` is mid-run: L=5000 and L=20000 rows are in,
the decisive L=80000 row is NOT yet computed.** This pre-commits what "generic" actually predicts and
how to read the pending result — the antidote to the bias audit (I earlier invoked "equidistribution"
to dismiss without knowing what it predicts).

## What I got wrong before
I labeled the Stage A low-tail "generic/near-**equidistribution** (a deterministic orbit has lower
discrepancy than iid)." For a **character** readout that reasoning is **backwards**, and here is why.

## The actual generic prediction (standard heuristic, not a theorem)
Object: `Σ_{s∈I} χₖ(x([s]G))`, `I` = L consecutive scalars, χₖ a k-th-power character (k=2,3,6).

1. **Complete sum is Weil-small.** `Σ_{s∈ℤ/nℤ} χₖ(x([s]G))` is `O(√p)` (a nontrivial character composed
   with the curve map has square-root-cancelling complete sums). Relative to `n`, ≈ 0.
2. **Incomplete sum, typical size ~ √L.** Completing an interval sum of length `L ≪ √p` gives a bound
   `≲ √p·log p` that is **vacuous** (`> L`) — it neither predicts nor forbids. Under the pseudorandom
   (mixing) heuristic, L consecutive terms cancel like a √L random walk: **`|Σ|² ~ L`**, the SAME order
   as L *iid* random points. (Exact classical analog: short Dirichlet sums `Σ_{n≤L} χ(n)`, `L≪q`, are
   typically `~√L` — not smaller.)
3. **Why "low discrepancy" does NOT help.** Equidistributed sequences beat √L only for **bounded-
   variation** test functions (Koksma–Hlawka / Weyl). `χ(x([s]G))` oscillates over roots of unity with
   **unbounded variation** — it is the opposite of smooth — so the low-discrepancy gain does not apply.
   A deterministic orbit read through a character is **pseudorandom, not extra-cancelling.**

> **Generic prediction: interval char-sums ≈ random point-set char-sums.** `ratio ≈ 1`,
> `P(int<rand) ≈ 0.5`. Extra cancellation (intervals ≪ random) is NOT the generic expectation — it
> would be an anomaly.

## Pre-committed interpretation of the L=80000 row (write once, obey it)
- **`P(int<rand) ≈ 0.5`, `ratio ≈ 1`** (consistent across L, no growth) → **CONFIRMS generic mixing.**
  The interval sum carries no special cancellation. The Stage A 5–25× low-tail is then located
  **entirely as the bootstrap-null inflation** (pool imbalance `L²δ²`) — NOT equidistribution, NOT secp
  structure. The "generic/near-artifactual" RESULT labels become *earned*, and **sharpened**: not even
  a mild generic effect — mixing ⇒ random. Then C2 is the clean next move.
- **`ratio ≪ 1`, `P(int<rand) → 1`, GROWING with L** (L=80000 significantly beyond L=20000's mild,
  non-significant lean; z ≳ 3) → **REFUTES the generic prediction.** Consecutive `[s]G` char-sums
  cancel *more* than pseudorandom ⇒ the orbit is **not** mixing for χ ⇒ a real, secp-structural
  correlation. **This outranks everything** — characterize the mechanism, the exact scaling exponent,
  and whether it points toward the gate. Do NOT dismiss.
- **`ratio ≫ 1`, `P → 0`** → intervals *less* cancelled (anti-correlation) — also a real anomaly, also
  chased.

## The interim rows against this yardstick (NOT decisive)
- L=5000: E3 ratio 1.04, P 0.488 — squarely generic (≈random).
- L=20000: E3 ratio 0.74, P 0.614 (z +1.5) — a *mild* lean below random, **not significant** at N=30;
  consistent with generic at ~1.5σ. The low medians with a near-0.5 rank are the heavy right tail, not
  a systematic shift.

**The L=80000 row decides between the two branches. This file is the yardstick it will be read
against — fixed before the number exists.**
