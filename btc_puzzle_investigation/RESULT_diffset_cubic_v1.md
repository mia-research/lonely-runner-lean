# RESULT — Cubic difference-set energy `E3` applied to the real 82 (v1)

**Grade:** `[EMPIRICAL — pre-registered REJECT-HIGH at α=0.05, nominal two-sided p≈0.033; NOT
multiple-comparison-corrected; robustness partial; interpretation ceiling below]`.
Applied 2026-07-26 vs frozen [PREREG_diffset_cubic_v1.md] (spec locked before the real value existed).
Integer-exact path.

---

## §1 — Fired cell (pre-committed conclusion)
```
(a,b,c) = (1082, 1057, 1182)   sum=3321 ✓   E3 ≡ 0 mod 3 ✓ (forced bug-check)
E3(real) = 13125
frozen region: fail-to-reject iff E3 ∈ [84, 11997]
decision:  13125 > 11997  ->  REJECT-HIGH (cubic-class concentration)
position:  98.4th percentile of the matched known-MT control null; two-sided rank p ≈ 0.033
```
Per prereg pre-commitment, a reject-high goes to §1: the real 82's pairwise x-difference distribution
over the secp cubic character is **concentrated beyond the frozen region** — driven by a **+75 excess
in class β²** ((a,b,c) deviations −25/−50/+75; χ²(df2)=7.90, p≈0.019).

## §1a — Verification (the reject is w.r.t. a validated null)
- Frozen null order-statistics reproduce the region exactly (A[249]=84, A[9750]=11997).
- Independent regeneration (seed 4242, 2000 resamples): mean 3293, 97.5%=11892 — matches frozen
  (97.5%=11997) within resampling noise. Null is the Exp(√-floor); E3=13125 in the tail.
- Integer-only signal path; forced E3≡0 mod3 held on real data.

## §1b — Robustness audit (fired cells get MORE scrutiny)
- **Jackknife drop-one:** E3 ∈ [9723, 15831], median 12513; **59/82 drops stay above** the
  size-scaled threshold ⇒ distributed, not a single-key artifact. But removing the single most
  influential key (puzzle 115) alone drops it to 9723 (< threshold) ⇒ moderately robust, not
  rock-solid. Top drivers span bit-lengths (115, 61, 42, 130, 64) — not one band.
- **High-bit subset (bits ≥ 11, n=72):** E3=9291 at the **98.0th percentile** of its own matched
  null ⇒ the excess is **present on the high-bit keys that can differ from control** (not confined to
  the shared low-bit keys). Bears on the null-artifact question only; not independent replication.

## §2 — Why this is NOT yet a finding (symmetric rigor; do not inflate)
- **Multiple comparisons.** E3 is **1 of ~7 statistics** computed this session (μ₆ marginal, χ₂
  marginal, 12-cell, Kruskal-Wallis, point-biserial, S_diff, E3). Nominal p≈0.033 ⇒ Bonferroni ×7 ≈
  **0.23 (not significant)**; even across only the 2 difference-set tests, ×2 ≈ 0.066 (borderline).
- **No independent real replication exists.** Only 82 solved keys; the 6 exposed-pubkey unsolved
  (135–160) are n=6 — far too small for E3. The high-bit subset is the *same* fired statistic
  re-tested (a robustness check that can fail-to-break it, not independent confirmation).
- **Under the standard assumption** (real puzzle keys uniform-random in their bit-ranges) real ≡
  constructed, so E3(real) is a null draw and p≈0.033 across ~7 tests is expected by chance.

## §3 — Interpretation (OPEN; a "ceiling" claim was retracted — see secondcontrol v1, 2026-07-27)
Even if the excess is real, E3 is a **joint property of the pubkey-x SET**: the real puzzle pubkeys'
pairwise differences over-populate cubic class β² relative to *our MT19937 constructed control*.
1. A real-vs-construction difference **could** be generation-side (the puzzle creator's key method ≠
   MT19937); *if* it is, that angle is off-limits per `feedback_no_prng_generation_side`. This is a
   possibility, **not** a demonstrated fact about this reject.
2. E3 does not, *by itself*, yield a private key. Whether the structure it detects is curve-relevant
   or merely generator-descriptive is **open** — the earlier "generator-descriptive by construction"
   phrasing was an unproved overclaim and is retracted.
3. Per the Anomaly-Drill protocol this is a **characterization, not a verdict** — no "break", no
   "leak", no closure, and no impossibility claim either. It opens a sharper probe.

## §4 — Next probe (the one decidable way to firm this up)
A **second, independent control** with a *different generator* (e.g. `secrets`/OS-CSPRNG or a
non-MT PRNG through the same select-bitlen→curve pipeline), pre-registered:
- If E3(real) rejects vs MT-control but **not** vs the independent control ⇒ the effect is
  "MT19937 ≠ real generator" (generation-side) ⇒ off-limits per the generation-side rule, not a
  curve statement.
- If it rejects vs **multiple independent controls** ⇒ a more robust joint property of the real set,
  worth characterizing (which pairs/bands carry the β² excess).
This does not upgrade the current grade; it is the reproduction the fired cell requires before it is
named anything.
