# RESULT — Cubic `E3` second-control reproduction (v1)

**Grade:** unchanged — `[EMPIRICAL — pre-registered reject, p≈0.03–0.04, NOT MC-corrected;
generation-side ceiling]`. Applied 2026-07-27 vs frozen [PREREG_diffset_cubic_secondcontrol_v1.md].
Reproduction of [RESULT_diffset_cubic_v1.md]. Integer-exact.

---

## Outcome (pre-committed reading #1)
```
E3(real) = 13125  (integrity recompute ✓)
Control-2 = uniform random valid secp curve x (generator-agnostic; no PRNG-of-d; no bit-length)
Control-2 null (n=10000): mean 3320.5, 2.5%=93, 50%=2307, 97.5%=12153
VALIDITY GATE: PASS  (Control-2 null ≈ MT null: mean 3320 vs 3274, 97.5% 12153 vs 11997)
DECISION vs Control-2: 13125 > 12153  ->  REJECT-HIGH, 98.1st pct, two-sided p ≈ 0.038
   (MT control gave: REJECT-HIGH, 98.4th pct, p ≈ 0.033)
```

## What this DID establish
- The reject is **not an artifact of the MT null's construction or bit-length matching**: it persists
  against a completely different, generator-agnostic null (uniform random curve points, no d, no PRNG).
- The validity gate passing means **bit-length is irrelevant to the E3 null** (pubkey-x is
  pseudorandom in d, as ECDLP assumes) — so E3(real)=13125 sits at the ~98th percentile of
  the *correct* null. Not a null-estimation artifact.

## What this did NOT establish (precise, do not inflate)
- **Not independent replication.** Same fixed E3(real)=13125, and the validity gate confirms
  Control-2's null is the *same distribution* as MT's. Two ~identical nulls → the two p-values
  (0.033, 0.038) are **one result expressed twice**, not two independent confirmations. The p-value is
  not reduced.
- **Multiple comparisons unaddressed.** Still 1 of ~7 statistics this session; Bonferroni non-sig.
- **No new real data.** n=82 fixed; the only true out-of-sample would be additional solved keys.

## Interpretation (OPEN) — earlier overclaim RETRACTED 2026-07-27
**Retraction.** An earlier draft of this file (and the chat around it) asserted an *unliftable
ceiling*: that E3 is "generator-descriptive **by construction**", that "**no control** can move it",
and that a reject "says **nothing** about the curve". Those are unconditional impossibility claims and
were **never proved** — stating them as settled is the null→closure / negative-bias failure mode this
project tracks (`feedback_negative_bias_enlarge_nulls_2026_07_17`, `feedback_conditional_negatives_phrasing`).
Retracted.

**What is actually supported (scoped, conditional):**
- E3 is a function of the pubkey-x set, itself a deterministic image of the d set. *(fact)*
- The two controls run — MT bit-matched and uniform curve points — yield the same null, so the
  interpretation is stable **across the controls tested**, not across all conceivable controls. *(measured)*
- If the real d's were uniform iid, E3(real)=13125 would be a null draw (p≈0.04). *(follows)*

**What is NOT established:** that an E3 reject *must* be generation-side, or that it *cannot* be
curve-relevant. The project's own stance is that a joint property of the key SET is a *candidate*
signal, not something to foreclose (`btc_puzzle_investigation/CLAUDE.md`). The interpretation is **open**.

## Bottom line
A weak (p≈0.03–0.04), pre-registered anomaly in the real 82-key pubkey set that is **not a null
artifact**, but **is** multiple-comparison-non-significant and un-replicated (n=82 fixed). Its
interpretation is **open**, not ceilinged. Characterization, not a verdict.

## Fork for the next step (both legitimate — neither foreclosed)
1. **Characterize the β² excess** (which pairs / bit-bands drive the +75 in class β²) — the
   non-dismissive move for a fired, non-artifact cell: understand it before naming it.
2. **Add a group-law object** — a joint statistic built from curve *addition* (`P_i ± P_j`, or a
   function of `d_i, d_j` via the group), which connects to the discrete log through curve arithmetic
   in a way a pure x-coordinate character sum does not. Complementary to (1), not a replacement for it.
