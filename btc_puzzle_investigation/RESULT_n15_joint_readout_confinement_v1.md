# RESULT — N15 joint multi-readout confinement: scoped null on constructed secp keys

**Grade:** `[VERIFIED-scope — scoped null; instrument live (ε=1 plant fires at log₂3, monotone;
hard-null FP calibrated), across bands 32/64/128/256 incl. the real secp bit-length + exact
full-enumeration b=16]`
**Date:** 2026-08-25. **Prereg:** `PREREG_n15_joint_readout_confinement_v1.md`
(SHA `de453d46de19cc1566de3cab249378e2bf3b97ebc8130bbe512fa71ffb2b27f3`), deviation **D1** applied
(`PREREG_n15_joint_readout_confinement_v1_DEVIATIONS.md` — frozen full-joint-C primary was
bias-unestimable; replaced by the estimable low-order cheap-predictor family, object unchanged).
**Runner:** `n15_readout_confinement_runner_v1.py` (`check_no_float.sh` exits 0).

**NOT a closure. NO information ceiling is claimed or implied.** The public point [d]G determines d
completely (H(d|[d]G)=0 — that is what ECDLP is); the "3.65 bits" below is only the capacity of the
THREE cheap readouts chosen here, a floor that RISES as readouts are added (orbit-only 2.585 → 3.65 with
the carry), never a cap on exposable information. The result is a scoped null on ONE arm: no CHEAP
predictor extracts these readouts (the operational-extraction question — the DLP — stays OPEN, assumed-
hard not proven). The word "ceiling" is deliberately avoided: a bound that rises with each readout added
is not a ceiling. See `NOTE_readout_structure_no_selfimposed_ceiling_v1.md`.

---

## Object (well-posed reframing, D1)
Does any BOUNDED-COMPLEXITY (cheap) function `f` of the scalar `d` predict the joint public readout
`T(d) = (e([d]G), s-class([d]G), y-parity([d]G))` (18 cells) beyond a matched null, on known-d
secp256k1 keys? A positive = an operational cheap keyspace pre-filter. Readouts (validated, exact int):
`e` = cubic character `x^((p−1)/3)≡β^e` (uniform on {0,1,2}); `s-class` = 3-class Eisenstein carry
`carry_c` (distribution {¾,⅛,⅛}); `y-parity` = `[2y ≥ p]`. Predictor family `F` = 9 singletons
`{d%3,%6,%7,%9,%12, jacobi(d,n), cube-res(d,n), hi₃(d,b), lo₃(d)}` + all 36 pairs (45 predictors),
each dense-coded on realized support (estimable). Primary `S = max_{f∈F} Î(f;T)`, family-wise
permutation p (permute T, B=2000, exact integer count).

## Instrument is LIVE (the null is EARNED, not VOID)
- **ε-plant** (c*(d)=e w.p. ε else uniform, tested as a predictor vs T): monotone
  `I(c*;T) = 0.012 → 0.024 → 0.086 → 0.334 → 1.585` bits across ε = 4/64…64/64; at ε=1,
  `I(c*;T) = 1.5849 = log₂3` exactly (= H(e), e is a coordinate of T), p_perm = 1/2001 (0/2000).
  **eps=1 fires (p<0.001): True; monotone: True.**
- **Hard null** (C paired to a randomly-shuffled T): family FP@(1/20) = 1/40 = 0.025 ≤ 2α. Calibrated.

## Result — primary `S = max_f Î(f;T)`, per band (N=100,000 sampled; b=16 FULL enumeration)

| band b | max predictor | S_max (bits) | family p_perm | verdict |
|---|---|---|---|---|
| 32  | d%7+d%12 | 0.01053 | 0.207  | within null |
| 64  | d%7+d%12 | 0.01045 | 0.288  | within null |
| 128 | d%7+d%12 | 0.01136 | **0.0050** | marginal — see below |
| 256 (real secp band) | d%7+d%12 | 0.01012 | 0.636 | within null |
| 16 (EXACT full enum, 32768 keys) | d%7+d%12 | 0.03120 | 0.637 | within null |

- **Power (matched-null bias floor):** singleton `MI_floor ≈ 1.35×10⁻³` bits, pair `≈ 1.31×10⁻²`
  bits at N=10⁵ (b=16 enum: `4.1×10⁻³` / `4.0×10⁻²`). Every observed `S_max` sits at or below the
  pair bias floor; the permutation null absorbs it (the fingerprint of plug-in bias, not signal).
- **Per-readout singleton MIs** `I(f;e)/I(f;s)/I(f;yp)` are all `≤ 2×10⁻⁴` bits across every band —
  far below the singleton floor `1.35×10⁻³`, i.e. no single cheap predictor carries any readout
  (extends the #4 baseline `max MI(e;8 cheap fns)=0.033` at n≈349 down to this deeper floor and to
  the full 18-cell readout T). The two-way `TC(e,s,yp) ≈ 1×10⁻⁴` bits: the three readouts are
  mutually near-independent on secp keys.

## The one marginal (surfaced, tested, does NOT survive)
Band b=128 shows family p_perm = 0.0050 for `d%7+d%12`. Following the drill/reproduction rules it is
**tested, not banked**:
1. It fails the pre-registered RETAINED bar (FW p < 0.001); 0.0050 > 0.001.
2. It **does not reproduce**: the SAME predictor `d%7+d%12` gives p = 0.207 / 0.288 / 0.636 at
   b = 32 / 64 / 256, and **0.637 at the EXACT full-enumeration b=16** (the highest-power arm, entire
   keyspace, zero sampling floor). One band in five, non-reproducing including under exact enumeration.
3. Its magnitude `S=0.01136` is **below** the pair bias floor `1.31×10⁻²`.
It is the expected multiple-comparison fluctuation (5 bands × 45-predictor family), not a lead.
**Re-test DONE (2026-08-25):** independent seed 11, B=4000, band 128, N=100000 → `d%7+d%12` family
p_perm = **0.4426** (was 0.005 at seed 7); the hit was seed-specific and dissolved. With the four
original non-reproductions (incl. exact b=16 enumeration) that is five independent non-reproductions plus
a fresh-seed wash. **Marginal decisively closed as noise.** Instrument re-confirmed live on the re-test
(ε=1 plant → 1.5849, monotone; hard-null FP 2/30 ≤ 0.10).

## Structure the three chosen readouts expose (characterized, exact — NOT a ceiling)
`H(T|I) ≈ 3.65 bits` at every band; `H(d|T,I) = (b−1) − 3.65` = 27.35 / 59.35 / 123.35 / 251.35 at
b = 32/64/128/256. This 3.65 is an **exact, additive decomposition** of what these THREE readouts carry,
independently reconstructing the corpus's algebraic accounting from a disjoint entropy method:
`H(e)=1.585` (cubic/μ₃) `+ H(y-parity)=1.000` (negation/μ₂) `= 2.585` (the μ₆-orbit label) `+
H(s-class)=1.061` (the {¾,⅛,⅛} carry) `= 3.646`, with `TC≈10⁻⁴` — the newly-measured fact that the
orbit label and the carry are **information-theoretically independent** (that is *why* they add).
**This is a rising floor, not a ceiling.** Adding one readout took it 2.585 → 3.65; nothing here bounds
what more readouts (or non-per-point / joint constructions) expose — the public point determines d in
full. What this arm shows is only that no CHEAP predictor extracts even these characterized bits at
tested power; converting indexical structure to operational work is the DLP, which stays OPEN (assumed-
hard, not proven). Reported as characterized structure + an open extraction question — never "0
operational / capped."

## Verdict (pre-committed, §7/§9 "SCOPED NULL" row + D1)
No cheap predictor (9 singletons + 36 pairs) predicts the joint readout `T=(e,s-class,y-parity)` beyond
the matched permutation null, reproducibly, across bands **32, 64, 128, 256** (incl. the real secp
256-bit band, via constructed keys) and the **exact full-enumeration b=16**, at power
`MI_floor ≈ 1.3×10⁻³` (singleton) / `1.3×10⁻²` (pair). Instrument live (ε=1 plant fires at log₂3,
hard-null calibrated). `|S| < MI_min`. **Bounded magnitude, NOT a closure.**

## What is NOT settled (untested channels — the null is bounded)
- **Higher-order cheap predictability** (functions of ≥3 C-components jointly, or the full joint C)
  invisible to all singletons and pairs (D1's named cost of making the primary estimable).
- Other cheap-predictor families beyond the frozen 9; other readouts / larger-alphabet joint readouts.
- The DLP-inversion direction (out of scope by construction — reading T is O(1); inverting T→d is the DLP).
- The exact-enumeration confinement arm reaches only b=16 here (b≤24 feasible); 256-bit confinement is
  sampled, and bounded by FACT 1's constant ceiling regardless.

## Owed gates
- Second independent `experiment-designer` read: OWED before any POSITIVE promotes (moot for this null;
  recorded).
- `compile-diff` if folded into a `POSITIVE_FINDINGS_MASTER_*` / handover.
- `check_no_float.sh`: exits 0 on the runner (mechanical gate satisfied).

## Frame-audit disclosures (2nd independent experiment-designer read, 2026-08-25)
The second isolated experiment-designer read judged the null **EARNED on a well-posed spec** (frame
sound; D1 a faithful feature-side reframe; matched null correct and not the `r=v−w` mode; the
"ceiling→rising floor" correction complete). Two disclosure gaps it surfaced, both low-impact and both
conservative for a null (neither changes what the null means):
1. **μ₆ null-validity witness (prereg §3/§7) — holds identically at these band sizes, so unreported.**
   The witness compares `S` on the μ₆-orbit-collapsed set vs the full set. The orbit action on the
   SCALAR is `d ↦ ±λ^j d (mod n)`; for `d` in a width-`2^b` interval with `n ~ 2^256`, the images
   `±λ^j d mod n` land at `~n` scale, **outside** the interval — so no two sampled/enumerated `d` are
   orbit-mates and the orbit-collapsed set **equals** the full set (exactly, incl. the b=16 full
   enumeration). The witness is therefore satisfied trivially; had it been violated it would inflate
   `S` (work against a null), so the null is conservative w.r.t. it.
2. **Hard-null calibrated at α=0.05 (40 re-pairings), not the verdict α=0.001 (§2e) — disclosed
   deviation.** A 0.001-level FP rate is not empirically measurable at 40 re-pairings; the exact
   permutation test is valid analytically (exchangeability under H₀), the empirical check is a sanity,
   and any residual miscalibration is anti-conservative (toward false positives), so it cannot
   manufacture a false null. Observed primary family p's (0.21–0.64) sit far from any threshold.

## Provenance
Exact int signal path (scalar mult, x/y, cubic char, `carry_c`, y-parity, C-components); float only in
the MI `log₂`, ranked against exact integer permutation counts (`# noqa: float`). Seed 7. Constructed
known-d keys on demand (build pipeline `build_fullrange_dataset_v1.py` arithmetic) + exact enumeration
at b=16. Real-82 OOS arm not exercised in this pass (constructed arm is the power-bearing arm; a
constructed null needs no real-arm corroboration — the real arm matters only to corroborate a
constructed POSITIVE, of which there is none). Runner + full log archived
(`n15_readout_confinement_runner_v1.py`).
