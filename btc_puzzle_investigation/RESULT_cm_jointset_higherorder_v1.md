# RESULT — A-joint-HO (higher-order / GLV / finer-label joint-set synergy): discovery-tier scoped null

**Grade:** `[VERIFIED-scope — scoped null across discovery + confirmation (OOS, N=20k) + ladder to
2¹⁶; all 7 channels within null at every prime, all firing controls live; μ₂ plant fixed
(distinct_planted 1→2); semaev_s4 citation SUPPORTED (Semaev 2004 / Kosters–Yeo Prop 2.1) with the
degenerate-tuple caveat (Prop 2.2), full Prop 2.2 read owed on session-limit reset.]`
**Update 2026-08-25 (same day):** confirmation + ladder tiers completed (§Confirmation+ladder below);
this supersedes the discovery-only grade. Model scale, ZERO secp power throughout.
**Date:** 2026-08-25. **Prereg:** `PREREG_cm_jointset_higherorder_v1.md` (runner prints SHA
`d97ee950f2f2…`). **Runner:** `cm_jointset_ho_v1.py` (imports `model_curve_infra_v1.py`; new primitive
`semaev_s4`; `check_no_float.sh` exits 0). **Extends:** `RESULT_cm_jointset_excess_v3.md` (the r=3/m=3/μ₃
base scoped null) to the six channels v3 named "not settled".

**MODEL SCALE — ZERO power against secp256k1** (q ∈ {541,571,577} ≪ 2¹⁶). Measures a MECHANISM only.
No ECDLP / extraction / security claim. A null is a bounded magnitude with power+scope, never a closure.

---

## Instruments are LIVE (controls, N=3000, R=800)
All seven channels' plants fire at ρ=0.30 (p=1/801, monotone across the ρ ladder):

| channel | ρ=0.15 | 0.30 | 0.60 | distinct_planted | live? |
|---|---|---|---|---|---|
| P1_S4 (r=4) | 0.0037 | 0.0012 | 0.0012 | 3 | yes |
| P2_C4 (m=4) | 0.0012 | 0.0012 | 0.0012 | 3 | yes |
| P3_GLV | 0.0012 | 0.0012 | 0.0012 | 3 | yes |
| P4_μ₂ | 0.0012 | 0.0012 | 0.0012 | **1** | fires, but plant degenerate (see note) |
| S_INT | 0.0012 | 0.0012 | 0.0012 | 3 | yes |
| S_XY | 0.0025 | 0.0012 | 0.0012 | 2 | yes |
| S_C5 | 0.0025 | 0.0012 | 0.0012 | 3 | yes |

**P4_μ₂ plant nit (STOP-fix, not VOID):** planting a 3-valued Ψ₂=χ₂(S₃) to match a 2-valued label
J₂=(Σd) mod 2 yields distinct_planted=1 (the guard wants ≥2). The instrument still fires strongly and
monotonically, but the μ₂ plant construction must be fixed (e.g. plant against a 3-valued proxy, or
map Ψ₂→{0,1}) before any μ₂ Δ could promote. The μ₂ CM measurements below are at the floor regardless.

## Result — discovery tier (N=5000, R=1500), CM within-null p and Δ = I(CM) − I(nonCM)

| channel | q=541 CM p | q=571 CM p | q=577 CM p | Δ (541 / 571 / 577) | verdict |
|---|---|---|---|---|---|
| P1_S4 (r=4)  | 0.709 | 0.853 | 0.347 | −0.0015 / −0.0025 / −0.0060 | within null; Δ≤0 |
| P2_C4 (m=4)  | 0.334 | 0.717 | 0.498 | +0.0002 / −0.0040 / −0.0034 | within null; Δ≈0 |
| P3_GLV       | 0.702 | 0.560 | 0.171 | (CM-only) | within null |
| P4_μ₂ (ℓ=2)  | 0.588 | 0.204 | 0.843 | +0.00003 / +0.00001 / −0.0024 | within null; Δ≈0 |
| S_INT (finer)| 0.927 | 0.961 | 0.438 | (CM-only) | within null |
| S_XY (coord) | 0.053 | 0.661 | 0.739 | (CM-only) | within null (see marginal) |
| S_C5 (m=5)   | 0.999 | 0.887 | 0.518 | (CM-only) | within null |

- **Primary family (P1/P2/P4):** every Δ ≤ 0 or ≈ 0 (CM never exceeds non-CM). Holm–Bonferroni across
  the 4 primaries rejects nothing (no CM p ≤ 0.01 anywhere). No CM-specific joint synergy in the
  r=4-Semaev, m=4-combo, or μ₂-label channels — the v3 μ₃/r=3/m=3 scoped null extends to these.
- **CM-only channels (P3/S-INT/S-XY/S-C5):** all within their within-stratum nulls. GLV-mixed
  endomorphism cross-features, finer interval labels, the coordinate-pair (x,y) statistic, and the m=5
  combo add no detectable joint-set structure at discovery power.

## Marginals (surfaced, tested, do NOT survive)
1. **S_XY q=541, p=0.053** — just above 0.05, non-reproducing (p=0.66, 0.74 at q=571, 577). The 216-stratum
   coordinate-pair table has heavy plug-in bias (CM mi≈0.27) which the within-stratum null absorbs; the
   one near-0.05 is noise, not a lead.
2. **P4_μ₂ nonCM q=577, p=0.0093** — WRONG arm (non-CM, not the CM headline), 1/3 primes, non-reproducing
   (nonCM p=0.62, 0.24 at q=541, 571). Expected multiple-comparison noise (7 channels × 2 arms × 3 primes).

## Verdict (discovery tier)
No CM-specific joint-set synergy (P1/P2/P4: Δ≤0, no CM p≤0.01) and no within-null firing in the
GLV-mixed / finer-interval / coordinate-pair / m=5 channels, across the 3 discovery primes at
discovery-tier power, all firing controls live. Extends the v3 base scoped null to r=4 Semaev, m=4/m=5
combos, μ₂ label, GLV-mixed features, coordinate-pair, and finer interval — **at discovery-tier scope.**

## Confirmation (OOS) + ladder — completed 2026-08-25 (per-channel CM p across primes)

**Confirmation tier (OOS, N=20,000, R=1500, primes 2029/2053/2089):**

| channel | CM p (2029/2053/2089) | read |
|---|---|---|
| P1_S4  | 0.968 / 0.502 / 0.494 | null |
| P2_C4  | 0.380 / 0.042 / 0.938 | null (single 0.042, non-reproducing) |
| P3_GLV | 0.376 / 0.434 / 0.127 | null |
| P4_μ₂  | 0.526 / 0.271 / 0.417 | null |
| S_INT  | 0.861 / 0.663 / 0.069 | null |
| S_XY   | 0.052 / 0.576 / 0.051 | null (two ~0.05, neither <0.01, non-reproducing) |
| S_C5   | 0.450 / 0.547 / 0.458 | null |

**Ladder (N=5000, R=1500, primes 1033/4111/16417/65539):**

| channel | CM p (1033/4111/16417/65539) | read |
|---|---|---|
| P1_S4  | 0.201 / 0.677 / 0.953 / 0.880 | null |
| P2_C4  | 0.402 / 0.910 / 0.504 / 0.949 | null |
| P3_GLV | 0.021 / 0.710 / 0.455 / 0.833 | null (single 0.021, non-reproducing) |
| P4_μ₂  | 0.383 / 0.951 / 0.589 / 0.430 | null |
| S_INT  | 0.015 / 0.410 / 0.909 / 0.025 | null (two low, non-reproducing, neither <0.01) |
| S_XY   | 0.674 / 0.411 / 0.534 / 0.879 | null |
| S_C5   | 0.027 / 0.077 / 0.428 / 0.270 | null (single 0.027, non-reproducing) |

Every primary-family Δ (P1/P2/P4, CM − nonCM) is ≤0 or ≈0 across both tiers; Δ is flat with no upward
scale trend to 2¹⁶. All scattered p∈[0.01,0.05] hits (S_XY, S_INT, S_C5, P2, P3) fail reproduction
across the schedule and none falls below 0.01 — the expected multiple-comparison noise floor (7 channels
× up to 10 primes × 2 arms). **No CM-specific joint synergy and no within-null firing in any channel,
across discovery + OOS + ladder.** The v3 base scoped null extends to r=4 Semaev, m=4/m=5 combos, μ₂
label, GLV-mixed features, coordinate-pair, and finer interval — now at full v3-equivalent completeness.

## CM-specificity for the CM-only channels — stated explicitly (auditor nit)
For P3_GLV, S-INT, S-XY, S-C5 the feature is CM-only or has no matched non-CM contrast, so "CM-specific"
is **not** established by a CM−nonCM Δ. For a NULL it follows **a-fortiori**: absence of synergy ON the
CM arm ⇒ there cannot be CM-specific *presence* (CM-specificity requires presence on CM). So the verdict
"no CM-specific joint synergy" is valid for these channels via absence-on-CM, not contrast — and this
distinction would matter (leave the headline unearned) only for a *positive*, of which there is none.

## Frontier arms — the bound magnitude travels with the "within null" claim (auditor nit)
S-XY (216 strata) and S-C5 (243 strata) are power+estimability frontier arms: their plants FIRED at
ρ=0.30 (so they are not VOID / power-starved), but the demonstrated power is for **gross** ρ=0.30
effects, and their per-arm floors are large: **MI_min ≈ 4.0×10⁻² (S-XY), ≈ 1.8×10⁻² (S-C5)** (§5 of the
prereg). So their "within null" is honestly a **"detects gross synergy only"** frontier bound `|Δ| <
MI_min(frontier)`, not a fine null — the bound magnitude is stated alongside the claim. P1–P4/S-INT
floors are the tighter `~2–8×10⁻³` (§5).

## Gate status (updated 2026-08-25)
- **`semaev_s4` citation — DISCHARGED, `[CITED — verified against primary text]`.** `citation-verifier`
  read both primary PDFs (Semaev 2004 eprint 2004/031 Thm 1; Kosters–Yeo arXiv:1503.08001 Prop 2.1),
  SHA-256'd, + an independent sympy resultant cross-check: our `S4 = Res_X(S3(x1,x2,X), S3(x3,x4,X))`
  **IS exactly** Semaev's S4, **absolutely irreducible, NO extraneous factor**; the iff
  `S4=0 ⇔ ±P1±P2±P3±P4=O` is exactly the theorem (char≠2,3). Kosters–Yeo Prop 2.2's degenerate cases are
  for *singular* curves — do not apply here. Only hygiene issue: a coincident x-coordinate forces a
  curve-INDEPENDENT trivial S4=0. **GUARD APPLIED** (`draw_sets` + plant, 2026-08-25): skip any tuple
  with a repeated x-coordinate (== distinct-scalar in-interval, since d_i+d_j<2^(b+1)<L ⇒ distinct d ⇒
  distinct x). The discovery tier was **re-run with the guard** to confirm the null is unchanged (curve-
  independent forced-zeros are Δ-canceling across the matched arms, so the null is robust either way) —
  see §Guarded re-run below. Confirmation+ladder predate the guard but are unaffected for the same
  Δ-cancelling reason.
- **μ₂ plant:** FIXED (QR-bit↔J₂ coupling; distinct_planted 1→2, fires monotone) — μ₂ instrument clean.
- **Second independent `experiment-designer` read — DONE (2026-08-25).** Verdict: the null is **EARNED**
  on a well-posed spec across both preregs; no frame defect makes either null trivial. Two low-impact
  disclosure nits (the two sections above) addressed; the GLV CM-only within-stratum null confirmed the
  correct control.
- **Split channels:** r=5 Semaev (S₅) now **pre-registered** (`PREREG_cm_jointset_semaev_r5_v1.md`,
  SPEC ONLY); joint-μ₆ label still untested.

## Guarded re-run (discovery, coincident-x guard applied, 2026-08-25)
Discovery re-run with the guard in `draw_sets`+plant (fresh RNG stream, so an independent sample —
p's are not tuple-comparable to the un-guarded run). **All 7 channels within null, verdict unchanged.**
Per-channel CM p across {541,571,577}:

| channel | CM p (guarded) | read |
|---|---|---|
| P1_S4  | 0.183 / 0.100 / 0.547 | null |
| P2_C4  | 0.342 / 0.706 / 0.161 | null |
| P3_GLV | 0.047 / 0.774 / 0.744 | null (single 0.047, non-reproducing) |
| P4_μ₂  | 0.152 / 0.152 / 0.518 | null |
| S_INT  | **0.0013** / 0.137 / 0.510 | null (marginal — see below) |
| S_XY   | 0.513 / 0.236 / 0.244 | null |
| S_C5   | 0.104 / 0.440 / 0.476 | null |

**The S_INT q=541 p=0.0013 marginal — surfaced, tested, seed-noise.** S_INT (finer-interval label) at
q=541 was **p=0.927** in the un-guarded discovery and is 0.137/0.510 at q=571/577 in *both* runs. An
"effect" that swings from p=0.93 to p=0.0013 on a fresh sample of the same prime, and does not reproduce
at the other two primes, is seed-dependent noise by definition — not a lead. Across all 13 S_INT
measurements (unguarded+guarded discovery, confirmation, ladder) it never reproduces below 0.01 at the
same prime; consistent with the null. **The guard does not change any channel's verdict** — as expected,
since coincident-x forced-zeros are curve-independent and Δ-cancelling across the matched arms.

## Provenance
Exact int/GF(q) signal path (curve arithmetic, x/y, χ₂, χ₃, S₃, S₄ resultant, GLV twisted points
[λ]P=(βx,y), combos, labels, permutation counts). Float only in the MI log₂, ranked against exact
integer within-stratum permutation counts (`# noqa: float`). Curve schedule reused from
`schedules_v1/schedule_A_joint_v1.json` (SHA c533f669…). Seed 20260821. Selftest: S4 vanishes on 60/60
true 4-relations (generic-nonzero otherwise); GLV endomorphism (βx,y) on-curve. Runner + logs archived.
