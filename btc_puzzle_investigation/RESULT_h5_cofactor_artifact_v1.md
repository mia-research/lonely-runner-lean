# RESULT — H-5 resolved: the Semaev CM relation-yield lever is a COFACTOR / subgroup-confinement artifact of non-cyclic j=0 model curves (not a CM lever, not the #E-leak)

**Date:** 2026-08-24
**Author:** ZCode (Claude). Executes the two owed H-5 follow-ups under
`PREREG_h5_factor_isolation_and_orbit_quo_v1.md` (the mandatory experiment-designer gate).
**Runs (frozen, this session):** `h5_followup_run_v1.py` over the frozen schedule SHA `f92cb4bb…`,
24 primes p∈[523,823] (p≡1 mod 3), m=3, |V|∈{4,5,6}, K=25, R_B=8. Raw:
`h5_followup_results_v1.jsonl` (1584 curve-evals). Analyses: `analyze_h5_followup_v1.py`,
`analyze_h5_F2b_primedrop_v1.py` (free arm), `analyze_h5_mechanism_v1.py` (group structure).
**Grade:** `[VERIFIED — mechanism identified, powered, pre-registered]`, scoped to the model primes.
The lever's magnitude is explained by a single structural variable at **Pearson r = 0.96**, all
plants fired, and the effect is null under the corrected sampler.
**Bottom line:** H1 is a **cofactor artifact** — it is present only because the j=0 model curves
are non-cyclic and the sampler used a single generator; it **vanishes at prime-order (cofactor-1)
curves such as secp256k1.** M25/N22 resolvable to **null with an identified mechanism**;
do-not-close #5 discharged (both arms).

---

## 1. Plants (all fired — the test is informative)

| plant | result |
|---|---|
| **C6 pipeline** (reproduce the leaky log's T1_j0) | 0.2074 / 0.4104 / 0.5676 vs log 0.2074 / 0.4094 / 0.5668 — diff <0.001 at every |V|. `quo` = `vector_space_dimension` matches `measure_system` exactly. |
| **C4 negative** (nonCM–nonCM) | null, perm_p 0.76 / 0.79 / 0.88 |
| **+0.5 injected** | detected, mean 0.7074 ≈ T1+0.5, perm_p 0.0000 (n=24 paired test resolves a 0.5 shift) |
| **Orbit-counter** (all-dup→1, all-distinct→3) | pass |
| **Forced-relation** `quo(t)=quo(ζ₃t)=quo(ζ₃²t)` on β-invariant V | pass (q=12,12,12) — confirms the isobaric λ→λT homogeneity the pre-reg used to demote the GLV arm |

## 2. Experiment 1 — factor isolation (pre-committed arms)

| arm (factor) | |V|=4 | |V|=5 | |V|=6 | verdict |
|---|---|---|---|---|
| **E_F1** twist B=1 vs random j=0 twists (control-free) | 0.111 (p=.010) | 0.234 (p=.0005) | 0.331 (p=.0003) | significant, grows |
| **E_F2a** matching rule (bracket-interp vs nearest) | −0.004 (p=.49) | −0.001 (p=.94) | −0.006 (p=.31) | **null** |
| **E_F2b** prime-drop selection (free arm) | −0.052 | −0.110 | −0.132 | **null, negative** |
| **E_F8** whole-group sampling: `T1_underF8` | 0.011 (p=.21) | −0.006 (p=.66) | −0.024 (p=.84) | **lever VANISHES** |
| **E_F8** the j0 gap `Q_gens − Q_randpoint` | 0.204 | 0.407 | 0.599 | ≈ T1_full — it **is** the lever |

Reading: the matching rule (F2a) and prime-drop (F2b) are both null — **the audit's stated
#E-mechanism is refuted** (consistent with `RESULT_h5_V_signature_leak_derivation_v1.md`). Under the
corrected `random_point` sampler the lever is null at every level (`T1_underF8` ≈ 0). And
`E_F8(j0) = Q_j0(gens) − Q_j0(randpoint)` ≈ `T1_full` at all three |V| — the **entire lever is the
j0 single-generator subgroup gap**.

## 3. The mechanism — cofactor n₂, at r = 0.96

`gens()[0]` on a **non-cyclic** curve `E ≅ ℤ/n₂ × ℤ/n₁` (n₂ | n₁) generates only the large cyclic
subgroup (order n₁ = #E/n₂), confining the factor base and target to an index-n₂ subgroup. A smaller
effective group ⇒ more m-tuples sum to the target ⇒ higher `quo`. The cyclic control (n₂=1) has no
confinement. So the lever = the confinement **differential**, quantitatively:

- **j0 (A=0,B=1) is non-cyclic at 24/24 primes; controls cyclic at 22/24.**
- **Pearson( T1_j0(|V|=6), log n₂(j0) ) = 0.962.** Extremes: p=601 j0=(24,24) → T1=1.55;
  p=547/631 (14,42) → T1≈1.34; the n₂=2 cases → T1≈0.1–0.3.
- **The only two negative-T1 primes (p=541, 751) are exactly the two where the control is also
  non-cyclic** ((2,·)) — the differential cancels when both sides carry a cofactor. A perfect
  internal control.
- **E_F1 is the same mechanism:** Pearson( logmean quo, log n₂ ) over the random-B j=0 twists =
  0.960. "B=1 special" just means B=1's twist is more non-cyclic than the average random twist.

The j=0 curves are systematically non-cyclic at p≡1 mod 3 because their CM structure forces rational
torsion — but the yield effect is mediated **entirely by the cofactor** (r=0.96), not by any
CM/μ₆ relation-yield mechanism. The earlier RESULT's named μ₆-multiplicity candidate is superseded:
it is the curve's **group** cofactor, not its automorphism group.

## 4. Experiment 2 — the excess is distinct relations, but subgroup-confined

| |V| | T1 (raw quo) | T2 (S_m-orbit) | D2 = logρ_j0 − logρ_ctrl | perm_p(D2, one-sided ≥0) | ρ_j0 | ρ_ctrl |
|---|---|---|---|---|---|---|
| 4 | 0.207 | 0.338 | −0.130 | 1.000 | 4.99 | 5.69 |
| 5 | 0.410 | 0.536 | −0.125 | 1.000 | 4.88 | 5.53 |
| 6 | 0.568 | 0.686 | −0.118 | 1.000 | 4.83 | 5.44 |

D2 is **negative** (ρ_ctrl > ρ_j0): j0 has *fewer* S_m-permutation duplicates than the control, so
the orbit-reduced lever T2 is **larger** than the raw T1. Per the pre-committed rule (D2≈0 & T2≈T1),
the excess **survives orbit reduction** — it is **distinct usable relations, not permutation
duplicates.** (Non-radical cells — quo≠#variety — are rare: 4/36/50 of 1200; noted as multiplicity.)
Combined with §3: the excess consists of *distinct relations within an artificially confined
subgroup* — real relations, but a subgroup-confinement artifact, not a whole-group yield advantage.

## 5. Verdict against the pre-committed decision rules

- **Exp 1 →** `[artifact — sampling / cofactor]`: the lever vanishes under whole-group sampling
  (E_F8 `T1_underF8` null, powered — the +0.5 plant fires at n=24, floor 0.13 at |V|=4), the #E arms
  (F2a, F2b) are null, and the magnitude is explained by log(cofactor) at r=0.96. E_F1 is the same
  cofactor variable expressed among twists (D5 interaction is resolved *by* the unifying r=0.96, so
  no 2³ escalation is needed).
- **Exp 2 →** the excess is distinct relations (not S_m-duplicates), which — read with Exp 1 — are
  subgroup-confined and therefore not a real whole-group yield lever.

## 6. Cryptographic reading (scoped)

The effect is a **cofactor phenomenon**: relation yield scales as `|V|^m · n₂ / #E`, i.e. n₂×
higher for a curve with cofactor n₂ than for a cyclic curve of the same #E — a well-understood
consequence of a smaller cryptographically-relevant subgroup, not a j=0/CM-specific leak.
**secp256k1 has prime order (n₂ = 1, perfectly cyclic)**, so this mechanism is absent at the target.
The model-scale lever says nothing about secp's security and does not reduce its keyspace — consistent
with N15's "no keyspace reduction" (and it is the correct, mechanism-level reason, not a bare null).

## 7. Reconciliation and dispositions

- **`AUDIT_semaev_v4_method_result_conclusion_v1`:** its H1 **null was correct**, but its stated
  mechanism (one-sided #E-bracket leak) is **refuted** (E_F2a≈0, E_F2b negative). The corrected run's
  null came from **F8 (whole-group sampling)** removing the subgroup confinement, not from #E-bracketing.
- **`RESULT_h5_V_signature_leak_derivation_v1.md`:** its #E-leak refutation is **upheld** (F2 arms
  null here too). Its tentative "H1 rehabilitates / μ₆-multiplicity candidate" lean is **superseded
  (downward correction):** the powered pre-registered test identifies a cofactor sampling artifact,
  not a real CM lever. (This is a tested null with a firing plant and an r=0.96 mechanism — not a
  pre-deflated one; running the experiment the pre-reg designed was what turned the lean into a verdict.)
- **M25 / N22:** the H1 leg resolves to **`[null — cofactor/sampling artifact, mechanism identified,
  model scale]`**; no longer a live "strongest positive." H2 (x-closure, do-not-close #4) is untouched
  and still owes its order-3 structure-matched control.
- **Do-not-close #5:** discharged — both the derivation arm (RESULT v1) and the mechanism arm (this)
  are delivered.

## 8. Owed / provenance

- The whole finding is `[VERIFIED — scoped]`, model primes only; no 256-bit, ECDLP, or key claim.
- Folding this + RESULT v1 + the N16 discharge (`NOTE_v14_item9_n16_state_v1.md`) into the ledger is a
  master-promotion step → triggers the `compile-diff` gate (a v15/addendum), not done here.
- Post-run audit vs the pre-reg: statistic unchanged, no silent filtering, plants fired, power & scope
  on every number, conclusions taken from the pre-committed cells. The only registered deviation:
  `measure_orbit` skips `measure_system`'s unused `d_ff`/`d_solv`/`d_gb` diagnostics (≈100× faster);
  `quo` is byte-identical (C6 confirms), so the deviation is verdict-neutral.
