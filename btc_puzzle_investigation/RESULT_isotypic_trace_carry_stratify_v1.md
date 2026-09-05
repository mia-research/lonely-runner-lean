# RESULT — γ: carry-stratification of the isotypic trace is UNDERPOWERED at p=43 (ABSTAIN, B1); the carry is constant on the rational-lift locus

**Date 2026-08-18.** Executes `PREREG_isotypic_trace_carry_stratify_v1.md` (FROZEN, SHA-256
`fb8283e018c18a2966b28cc1b58cddd5d361351f746c06cf6b97c314f7e2f84a`). Tests intersection γ of
`ANALYSIS_intersection_leads_v1.md`: does the public carry class `c([d]G)` stratify the isotypic trace
`ℓ(d)` into within-class affine structure? Script: `scratchpad/cubic_coherence/gamma_run_v1.py`
(**fully exact integer — no float anywhere**). Data: `ℓ(d)` from `trace_openq_test.sage` (Sage 10.9,
p=43), `x([d]G)` from Sage (G=(7,7), ord 31), carry from the Eisenstein lift with `π=7+ω`
(`A_SP=7,B_SP=1,BETA=36`, the p=43 analog of the secp construction; `A_SP,B_SP` = components of `π`,
norm `A²−AB+B²=p`, verified). **Grade `[ABSTAIN — underpowered, B1]`.** p=43 only; nothing transfers.

## Outcome: B1 (ABSTAIN — not powered)

The frozen §0 structure report (printed before any fit):
- **FS1** point counts by carry: **{0:15, +:0, −:0}** — all 15 rational-lift d are carry-0.
- **FS2** GLV orbits (M=5, all size 3): {3,13,15}, {4,7,20}, {6,26,30}, {12,21,29}, {17,22,23}.
- **FS3** orbit counts by carry: {0:5, +:0, −:0}. **FS4** `N_perm = 1`.
- **FS5 integrity BOTH PASS:** (a) carry is orbit-invariant (all 3 members of each orbit share carry 0);
  (b) ℓ orbit-covariance `ℓ(25^t·rep)=k^t·ℓ(rep)` holds with a single `k∈{1849,587}` per orbit.
- **Power gate:** P1 (some class m≥3) **True** (m0=5); P2 (`N_perm≥20`) **False** (`N_perm=1`).

Per the frozen decision rule → **B1: ABSTAIN.** The public carry is **constant (0)** on the entire
rational-lift dataset, so there is only one carry class and **no stratification is testable** — there is
nothing to permute. The `experiment-designer` spec anticipated this exact degeneracy ("given the
3/4:1/8:1/8 law this will almost surely ABSTAIN"); the pre-registration pre-committed the outcome, and
the gate fired as designed.

## Why (and why it is not a bug or a null)

The carry construction is **sound and non-degenerate** at p=43: over all `X∈[1,42]` the distribution is
**{0:36, +1:3, −1:3}** — skewed from the continuum ¾ toward 6/7 at this tiny prime, but genuinely
three-valued (6 non-zero-carry points exist). By orbits: 12 of the 14 orbits are carry-0. The 5
rational-lift orbits all landing in carry-0 is **~40% likely by chance** (`C(12,5)/C(14,5)=0.40`) — a
non-event, not a signal. So the test simply has no contrast to measure at p=43.

**This is NOT a null and NOT a positive** (anti-suppression, per spec): it does **not** close whether `ℓ`
carries partial-`d` information beyond the orbit label, and it does **not** say "carry does not handle
`ℓ`." It says only: **at p=43 the carry is constant on the accessible (rational-lift) d, so γ cannot be
run.** The verdict is owed a **larger `A_new`** (a bigger `p≡1 mod 3` with `y²=x³+7`), where more carry
classes would populate — **currently BLOCKED** by the Sage/Singular function-field-Jacobian hang above
p=43 (recorded owed, 2026-08-18). The test logic + machinery are ready to run unchanged the moment a
faster `A_new`/`ℓ`-realization exists.

## Low-confidence observation (flagged, not claimed)

The **rational-lift locus** (the d for which `S([d]G)` lifts rationally to `A_new`) is **entirely within
the carry-0 locus** at p=43 (15/15). Given 12/14 orbits are carry-0 anyway, this is ~40% by chance and
is **NOT established** — but "rational-liftability ⊆ carry-0" is a concrete, cheap thing to check at a
larger `A_new`, where both loci have more room. If it held with power it would be a real link between the
`A_new` cover's lift geometry and the public carry (O2↔O3 in the intersection map). Noted as a probe, not
a finding.

## Disclosed clarification (frozen pre-data, not a deviation affecting the verdict)
The spec's FS2 wrote "orbit … mod 1893"; the scalar `d` lives mod `nE=31` (the order of G), where `λ=25`
has order 3 — the orbit is `{d,25d,625d} mod 31`. This obvious intent was disclosed in-file **before**
the SHA was computed (bracketed note in FS2), so it is part of the frozen spec. The GLV action was
independently verified on the data (`x([25d]G)=36·x([d]G) mod 43`, e.g. d=3: `36·29 mod 43 = 12 =
x([13]G)`).

## Scope
p=43, this `A_new` (order 1893), these 15 rational-lift d. No transfer to any larger `A_new` or to secp.
An ABSTAIN scoped to p=43; the object (does the carry stratify `ℓ`?) remains **open**, owed a larger `A_new`.
