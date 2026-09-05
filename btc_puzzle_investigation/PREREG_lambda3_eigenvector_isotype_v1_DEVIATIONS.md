# DEVIATIONS — Arm 0 run vs `PREREG_lambda3_eigenvector_isotype_v1.md`

**Run:** `arm0_gate_lambda3_v1.py`, 2026-07-21 · **Result:** `RESULT_lambda3_arm0_gate_v1.md`.
Every deviation disclosed whether or not it is wrong (prereg header requirement). None changes a
pre-committed outcome cell; the branch reached (GATE-FAIL/redefine) is one of the four pre-committed
Arm-0 branches.

## D1 — decision made on the powered set, not the committed 12 (WITHIN the power budget)
Prereg Arm 0 named "the 12 smallest p>400, #E prime" (n∈[397,1303]) as the primary list, **with a
pre-committed power budget**: "if measured σ_gap at p≤5000 exceeds measured Δ, extend upward to
prime-order p up to ~10⁵." The firing calibration gave n*=2500; **all 12 committed primes have n<n***
(underpowered). Per the budget, the verdict was decided on the **powered set** — the 8 smallest
prime-order curves with n≥n* (p=2503…3571). The 12 committed were still run and reported as
underpowered (not decisive). Deviation: the *specific* powered selection (first 8 with n≥n*) is a
refinement of "extend upward," disclosed here.

## D2 — n* understates the n needed for the REAL gap (material interpretive caveat)
The prereg's Arm-0 power sizing borrowed DRILL-01's C_T band as an order-of-magnitude (flagged there).
Implemented: firing calibrates n* empirically as the smallest n where the SEP plant (gap **0.153**)
resolves S>0.9 → n*=2500. **But the real subdominant gaps are ~0.02** (≈7× smaller), and eigenvector
resolution scales `n ∝ 1/gap²`, so a real *individual* vector would need n~10⁵–10⁶. Consequence: the
gate is underpowered for the real gap even on the "powered" set; the honest reading is
**near-degenerate/unresolved at accessible n**, reported alongside the GATE-FAIL branch. This caveat is
stronger than the prereg anticipated and is disclosed in the RESULT.

## D3 — firing construction stronger than "rank-1 perturbation opening gap δ"
Prereg §Arm 0 firing said "M + rank-1 perturbation opening a known gap δ." Implemented instead: (a)
**analytic exact operators** — SEP (holding-chain, distinct real spectrum, gap 0.153) and DEGEN
(C₁⊗C₁, exact degeneracy 4.4e-16) — validating `gaps_flags`/`subspace_overlap` directly; then (b) a
**sampled n-sweep** for the power threshold. This satisfies the firing intent (positive control fires:
SEP resolves to S>0.9; negative control: DEGEN reads S_sub≫S) more cleanly than a single δ. Disclosed.

## D4 — `subspace_overlap` bug fixed mid-build (implementation, pre-data)
First implementation summed non-orthonormal `uᵢuᵢᴴ` over the (non-normal M's) eigenvectors → gave
`S_sub>1` (up to 2.19). Fixed to a **QR-orthonormalized** basis: `S_sub=‖Q_Aᴴ Q_B‖_F/√dim ∈[0,1]`.
Caught in the firing smoke test **before** any real-prime verdict. Corrected implementation, not a
data-dependent choice.

## D5 — S_sub added as the gauge DISCRIMINATOR (refinement of the S<0.9 rule)
Prereg keyed GATE-FAIL(degenerate) on "individual S<0.9." Implemented additionally reports S_sub and
uses **S_sub≫S** as the signature of "gauge within a (near-)stable subspace" vs "pure noise." At the
real primes both S<0.9 and S_sub<0.9 (the cluster is >2-dim), so the pair-subspace is itself not clean
— which is *why* the RESULT redefines to the full slow band (dimension TBD), not the {v₂,v₃} pair.
Disclosed as a refinement that made the object redefinition sharper.

## D6 — branch = GATE-FAIL(degenerate/gauge); ABSTAIN caveat attached
The literal pre-committed condition "Δ₂₃<3σ_gap OR S<0.9" holds 8/8 → GATE-FAIL(degenerate/gauge),
which redefines the object to the slow eigenspace. The ABSTAIN branch ("noise band too wide to resolve
the gap at accessible n") **also** applies (D2). The operational conclusion is identical (do not
characterize the individual vector; move to the subspace), so GATE-FAIL/redefine is reported with the
ABSTAIN-flavored power caveat explicit. No outcome cell reinterpreted after data.

## D7 — bootstrap draws, K-convergence scope (minor)
`B=200` in `gate_one` (as prereg); `B=80` in `k_convergence` for speed. K-convergence computed at the
top powered prime (p=3571) only (prereg permits "the largest well-sampled prime"). The `kconv_ok`
boolean fired True (slowing test) but the values **drift 0.862→0.651** across K=4→10; the RESULT
reports the values, not the boolean, and treats the drift as corroborating (the "85%" is K-inflated
too). Disclosed.

## D8 — Arm 1 ran gauge-free on the SUBSPACE via an exact integer quadratic form (not per-vector)
PREREG Arm 1 phrased W_cov via per-vector isotypic energies `‖P_kφ‖²`. Because Arm 0 made the
individual vectors gauge, Arm 1 uses the **basis-invariant** form `W_cov(V)=⅔−(1/3m)tr((UᴴDU)⁻¹
Uᴴ(N₁+N₂)U)` with exact integer `N_k,D` (β-cell geometry). Re-derived; reduces to the PREREG §0 formula
at m=1. Strengthens the prereg (removes the gauge dependence), disclosed.

## D9 — NULL-MISMATCH caught and corrected mid-run (the load-bearing Arm-2 fix)
The first Null-A (unrestricted random subspace) flagged a `W_cov(m=15)` "excess" at **6/6** primes.
This was a **phantom**: the non-Perron object excludes the stationary vector π, and `w_cov(π)=0`
(purely invariant), so `W_cov(non-Perron)=(16/15)W_cov(full)` — a rescaling the unrestricted null does
not carry. Corrected to a **π-orthogonal matched null**; the excess **vanishes at every m**. This is
the `feedback_test_on_both_sets` / v17 control-row lesson (the null must carry the object's symmetry).
The corrected (matched-null) result — **no covariant excess** — is what the RESULT reports. Disclosed
as the load-bearing correction of this arm.

## D10 — only the full non-Perron space is stably defined; small-m gauge (confirms Arm 0)
PREREG Arm 1 decides "on the stable m-range S_sub>0.9." Empirically only **m=15** (S_sub=1.0, always)
and borderline **m≈12** (S_sub≈0.88–0.93) are stable; m=1..8 are gauge-unstable (S_sub 0.005–0.80).
So the "stable range" is effectively the whole non-Perron space, and the slowest-mode covariance
gradient (the v25 claim) is unresolved at accessible n. Reported as scoped, per the Arm-0 power caveat.
Null-B (i.i.d.-walk operator) was not separately run: the random-subspace null (Null-A analog) is the
stronger "is the slow span special" test, and it already shows no excess. Disclosed.

## Unchanged from prereg (for the record)
NO-FLOAT guard passes (`OK`); labels/counts exact-int; eigendecomposition/statistics are the documented
carve-out (per-line `# noqa: float`). Object = the K=4 walk operator M and its subdominant spectrum.
Seed 20260721. Scale banner honored (p≤3571; zero power at 2²⁵⁶).
