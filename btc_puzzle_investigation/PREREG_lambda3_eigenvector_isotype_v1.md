# PRE-REGISTRATION — Characterization of the λ₃ cell-walk eigenvector's μ₆-isotypic content — v1

**Written 2026-07-21, BEFORE any operator eigenvalue/eigenvector data for this drill is seen.**
This is a test specification, not a result. It fixes the object, statistic, matched control, firing
check, power, scope, exactness, and every falsification branch in advance. Post-run, audit the run
against this file in `PREREG_lambda3_eigenvector_isotype_v1_DEVIATIONS.md`; every deviation is
disclosed whether or not it is wrong.

**Type:** CHARACTERIZATION (Anomaly-Drill protocol, `feedback_anomaly_drill_protocol_2026_07_17`) —
**not** a leak test. Output is a symmetry-type / subspace characterization plus bounded magnitudes
with power; never a verdict, never a closure (drill rules 1, 5, 6).

**Governs:** re-run + extension of `conservation_spectrum_v2.py::test_a_eigenvector_mu3`; the measured
claims in `masked_structure_findings_v25.md` (Correction 1) and `_v27.md` (#1).

**Grades:** `[PROVED]` exact/algebraic · `[VERIFIED]` exact per-prime, scoped · `[EMPIRICAL]`
float-spectral ranked vs matched null.

**Provenance:** designed by the `experiment-designer` agent in context isolation; the load-bearing
algebra below was independently re-derived by the coordinator before this file was written (see §0).

---

## 0. COORDINATOR SPOT-CHECK (done before writing; trust-but-verify, CLAUDE.md §2)

**Load-bearing identity — VERIFIED by independent re-derivation.** With
`A = Σ_S φ(βx)·conj(φ(x)) / Σ_S|φ(x)|²` (the quantity `test_a_eigenvector_mu3` already computes) and
the μ₃ projectors `P_k φ(x) = ⅓ Σ_{j} ζ^{−kj} φ(β^j x)` (ζ=e^{2πi/3}):

- Set `c_m = Σ_S φ(β^m x) conj(φ(x))/Σ_S|φ|²`. Then `c_0 = 1` and `c_2 = conj(c_1) = conj(A)`
  (sub y=β²x, β order 3, S is β-invariant since (βx)³+7 = x³+7).
- `w_k = ‖P_kφ‖²/‖φ‖² = ⅓ Σ_m ζ^{−km} c_m` (each m occurs for 3 of the 9 (j,j′) pairs).
- ⇒ `w₀ = ⅓(1 + 2·Re A)`, `w₁ = ⅓(1 − Re A + √3·Im A)`, `w₂ = ⅓(1 − Re A − √3·Im A)`, and since
  `Σ_k P_k = I` (orthogonal) ⇒ `Σ_k w_k = 1` ⇒ **`w_cov = w₁ + w₂ = 1 − w₀ = ⅔(1 − Re A)`.** ✓

This binds the entire prereg to the committed code: the covariant weight is a deterministic function
of `A`, and of the code's printed `(|A|, arg A)` via `Re A = |A|·cos(arg A)`.

**Swap invariance — VERIFIED.** Using β² instead of β gives `A′ = conj(A)` ⇒ `Re A′ = Re A` ⇒ `w_cov`
unchanged, `w₁ ↔ w₂`. So `w_cov` is the convention-independent object; individual `w₁, w₂` are not.

**Real/complex tension — CONFIRMED REAL, deferred to Arm 0.** `w₁ = w₂ ⟺ Im A = 0 ⟺ arg A ∈ {0°,180°}`,
which holds **iff v₃ is a real eigenvector**. The code's docstring expects `arg A ≈ ±120°` (a *complex*
covariant mode, e.g. `φ(βx)=ζφ(x) ⇒ A=ζ`). v25's "w₁=w₂ always" and the code's "±120°" are mutually
exclusive; which holds is exactly the Arm-0 real/complex flag. **The successor must not cite "w₁=w₂
always" as established until Arm 0 resolves it.**

**Two refinements folded into the arms below:**
- (R1) The FIELD/CURVE identity `Σ_S|ψ|² = ½(FIELD+CURVE)` uses `𝟙[x∈S] = ½(1+χ₂(x³+7))`, which
  under-weights the ≤3 zero-abscissae (`x³+7≡0`, χ₂=0) that the code *includes at full weight*
  (`legendre==0` is not skipped). The identity is exact only after adding back
  `½·Σ_{χ₂=0}|ψ|²`. Implementation must handle the ≤3 zero-points explicitly (Arm 1).
- (R2) Null-B (i.i.d. draw from S) is marginal-matched **in expectation**; Null-A matches the exact
  empirical cell-marginal. Keep both as the complementary pair (Arm 2).

---

> ## ⚠ SCALE BANNER (total, per drill rule 3)
> Every number is at **p ∈ [400, ~10⁵]** (≈ 2⁹ … 2¹⁷). secp is p ≈ 2²⁵⁶ — **≥ 239 binary orders
> above the top of this range. Nothing here has any power at 2²⁵⁶.** Every conclusion is scoped to
> `y²=x³+7`, `p≡1 mod 3`, `n=#E(F_p)` prime, the first-generator point orbit, K∈{4,6,8,10}, and the
> stated p-list. It does **not** reach secp.

---

## 1. OBJECT

Let E: y²=x³+7 over F_p, p≡1 mod 3, n=#E prime, G the first generator (`curve_gen`). Point orbit
x_d = x([d]G), d=1..n−1. Fix K; cell(x,K)∈{0,…,K²−1} is the exact (Fraction) Eisenstein reduced-basis
K×K bin (`cell_fn`). **M** = row-stochastic K²×K² operator of the empirical d→d+1 transition
L_d→L_{d+1} where L_d=cell(x_d,K) (`transfer_matrix`; exact rational entries = integer counts /
integer row sums). |λ₁|≥|λ₂|≥|λ₃|≥…; v_r the r-th eigenvector (`np.linalg.eig`). Pullback
φ_r(x) = v_r[cell(x,K)], a function of the public x on the support S = {x∈F_p : χ₂(x³+7)∈{0,+1}}
(the code's `legendre((x³+7)%p,p) ≥ 0`).

**The object being characterized:** the μ₆-isotypic content of φ₃, where the **field** group
μ₆ = ⟨τ:x↦βx⟩(order 3, β=`beta_of(p)`) × ⟨ν:x↦−x⟩(order 2) acts multiplicatively on x. This is the
field μ₆ of `_field_bigrading_v1.py` / v35 §2 — strictly larger than Aut(E)'s reach on x (μ₃ only).
The reported "85% μ₃-covariant, broadband, no closed form" is a claim about *this* object.

**Tautology disclosure (feedback_residue_vs_component_tautology).** φ₃ is built from the cell-walk,
which is built from the orbit of d. Therefore **no arm correlates φ₃ against functions of d.** Arms 0–2
characterize φ₃ as a function *on cells / on x* under the μ₆ action — disjoint-construction from the
d-index. Any d-axis object (the v27 #1 DFT/overlap) is **characterization-only** and load-nothing:
φ₃(x)=v[cell(x)] is a bounded-degree lattice readout of public x, already floor-bounded by KS/closure
(`POSITIVE_FINDINGS_MASTER_v4.md` Part VI), so a d-axis correlation is inadmissible as a leak statistic
by construction.

**Not the same operator as C_T.** The addition-law operator C_T=C₁⊗C₁ has λ₂=λ₃=1/3 exactly,
θ-independent `[PROVED]` (master §X.10, `ct_shear_prediction_v1.py`). This d→d+1 **walk** operator M is
a **different construction**; the spec does not assume it shares that degeneracy — Arm 0 **measures**
M's gaps. (The C_T degeneracy is *why* Arm 0 exists: any near-degeneracy in M makes "the λ₃
eigenvector" gauge.)

---

## 8. EXACTNESS / NO-FLOAT carve-out (`btc_puzzle_investigation/CLAUDE.md`)

**Exact (int / Fraction / Z[ω]) in the signal path:** cell labels; transition counts and row sums
(M's entries are exact rationals); χ₂(x³+7) via QR table; the τ (x↦βx) and ν (x↦−x) actions on x; all
projector index arithmetic; the FIELD and CURVE sums applied to the exact known-bidegree control
readouts (Z[ω], as in `isotypic_selection_rule_v1.py`). The split identity Σ_S = ½(FIELD+CURVE)
**+ the R1 zero-abscissae correction** is verified as an exact integer identity per prime.

**Documented float carve-out (analytic size only, no key in path — identical to
`conservation_spectrum_v1/v2`, `isotypic_selection_rule_v1`):** (i) the eigenvector v_r (spectral
display of the exact-rational M); (ii) ζ=e^{2πi/3} in P_k when applied to the *float* vector v_r;
(iii) energies |P_{(i,k)}φ₃|². These enter **only** as monotone statistics ranked against the matched
null (Arm 2) — **never as a threshold on data**. The verdict is an integer-count rank p-value. No key,
(n,k,D), or target is in the path (the object is v_r; p≤~10⁵). Run `check_no_float.sh` /
`check_no_float.py` on the sweep script's signal-path functions before the run.

---

## Arm 0 — GATE: is "the λ₃ eigenvector" well-defined? (runs first; can redefine the object)

**Statistic.**
- Modulus gaps Δ₂₃=|λ₂|−|λ₃|, Δ₃₄=|λ₃|−|λ₄| of M.
- **Real/complex flag:** |Im λ₃|, and whether {λ₂,λ₃} or {λ₃,λ₄} form a conjugate pair (then
  |λ|-degeneracy is exact, v complex, defined up to phase). *(Resolves the §0 w₁=w₂ vs ±120° tension.)*
- **Noise band σ_gap:** recompute M on the two orbit halves d∈[1,⌊n/2⌋] and [⌊n/2⌋,n−1], and on B=200
  block-bootstrap resamples of the transition-count matrix; σ_gap = spread of Δ₂₃, Δ₃₄; σ_vec via
  eigenvector overlap.
- **Eigenvector stability** S = |⟨v₃^(halfA), v₃^(halfB)⟩| (and full-vs-jackknife). For a
  complex/degenerate cluster, use the **subspace** overlap S_sub = ‖Π^(A)Π^(B)‖_F/√(dim) of the
  orthogonal projector Π onto the near-degenerate slow cluster (basis/gauge-independent — a trace).
- **K-convergence** of w_cov (Arm 1) at K∈{4,6,8,10}: successive |w_cov(K+2)−w_cov(K)|, assessed
  **only** on (K,p) cells with n/K²≥20 samples/row (under-sampled cells flagged and excluded —
  disclosed, not silent; the "146-transition operator is noise" guard applied to K).

**Carve-out:** gaps/overlaps are float-spectral of exact-rational M, ranked against the resample band.

**Matched control + firing.** The noise band *is* the control (half-orbit + bootstrap + the Arm-2
μ₃-preserving surrogate's gap distribution). **Firing:** build M_plant = M with a rank-1 perturbation
opening a *known* gap δ between positions 2 and 3; the gate must report Δ₂₃≈δ and S≈1 for δ ≫ σ_gap,
and Δ₂₃ within σ_gap (no false gap) for δ=0. If the gate cannot recover a planted δ, Arm 0 is
uninformative — stop.

**Power/sample.** Pre-committed prime list: the 12 smallest p>400 with p≡1 mod 3, p∉{2,3,7}, n=#E
prime (deterministic; skipped-for-n-composite counts reported per the silent-filter rule); spans
p≈[433, ~5000], n≈[400, 5000]. Order-of-magnitude sizing (from DRILL 01's C_T band
|λ₂−λ₃|_noise≈9.4·n^{−0.584} — **flagged: a different, 9-state operator; used only to size the range,
the actual band is measured**): expected gap noise ≈ 0.28 (n=400), 0.16 (n=1051), 0.10 (n=2503), 0.065
(n=5000). A gap Δ₂₃ is resolvable at these primes only if it exceeds ≈3σ_gap ≈ 0.2–0.3 at the small
end. **Pre-committed power budget:** if measured σ_gap at p≤5000 exceeds measured Δ₂₃, extend the list
upward to prime-order p up to ~10⁵ (still ≪2²⁵⁶); if still unresolved, the object is redefined (below).

**Scope.** The p-list, K∈{4,6,8,10}, this M, first generator. Not 2²⁵⁶.

**Falsification / pre-committed cells.**
- **GATE-PASS** — Δ₂₃,Δ₃₄ > 3σ_gap at ≥ most primes AND S>0.9 AND stable real/complex character AND
  w_cov K-converges (|w(10)−w(8)|<|w(6)−w(4)| and <0.1): "the λ₃ eigenvector" is a well-defined object
  at the licensed n; proceed to Arm 1 on the **individual vector** v₃.
- **GATE-FAIL (degenerate/gauge)** — Δ₂₃ or Δ₃₄ < 3σ_gap, OR {λ₂,λ₃}/{λ₃,λ₄} a conjugate pair, OR
  S<0.9: the individual vector is gauge; **REDEFINE the object (pre-committed branch, not a failure)**
  to the slow eigenSPACE V_slow = span of the near-degenerate cluster; the Arm-1/2 object becomes the
  **TOTAL** covariant weight of its projector Π: W_cov = Σ_{k∈{1,2}}‖P_kΠ‖²_F/‖Π‖²_F
  (basis-independent). **The individual numbers 0.48/0.85 are retracted as gauge at these p**; only the
  space total is characterized.
- **GATE-FAIL (K-drift)** — w_cov does not converge on well-sampled cells: the "85%" is a
  coarse-graining artifact of K=4; report w_cov(K) as a K-dependent curve, no single covariant weight
  licensed; proceed to Arm 1 reporting the *trend*, not a value.
- **ABSTAIN** — noise band too wide at all accessible n (≤~10⁵) to resolve the gap: report the band and
  the n needed (power budget); no well-definedness verdict. Abstention = "the individual/space
  distinction is unresolved at n≤10⁵," scoped, **not** a closure.

---

## Arm 1 — Full μ₆ isotypic decomposition + FIELD/CURVE split of the well-defined object

**Statistic.** Projectors on x: P_k φ(x)=⅓Σ_{j=0}^2 ζ^{−kj} φ(τ^j x) (μ₃, k∈{0,1,2}); Q_i
φ(x)=½(φ(x)+(−1)^i φ(νx)) (field parity, i∈{0,1}); P_{(i,k)}=Q_iP_k. Six weights over set X:
w_{(i,k)}^X = Σ_X|P_{(i,k)}φ|²/Σ_X|φ|². Covariant weight w_cov^X = 1 − Σ_i w_{(i,0)}^X.

**Exact link to the committed statistic (VERIFIED §0).** `test_a` outputs A = Σ_S φ(τx)conj(φ(x))/Σ_S|φ|².
By construction A = w₀+ζw₁+ζ²w₂, hence exactly `w_cov^S = ⅔(1 − Re A)`, `w₀=(1+2Re A)/3`,
`w₁=(1−Re A+√3 Im A)/3`, `w₂=(1−Re A−√3 Im A)/3`. New content of Arm 1: (a) the field-parity split i
(μ₆, not μ₃), and (b) the FIELD/CURVE split.

**The mandatory FIELD/CURVE split (drill rule 9; `isotypic_selection_rule_v1.py`).** φ₃ is a function
of x alone; with 𝟙[x∈S]=½(1+χ₂(x³+7)) **plus the R1 correction for the ≤3 zero-abscissae**:
Σ_S|ψ|² = ½(FIELD[ψ]+CURVE[ψ]) + ½Σ_{χ₂=0}|ψ|², FIELD[ψ]=Σ_{F_p}|ψ|², CURVE[ψ]=Σ_{F_p}|ψ|²χ₂(x³+7).
Define f_FIELD = FIELD[P_covφ]/FIELD[φ] (pure-lattice covariant fraction, **zero curve content**) and
w_cov^S (curve-support covariant fraction). Implementation verifies the corrected identity to the
integer per prime before use.

**Falsifiable hypotheses:**
- **H_FIELD** (lattice-generic / Cap-Law inert-lens, θ-independent): f_FIELD ≈ w_cov^S — covariant
  weight survives with the χ₂ twist removed; a pure-lattice fact of the cell readout, present whether
  or not x is on E.
- **H_CURVE** (Weil): f_FIELD ≪ w_cov^S — removing χ₂ collapses the covariant weight; the covariant
  energy is carried by CURVE[P_covφ], a Weil-scale sum (|CURVE| ≤ ‖·‖_W·2√p). "The broadband/no-
  closed-form covariant residual is the CURVE part," made decidable.
- **θ-independence sub-test:** recompute f_FIELD under an alternate reduced-basis orientation and a
  second p at the same residue class; H_FIELD ⇒ f_FIELD θ-invariant (Cap-Law lattice).

**Carve-out.** v₃ float; P_{(i,k)} energies float, ranked vs Arm-2 null. The split identity and the
known-bidegree controls are exact Z[ω].

**Matched control + firing.** *Implementation firing (exact):* the corrected identity must hold to the
integer at every prime. *Projector firing (exact, zero-float):* a known **pure-covariant** readout
χ₃(x)=ω^{ind(x)} (field bidegree (·,1)) must return w_cov=1; a known **invariant** readout
(constant → 0; nrm(x)=‖eis(x)‖² → μ₃-invariant → 0) must return 0 — through the same P_k pipeline. If
these do not fire exactly, the isotypic machinery is broken — stop. *Statistical control:* Arm 2.

**Power/sample.** Same p-list + K-set. The FIELD/CURVE split is an **exact** sum over F_p (no sampling
noise); noise enters only through v₃ (Arm-0 stability S). If GATE-PASS, the split attributes cleanly;
if GATE-FAIL, run the split on Π (stable). Discriminator resolvable when |f_FIELD − w_cov^S| exceeds
the Arm-2 null band (O(0.05–0.1) at n≈2503).

**Scope.** p-list, K-set, this M. Not 2²⁵⁶.

**Pre-committed cells.**
- **H_FIELD confirmed** (f_FIELD ≈ w_cov^S within null, θ-invariant): the "85% μ₃-covariant λ₃ vector"
  is a **Cap-Law inert-lens lattice fact, θ-independent, zero curve content** — connects to v35 §1a
  and the frame-operator ¾−½=¼ lattice geometry. Report the full 6-sector μ₆ table (which (i,k) carries
  φ₃'s energy). A POSITIVE characterization (a named lattice object), not a dismissal.
- **H_CURVE confirmed** (f_FIELD ≪ w_cov^S; CURVE carries covariant energy): the covariant residual
  **is the CURVE(Weil) part** of the v35 split; magnitude Weil-bounded; broadband because Weil sums are
  broadband. Live characterization: which cover / cohomological piece (hand to Part VII machinery).
  Stays open with a sharper law + bound, not closed.
- **MIXED** (both material): report both fractions + the 6-sector table; the object is part-lattice
  part-Weil — name both parts and their magnitudes, neither dismissed.
- **GATE-FAIL upstream:** same three sub-branches on Π's W_cov (space total); individual weights
  retracted.
- **ABSTAIN:** if the well-defined object's covariant weight is itself within the Arm-2 null at every
  K,p, there is no covariant excess to attribute — report the band + power; abstaining on
  FIELD-vs-CURVE ≠ closing the object (feedback_prereg_abstention).

---

## Arm 2 — Matched μ₃-preserving control on the covariant weight (with firing)

**Statistic.** Rank p-value of the real covariant weight w_cov^{real} (Arm 1, over S; or W_cov if
GATE-FAIL) within the distribution of w_cov over B=200 matched-null draws per prime, per K. Report
integer rank count (#{null ≥ real}/B) — **no float threshold**. RNG seed fixed **20260721**.

**Matched controls — both preserve the cell-marginal and the μ₃ cell-relation; NEITHER is a plain
shuffle.**
- **Null-A (marginal-matched random operator):** a random row-stochastic K²×K² matrix whose stationary
  distribution equals the *exact* empirical cell-marginal π, with no arithmetic transition structure
  and no privileged μ₃ direction. Its λ₃-vector covariant weight = "generic operator with this
  marginal" band. Tests whether w_cov is a marginal artifact.
- **Null-B (μ₃-geometry-preserving surrogate):** replace the arithmetic x-sequence {x_d} with {x′_d}
  drawn i.i.d. uniform from the actual curve x-support S (seeded), same length; rebuild M′. Preserves
  the cell-marginal (**in expectation — R2**) AND the exact x↦βx cell geometry and lift (τ acts on real
  x-values, cell(βx) computed identically) while destroying only the P→P+G arithmetic walk. The tight
  matched null — μ₃ geometry intact by construction, so it cannot produce the symmetry-breaking phantom
  (the 6–7σ soft-shadow failure mode, feedback v17 / test_on_both_sets).

Excess over Null-A = "beyond a generic operator with this marginal"; excess over Null-B = "beyond the
lift/μ₃ geometry — genuinely arithmetic."

**Firing check — mandatory, both directions.**
- **Positive plant:** inject a synthetic x′-sequence whose λ₃ eigenvector is a known μ₃-covariant
  target with w_cov=w* (e.g. 0.9); the full Arm-0→1 pipeline must recover w_cov≈w*, and BOTH nulls
  must sit ≪ w*.
- **Negative plant:** inject a μ₃-invariant-structured sequence (w*=0); the pipeline must return
  w_cov≈0 (must not manufacture covariant weight), nulls ≈ same.
If either plant fails, the statistic is uninformative — **stop, no covariant-weight conclusion
licensed.**

**Carve-out.** π exact rational; multinomial draws are the surrogate (seeded RNG — standard null
carve-out); w_cov float ranked; verdict = integer rank.

**Power/sample.** B=200 ⇒ rank resolution 1/200=0.005. Null band width measured (scales with n;
≈O(0.05–0.1) at n≈2503). Detectable covariant **excess** = w_cov^{real} above the 99th percentile of
both nulls, resolvable if w_cov^{real} − median(null) ≳ 0.1 at n≈2503 (tighter at larger n via the
power budget). Same p-list + K-set.

**Scope.** p-list, K-set, this M. Not 2²⁵⁶.

**Pre-committed cells.**
- **Real excess** (w_cov^{real} > 99th pct of BOTH nulls at ≥ most primes, K-convergent): a real
  μ₃-covariant excess in the λ₃ vector/space — hand to Arm 1's FIELD/CURVE split to name it (lattice
  vs Weil).
- **Within Null-A only** (real ≈ Null-A): the "85%" is a **marginal artifact** — any sequence with this
  cell-marginal gives it; NOT eigenvector-specific structure. Retract "λ₃ is predominantly
  μ₃-covariant" as an eigenvector statement; restate as a marginal statement. Scoped null, band + power
  reported (a magnitude, not "no structure" — drill rule 1).
- **Within Null-B, above Null-A:** the covariant weight is forced by the μ₃/lift cell geometry (not the
  arithmetic walk) — a lattice fact; θ-tested via Arm-1 FIELD (expected H_FIELD).
- **Firing FAILS:** measurement uninformative; report and stop.
- **ABSTAIN:** real and nulls overlap within resolution at all accessible n; report band + n-needed
  (power budget). Abstention = "covariant weight is at the μ₃-matched-null level at n≤10⁵," scoped, not
  a closure.

---

## (a) Reproduction flags — measured claims vs the committed code

1. **w₁+w₂ = 0.60→0.85 is NOT directly output by `conservation_spectrum_v2.py`.** Committed `test_a`
   outputs only (|λ|, |A|, arg A). v25 Correction 1's numbers came from a re-run of the v2 internals
   with the isotypic decomposition added — a modified script not on disk under that name. **However**
   w_cov^S = ⅔(1−Re A) = ⅔(1 − |A|cos(arg A)) is reconstructible from the committed output; the
   specific 0.48/0.45/0.54 and 0.60/0.83/0.85 values cannot be read off the committed file as-is.
2. **Internal tension "w₁=w₂ always" (v25) vs "arg(A)≈±120°" (code): CONFIRMED real (§0).** Resolved by
   the Arm-0 real/complex flag. Arm 1 does not depend on the resolution (reports w₀,w₁,w₂ from A
   directly), but the successor must not cite "w₁=w₂ always" as established.
3. **β/β² label ambiguity is benign for the object (VERIFIED §0).** `beta_of(p)` returns *a* primitive
   cube root, uncalibrated vs the lift's ω²-action. Swapping β↔β² swaps w₁↔w₂ but leaves w_cov and w₀
   invariant — the object (covariant weight) is well-defined; only individual w₁,w₂ labels are
   convention-dependent.
4. **The v35 §5 β-calibration bug does NOT affect this object.** `cell_fn` uses only
   `eis`/`reduced_basis` from `int1_frame_operator_v1.build`, not its buggy `beta`/`eps` (line 41,
   probe x=12345). The cell readout is unaffected; β here is `beta_of(p)`.
5. **PR/n ≈ 0.23–0.34 (v27 #1): reproducible** from `investigate_harmonics_v1.py` (participation ratio
   of the d-space DFT). A **d-axis** object ⇒ characterization-only per the tautology disclosure; not
   in Arms 0–2.
6. **orbit-phase overlap 0.09→0.02→0 (v27 #1): reproducible but weak** — the candidate
   ψ(x)=exp(2πi·argmin-index/3) is flagged in the code's own comment as "NOT beta-equivariant" (a μ₃
   orbit *label*, not a covariant observable). A low overlap of a covariant vector with an admittedly
   non-covariant candidate is the expected/uninformative outcome.

## (b) Arms judged unfalsifiable as written (excluded from Arms 0–2; not to be treated as evidence)

- **"orbit-phase overlap → 0 ⇒ no closed form": unfalsifiable** as a characterization of the covariant
  part. It correlates φ₃ against one non-β-equivariant label; a null overlap rules out only that single
  non-covariant candidate. Do not read "overlap→0" as "no closed form."
- **"broadband (PR/n≈0.3) ⇒ no closed form": not falsifiable in isolation.** Broadbandness is
  consistent with BOTH a genuine Weil/CURVE sum (broadband by nature) AND estimation noise on a
  gauge/near-degenerate eigenvector. Decidable only when paired with the Arm-0 gate and the Arm-1
  FIELD/CURVE split. Folded into Arm 1; not a standalone finding.

---

## Ranking / pre-commitment summary

Gate first. A failed gate **redefines** the object (individual vector → slow eigenspace, or single-K
value → K-curve) — it does not proceed on a gauge quantity. Arm 1 attributes the (well-defined)
covariant weight to FIELD(lattice) vs CURVE(Weil) via the exact split; Arm 2 tests whether that weight
is even an excess over a μ₃-preserving matched null (Null-A marginal, Null-B lift-geometry) with
mandatory two-sided firing. Every terminal cell — including all four abstention branches — has its
conclusion fixed above, before data. **No cell concludes "safe/generic/no-structure":** a within-null
result is reported as a bounded magnitude at the matched-null level with its power and scope (drill
rule 1).

---

**Files read to fix semantics:** `conservation_spectrum_v2.py`, `isotypic_selection_rule_v1.py`,
`_field_bigrading_v1.py`, `int1_frame_operator_v1.py`, `_anomaly_drill_ct_split_v2.py`,
`ct_coupling_universality_v1.py`, `investigate_harmonics_v1.py`, `masked_structure_findings_v25/v27/v35.md`,
`POSITIVE_FINDINGS_MASTER_v4.md` (Part VI, §X.10), `btc_puzzle_investigation/CLAUDE.md` (NO-FLOAT),
`memory/feedback_anomaly_drill_protocol_2026_07_17.md`.
