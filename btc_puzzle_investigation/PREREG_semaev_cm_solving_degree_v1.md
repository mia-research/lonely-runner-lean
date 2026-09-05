# PRE-REGISTRATION — does the μ₆/μ₃ CM symmetry of secp256k1's j=0 curve LOWER the FIRST-FALL DEGREE of the Semaev index-calculus system, as a syzygy-structure effect, relative to a matched non-CM curve?

**File:** `PREREG_semaev_cm_solving_degree_v1.md`  **Date:** 2026-08-30
**Status: PRE-RUN / FROZEN before any confirmatory datum.** No verdict statistic computed. The only
runs licensed before this spec freezes are (i) the up-front TRACTABILITY GATE of §3 (run on a
CM-agnostic neutral system, so it cannot peek at the hypothesis) and (ii) the firing/VOID controls of
§5. Any change after the first confirmatory datum is a DEVIATION, logged in
`PREREG_semaev_cm_solving_degree_v1_DEVIATIONS.md`.

**Probe id:** P2c. Sibling to **P2** (`PREREG_mu6_solving_degree_v1.md`, last-fall degree, fixed |V|,
result Δ(d_LF)=0 quo-matched) and **P2b** (`PREREG_mu6_isotypic_solving_degree_P2b_v1.md`, per-isotype
d_LF on the σ-invariant target-orbit ideal). P2c differs in three pre-committed ways: (a) the verdict
statistic is the **first-fall degree D_ff** (coordinator correction; see §0-B, §2); (b) the object is
the **effect of the μ₃-SYMMETRIZATION on D_ff**, not the bare-curve contrast (which is forced — §0-A);
(c) an **up-front admissibility gate** decides whether an empirical |FB|-scaling arm is even run, or
the design pivots to a **structural/derived** first-fall argument (§0-B, §3, §6).

**Instruments to reuse (frozen):** `semaev_elimination_v1.py` — `summation_poly`, `_build_summation`,
`decomposition_system`, `measure_system`, `macaulay_stats` (exact per-degree GF(q) rank profile with the
`fall` field), `first_fall_and_solving`, `decomposable_target`, `mu3_lever_test`,
`leading_form_independence`, `isobaric_check`. `model_curve_infra_v1.py` — `select_j0_prime_order(...,
exclude_anomalous=True)`, `select_jgen(..., exclude_anomalous=True)`, `point_count`, `is_prime`, point
ops, `cube_root_units`. Semaev primitives cross-check: `cm_jointset_ho_v1.py` `semaev_s4`,
`cm_jointset_semaev_r5_v1.py` S5. `check_no_float.sh`. One harness extension is required (a σ-invariant
target-orbit + invariant-variable presentation, §4); it must be frozen and its firing plant re-run
before any confirmatory cell.

---

## 0. Ordering guard (why this spec exists — three pre-closed traps)

**Trap A — the FORCED first-fall degree (zero-power tautology for the bare-curve contrast).**
The project has already established (`RESULT_semaev_dsolv_statistic_power_v1.md` Finding 1;
`leading_form_independence(m)` in `semaev_elimination_v1.py`) that the leading (top-total-degree) form
of S_{m+1} is **isobaric, hence IDENTICAL across all curves** (A=0 j0, non-CM, j1728 alike). The
field-equation leading forms are `X_i^{|V|}`, also curve-independent. **First-fall degree is a
leading-form/syzygy-of-top-forms invariant → therefore FORCED equal for CM vs non-CM at matched (m,|V|)
in the SAME variable presentation.** A statistic forced equal across the two arms has *zero power*; a
"CM lowers D_ff" verdict measured on the bare-curve contrast would be a rationalization with a p-value.
**Resolution (pre-committed):** the bare-curve D_ff contrast is DEMOTED to a **negative control** (§5,
control N1: it MUST come out equal, quo-matched; if it differs, the harness is mis-built → VOID). The
verdict object is instead the effect of the **μ₃-SYMMETRIZATION** on D_ff (§1, §2, §6), where D_ff is
*not* forced: the symmetrized system lives in different variables with different leading forms, and the
β-covariance introduces early syzygies exactly at the first-fall degree — which is where the CM effect,
if any, must appear.

**Trap B — the un-informative-by-construction solving-degree scaling (dynamic-range collapse).**
Coordinator evidence (exploratory, q=79, |FB|=4,5,6): full Gröbner solving degree spans ~3.25 → ~4.5, a
dynamic range of ~1-2 integer degrees over the *entire* tractable |FB| span, where ±1 integer noise
swamps any scaling exponent; Gröbner blows up long before |FB| is large enough to expose an asymptotic
exponent. **A "solving-degree-vs-|FB| scaling exponent" verdict at tractable scale is preordained
uninformative and is NOT designed here.** The verdict statistic is the **first-fall degree D_ff**, which
appears at low degree *before* the Gröbner blow-up (this is precisely why the index-calculus literature
— Petit–Quisquater first-fall-degree assumption; Faugère–Gaudry–Huot–Renault symmetrized Semaev — uses
it), computable at meaningfully larger (|FB|,m). And even D_ff is admitted for a *scaling* verdict only
if the up-front tractability gate (§3) demonstrates ≥3-4 integer steps of dynamic range; otherwise the
empirical scaling arm is declared INADMISSIBLE and the design pivots to the structural arm (§6). No
scale is run that provably cannot show the effect.

**Trap C — the size-shrink confound in the symmetrization comparison.**
A μ₃-closed factor base of size |V| has field equations `∏_{r∈V}(X_i−r) = ∏_{orbit reps ρ}(X_i³−ρ³) =
h(X_i³)`, degree |V| but a polynomial of degree |V|/3 in the invariant `u_i = x_i³`. A raw-vs-symmetrized
D_ff drop could therefore be the *trivial |V|/3 shrink* of the field-equation degree, present on ANY
curve, rather than the CM covariance. This is the exact worry already written into
`mu3_lever_test`'s docstring ("beyond the trivial |V|/3 factor-base shrink"). **Resolution:** the μ₃
lever is isolated by a matched control that gets the identical size shrink but lacks the covariance — the
**non-CM curve with a μ₃-closed FB** (§3), whose S_{m+1} does NOT satisfy the β-covariance so its
invariant-variable reduction is NOT equivalence-preserving. The verdict is the **double difference**
`ΔΔ = [D_ff(CM raw) − D_ff(CM sym)] − [D_ff(nonCM raw) − D_ff(nonCM sym)]` (§2), or, when the non-CM
reduction fails the per-arm equivalence control, the *qualitative* signature "the reduction is
equivalence-preserving only on CM" (both readings pre-committed, §9).

**Trap D — closure by declaration.** Per the project stance and P2/P2b: D_ff (or a symmetrization
effect on it) is ONE factor of total IC cost (relations × 1/yield × cost/solve + linear algebra); a
null here is a scoped COMPONENT result, never a closure of the CM/Semaev avenue. Pre-committed in §9,
with the un-projected subspace named (the isotypic staircase *shape*, P2b's object).

---

## 1. OBJECT

**What is measured.** The **first-fall degree D_ff** of the Semaev point-decomposition system over
GF(q), and specifically whether the **μ₃-symmetrization** of that system — a μ₃-closed factor base plus
a rewrite in μ₃-invariant variables — LOWERS D_ff relative to the raw system, and whether that drop is
**CM-specific** (present on the j=0 μ₆ curve, absent on a #E-matched non-CM curve that receives the
identical μ₃-closed-FB treatment).

- **Raw system** (`decomposition_system`): `I_raw = ⟨ S_{m+1}(x₁,…,x_m, t) ⟩ + ⟨ ∏_{r∈V}(x_i − r) :
  i=1..m ⟩` over GF(q), degrevlex, `t = x`-coord of a real decomposable target `T = P₁+…+P_m`,
  `P_i` with x-coords in the factor base `V`. (Consistent regime = real relation exists = the
  attack-relevant object; the inconsistent regime is forced, P2 Trap A.)
- **Symmetrized system** `I_sym` (the novel element, specified in full in §4): on a **μ₃-closed** `V`
  (closed under `x ↦ βx`, `β³=1`, so `V` is a union of μ₃-orbits `{ρ, βρ, β²ρ}`), form the
  **σ-invariant target-orbit ideal** (targets `{t, βt, β²t}` bundled via `t³ = c`; σ: x_i↦βx_i then
  preserves the ideal — established for j=0 in `RESULT_mu6_isotypic_solving_degree_P2b_v1.md`), and pass
  to the **invariant subring** `GF(q)[x₁,…,x_m]^σ` (monomials of total degree ≡ 0 mod 3; `u_i = x_i³`
  and the mixed invariants). D_ff is read on this reduced presentation.

**Object, not proxy.** D_ff is the smallest degree D at which the Macaulay matrix of the generating set
first exhibits a degree fall (a genuine syzygy producing a lower-degree element) — read from the exact
GF(q) rank profile, an emergent computational property of the ideal, not a quantity defined to differ
between systems. It is the community-standard first-fall-degree object.

**Tautology check (stated before the run).** The μ₃-symmetrization is a *construction* applied to the
SAME variety (the same set of decompositions of the same target orbit on the same FB); D_ff is an
emergent Macaulay quantity of the reduced ideal — disjoint in construction from the covariance that
motivates the reduction, so measuring one against the other is not a tautology. The one genuine
entanglements are (i) yield/quo (Trap B of P2) — removed by quo-matching the raw arms (§3); (ii) the
|V|/3 size shrink (Trap C) — removed by the non-CM μ₃-closed-FB matched control (§3, §2 double
difference). The bare-curve D_ff is FORCED (§0-A) and is used only as a negative control.

**Subspace caveat (mandatory).** D_ff is a scalar. If the μ₃ symmetry's effect lives NOT in the scalar
first-fall degree but in the *shape* of the resolution — the ω-isotypic pieces of the staircase, which
variables resolve first, the syzygy-module degrees (P2b's object) — a scalar D_ff null does NOT close
it. A scalar null is scoped to the scalar; the pre-committed non-closure follow-up (§9) is the isotypic
staircase / syzygy-module structure.

---

## 2. STATISTIC (exactly one primary, named now)

**Primary statistic: the first-fall degree**

```
D_ff(I) := min { D in [1, Dmax] : macaulay_stats(F, gens(I), xs, Dmax)[D]['fall'] > 0 }
```

read from the EXACT GF(q) Macaulay rank profile (`macaulay_stats`; `fall = inter - prev_rank`, a
degree-fall > 0 at D marks the first genuine syzygy producing a lower-degree element). `first_fall_and_solving`
already returns this as `d_ff`; no read-out change is needed for the raw arm. The symmetrized arm needs
the new σ-invariant/invariant-variable generator set (§4), then the SAME `macaulay_stats` D_ff read-out.

**Why D_ff and not the alternatives (pre-committed choice, with reasons):**
- **Full solving degree / max-GB-generator degree (`d_gb`)** — EXCLUDED as the verdict statistic:
  (i) dynamic-range collapse + intractability at scaling scale (§0-B, coordinator evidence);
  (ii) `d_gb` is solver/term-order dependent. Retained only as a disclosed secondary read-out on the
  small cells where Gröbner completes.
- **Quo-saturation degree `d_solv`** — entangled with the KNOWN CM yield difference (P2 Trap B). Kept as
  a quo-matched secondary read-out, never the headline.
- **Last-fall degree `d_LF`** — P2's primary; retained here as a secondary read-out because it is the
  Caminata–Gorla solving-degree lower proxy and gives continuity with P2's Δ=0 result. Not primary here
  per the coordinator's D_ff mandate and because D_ff is the statistic reachable at larger (|FB|,m).

**Verdict object.** The symmetrization effect on D_ff, isolated from the size shrink by the double
difference:
```
ΔΔ_ff = [ D_ff(CM_raw)   - D_ff(CM_sym)   ]  -  [ D_ff(nonCM_raw) - D_ff(nonCM_sym) ]
```
per (q, m, |V|)-cell, over quo-matched, #E-matched CM/non-CM pairs. `ΔΔ_ff > 0` = the μ₃ symmetrization
lowers D_ff MORE on the CM curve than the pure size-shrink baseline supplies. Pooled across primes by a
sign-flip permutation null (`Σ ε_i (ΔΔ_ff)_i`, ε_i∈{±1}) — a targeted, pooled statistic, NOT a
max-over-cells.

**Two arms, both pre-committed (the tractability gate of §3 selects which is the verdict):**
- **EMPIRICAL-SCALING arm** (verdict only if §3 gate PASSES): report `ΔΔ_ff(|V|)` and `D_ff(CM_sym)(|V|)`
  vs `D_ff(nonCM_sym)(|V|)` as *curves in |V|*, and test whether the CM advantage GROWS with |V|
  (a fitted flat-vs-linear trend on the integer curve, ranked against a permutation bootstrap; §5) —
  a constant offset is NOT the lever, a growing gap is. Report the degree-vs-|V| tables, never a single
  |V|.
- **STRUCTURAL arm** (verdict if §3 gate FAILS, i.e. dynamic range insufficient): the DERIVED
  first-fall statement (§6) — how the β-covariance introduces early syzygies in the invariant-variable
  block — corroborated by exact low-degree Macaulay-rank spot checks; NOT a fitted exponent from a
  too-narrow sweep.

**Negative-control statistic (forced, must hold):** `D_ff(CM_raw) - D_ff(nonCM_raw) = 0` quo-matched
(the isobaric forced-equality, §0-A). A nonzero here means the harness is mis-built → VOID.

**Validity gate on every cell (Dmax-stability):** `Dmax` must exceed the largest degree any cell's D_ff
could reach (D_ff ≤ Macaulay bound `deg(Sx) + m·(|V|-1)`), and raising `Dmax` by +4 must leave D_ff
unchanged. A censored cell (D_ff moves when Dmax rises, i.e. no fall observed ≤ Dmax) is marked
UNRESOLVED and EXCLUDED from the pooled statistic — its exclusion is recorded, never silent.

---

## 3. TRACTABILITY GATE (up-front admissibility precondition) + MATCHED CONTROL

### 3a. Tractability gate — MANDATORY, run BEFORE any confirmatory arm, on a CM-agnostic system

The gate decides admissibility of the EMPIRICAL-SCALING arm. It is run on a **neutral** system so it
cannot peek at the CM hypothesis: the raw non-CM arm (or a generic dense system of the same degree
profile), sweeping D_ff across the tractable `(q, |V|, m)` grid.

**PASS criteria (all three, pre-committed numeric):**
1. **Dynamic range:** D_ff (as a function of |V| at fixed m, or of m at fixed |V|) must vary by
   **≥ 3 integer steps** across the swept range. (`RESULT_semaev_dsolv_statistic_power_v1.md` should be
   consulted first: if D_ff there is flat over |V|, the empirical arm is inadmissible immediately.)
2. **Enough sweep points:** **≥ 4 distinct resolved |V|-levels** (raw arm) / **≥ 3 distinct resolved
   μ₃-closed |V|-levels ∈ {3,6,9,12,…}** (symmetrized arm) within the time box, each with the
   Dmax-stability gate (§2) satisfied.
3. **Noise floor stated:** the per-(|V|,m) cell spread of D_ff over the K replicates (§3b) must be
   reported; the trend to be claimed must exceed this ±integer floor (D_ff is integer, so the floor is
   the observed inter-replicate range, typically 0-1).

**On FAIL:** the EMPIRICAL-SCALING arm is declared **INADMISSIBLE — not run** (recorded, with the
observed dynamic range). The design pivots to the STRUCTURAL arm (§6) as the verdict. This is the
coordinator's binding instruction: no uninformative sweep is run.

### 3b. Matched control (isolates μ₆/CM from #E, yield, and size)

Per model prime `q ≡ 1 mod 3` (so β exists and μ₆ is rational on j0):
- Build j0 (`y²=x³+B`, μ₆) via `select_j0_prime_order(q, exclude_anomalous=True)` and `n_nonCM ≥ 5`
  ORDINARY non-CM curves (`j∉{0,1728}`) via `select_jgen(q, target_N=#E_j0, exclude_anomalous=True)`.
  **Anomalous (trace-1) curves excluded on BOTH arms** (Smart's attack confounds).
- Pair j0 to the NEAREST-#E non-CM (`match_nearest`), C2-capped: accept only if relative #E gap
  `< 2/√q` (else drop the prime — recorded).
- **quo-matching (removes the yield confound, P2 Trap B):** for the paired cell, resample decomposable
  targets (`decomposable_target`, distinct seeds) until a j0 target and a non-CM target with EQUAL `quo`
  are found (bounded budget B_match; unmet primes recorded, enter only a stratified fallback, not the
  primary pooled test).
- **μ₃-closed FB on BOTH arms** for the symmetrized comparison (`mu3_lever_test`'s construction: μ₃-close
  the decomposition x-coords, pad with full μ₃-orbits to size |V|). The non-CM arm gets the identical
  size shrink but lacks the β-covariance — this is the Trap-C control.
- **Averaging:** every (q, m, |V|, arm) cell is the median over `K = n_nonCM × FB-samples × target-seeds`
  replicates (`K ≥ 15`); report median + inter-quartile spread, never a single instance.

**What the control PRESERVES:** q; #E (±2/√q); m; |V|; the isobaric Semaev leading-form profile
(IDENTICAL across curves, `leading_form_independence`); consistent regime; `quo` (matched); the μ₃-closed
FB size shrink (both arms). **What it DESTROYS:** the j=0 β-covariance of S_{m+1} (present only on the CM
curve) and the curve arithmetic. Because leading forms are identical (forced), and the size shrink is
matched, any surviving `ΔΔ_ff` lives strictly in the covariance-induced lower-order syzygies — the μ₃
lever.

**Secondary discriminating arm (μ₆-specific vs generic-CM):** j1728 (μ₄, ORDINARY, require q≡1 mod 12),
#E-matched, same statistic — to separate a μ₆-specific drop from a generic-CM drop. Not part of the
primary verdict.

---

## 4. THE SYMMETRIZATION — precise reduction + equivalence (the non-self-auditable element)

**The automorphism.** `E: y²=x³+B` (j=0) carries the order-3 automorphism `[ω]:(x,y)↦(βx,y)`
(`(βx)³+B = β³x³+B = x³+B` ✓); with `[-1]:(x,y)↦(x,-y)` it generates the μ₆ = μ₂×μ₃ torsion of Aut(E).

**The covariance (derived, weight to be certified per m by `isobaric_check`).**
`S_{m+1}(βx₁,…,βx_m,βx_R) = β^{κ} S_{m+1}(x₁,…,x_m,x_R)`, κ = the isobaric weight (κ ≡ 0 mod 3 iff σ
preserves the polynomial up to scalar). This is the EXACT algebraic symmetry that motivates the
reduction; it is present by construction on j0 and ABSENT on any non-CM curve.

**Why the fixed-target ideal is NOT the object (established, P2b).** For a FIXED target `x_R`, σ rotates
the target (`σ(Sx) = S(x, β⁻¹ x_R)`), so `I_raw` is not σ-invariant; P2 measured that symmetry-BROKEN
object. To get a σ-invariant, 0-dimensional ideal, bundle the TARGET ORBIT `{x_R, βx_R, β²x_R}` via the
extra generator `x_R³ = c` (`c = x_R³`, σ-invariant). On j0 this ideal IS σ-invariant and 0-dimensional
(P2b: for m=3, quotient dim 36 = 12/12/12 ω-isotypic, top-degrees {6,4,5}).

**The invariant-variable reduction.** `GF(q)[x₁,…,x_m]^σ` = the subring of monomials of total degree
≡ 0 mod 3 (generated by `u_i = x_i³` and the mixed degree-3 invariants `x_i x_j x_k`, etc.). On a
μ₃-closed FB the field equations become `h(u_i) = ∏_{orbit reps ρ}(u_i - ρ³)`, degree |V|/3 in `u_i`.
The symmetrized system `I_sym` is the ideal expressed on this invariant subring (equivalently the
degree-≡0-mod-3 isotypic block, which block-diagonalizes the Macaulay matrix for σ-invariant `I`).

**Equivalence (why solving `I_sym` solves the decomposition problem).** Decompositions occur in σ-orbits
of size 3 (fixed points require `βx=x ⟹ x=0`, excluded). The variety of `I_sym` is in generic 3-to-1
correspondence with the σ-orbits of the variety of the target-orbit ideal; recovering one invariant
solution recovers the whole μ₃-orbit of decompositions — this is the index-calculus win, not a change of
problem. **This equivalence is CHECKED per cell** by the firing control §5(b): plant a known
decomposition on the μ₃-closed FB, solve `I_sym`, confirm the planted σ-orbit is recovered. If not, the
reduction is mis-built → VOID (never silently trusted).

**Matched-control behavior (the μ₃ signature).** On a non-CM curve, S_{m+1} lacks the β-covariance, so
σ does NOT preserve the target-orbit ideal → the invariant-variable reduction is NOT equivalence-
preserving there (its per-cell equivalence control §5(b) FAILS, or the reduced variety loses the real
decompositions). Two pre-committed readings (§9): (i) if the non-CM reduction is well-defined (size
shrink only), the verdict is the double difference `ΔΔ_ff`; (ii) if the non-CM reduction fails its
equivalence control, the qualitative signature "equivalence-preserving only on CM" IS the μ₃ finding,
reported with power+scope, not a degree double-difference.

---

## 5. FIRING & VOID CONTROLS (all must fire/hold; no verdict if any fails)

- **(a) SYMMETRIZATION FIRING PLANT (must fire) — a KNOWN D_ff drop of KNOWN provenance.** A σ-invariant
  ideal built so the invariant-variable block provably resolves a syzygy EARLIER than the raw
  presentation (e.g. P2b's `x_i³ - c_i` block construction with a planted early covariant syzygy, whose
  raw vs invariant first-fall degrees `d_raw > d_sym` are known a priori). The instrument MUST read
  `D_ff(sym) < D_ff(raw)` on this plant. If it does NOT, the symmetrization is mis-built ⇒ **STOP-fix**;
  no confirmatory cell runs until it fires. (Kept SEPARATE from the μ₃/CM hypothesis — a generic
  planted covariant syzygy of known size, so its firing certifies the instrument without presupposing
  the answer.)
- **(b) SOLVER / EQUIVALENCE SANITY (must hold, else VOID).** For every symmetrized cell, plant a known
  decomposition `(x₁*,…,x_m*)` on the μ₃-closed FB; the reduced system's variety MUST be non-empty and
  contain the σ-orbit of the plant (the Gröbner/elimination solve actually FINDS the planted relation).
  If the variety is empty or the planted orbit is absent, D_ff is meaningless ⇒ VOID for that cell.
- **(N1) FORCED-EQUALITY NEGATIVE CONTROL (must hold).** `D_ff(CM_raw) = D_ff(nonCM_raw)` quo-matched
  (the isobaric forced-equality, §0-A). If it differs, the harness is mis-built ⇒ VOID.
- **(N2) SIZE-SHRINK NEGATIVE CONTROL (must hold).** Two INDEPENDENT non-CM curves, both μ₃-closed-FB,
  same size ⇒ their raw-vs-sym D_ff differences match (`ΔΔ_ff` between two non-CM ≈ 0). If two non-CM
  curves show a spurious `ΔΔ_ff`, the size-shrink baseline is mis-calibrated ⇒ VOID.

**Rule (project law):** if the firing plant (a) does not fire, the null is uninformative — full stop,
outcome VOID (§9), NOT a reported null.

---

## 6. STRUCTURAL / ANALYTIC ARM (PRIMARY VERDICT if §3 gate FAILS)

Per coordinator #4: if the tractable scale cannot deliver the dynamic range (§3a FAIL), the verdict is
the DERIVED first-fall statement, spot-checked at the low degrees where D_ff lives — not extrapolated
from a too-narrow numeric sweep.

**What is derived.** (i) the covariance weight κ and κ mod 3 (`isobaric_check`, exact); (ii) the
isotypic dimensions of the σ-invariant target-orbit quotient (P2b established 12/12/12 for m=3); (iii)
the claim that the β-covariance produces a first syzygy in the invariant block at a first-fall degree
`D_ff^sym ≤ D_ff^raw`, with the *reason* (the covariant relation among the top forms in the invariant
grading), and by how much — as a statement about the syzygy structure, not a fitted number.
**Matched control (analytic):** on a non-CM curve the covariance is absent, so no such invariant-block
syzygy exists; the derivation predicts NO drop (or an ill-posed reduction). FGHR's symmetrized-Semaev
degree-reduction is the template and is CITATION-OWED (§ owed gates) before the derivation is graded.

**Spot-check (empirical corroboration, low degree only).** At several small `(q, m, |V|)` with q≡1 mod 3
and μ₃-closed |V|∈{3,6,9}, compute `D_ff(CM_sym)`, `D_ff(CM_raw)`, `D_ff(nonCM_sym)`, `D_ff(nonCM_raw)`
via exact GF(q) Macaulay ranks and confirm they match the derivation's prediction. Divergence between
derivation and spot-check is a DEVIATION and blocks the verdict. The spot-check is corroboration of a
derived statement, never itself the scaling claim.

**Extrapolation caveat (binding, coordinator #5).** A model-scale D_ff drop — empirical or derived — is a
MECHANISM signal about the syzygy structure of the μ₃-symmetrized Semaev system; it is NOT a secp-scale
complexity claim. secp's |FB| would be astronomically larger and is not reached. A lower model-scale
D_ff is suggestive of a lever *mechanism*, decided by the derivation's scale-freeness + cross-prime
stability, never by extrapolating a model-scale number.

---

## 7. POWER / ESTIMABILITY / SCOPE

- **D_ff is a small INTEGER.** The minimum detectable per-cell effect is **one integer step**; a
  sub-integer trend is below power and cannot be claimed. The inter-replicate noise floor (§3a-3) is
  reported per cell (integer, typically 0-1).
- **Scaling power (empirical arm, only if §3 PASSES).** To distinguish a CONSTANT offset from a GROWING
  gap in `ΔΔ_ff(|V|)`, need ≥3-4 resolved |V|-levels with monotone consistent sign; fit flat-vs-linear
  on the integer curve, rank the AICc improvement against a permutation bootstrap (arm-label permute
  within each |V|-level; size-only float, §8). A gap growth of **< 1 total integer step across the
  swept |V|-span** is BELOW resolution → reported as "no resolvable growth," NOT "no growth." **If fewer
  than 3 |V|-levels resolve, the scaling verdict is VOID-underpowered** (pre-committed §9).
- **Cross-prime stability (scale-free requirement).** A mechanism claim needs the SIGN of `ΔΔ_ff` (or
  the structural derivation) stable across the prime band — not an extrapolation of a fitted number.
- **Structural-arm power.** The derivation's power is the exactness of the covariance/isotypic
  computation + the spot-check agreement at every tested low-degree cell; a single spot-check divergence
  falsifies the derivation.
- **SCOPE.** Model primes `q ≡ 1 mod 3` only (β exists, μ₆ rational). Primary band: reuse a frozen
  Gröbner-tractable set (e.g. the P2 band p∈[523,823], or the wider [523,8011] where D_ff resolves;
  SHA-256 recorded pre-run). j1728 secondary arm: q≡1 mod 12. m=3 (S₄) PRIMARY; m=4 (S₅) SECONDARY under
  a per-cell time box; m=5 (S₆): VOID-intractable. |V| grid: raw arm |V|∈{4,…, largest that resolves
  D_ff in the time box}; μ₃-closed arm |V|∈{3,6,9,12,…} (multiples of 3). **secp-scale (2²⁵⁶) is
  INFEASIBLE and not attempted** (§6 caveat). Every number the run emits carries `(q-band, m, |V|, quo,
  n_nonCM, arm)`.

---

## 8. EXACTNESS (float-free by construction)

- **Signal path exact.** Macaulay ranks are over GF(q) (exact modular linear algebra); D_ff, d_LF,
  d_solv, d_gb, quo, dim, κ, isotypic dims are INTEGERS read from ranks / degrees / GB generators — no
  float threshold decides any degree. Curve construction, targets, factor bases, β, invariant variables:
  `int` / GF(q). No key or key-derived value enters (model-prime arithmetic; no puzzle key).
- **Backend note.** The rigorous harness is Sage (`matrix(GF(q)).rank()`, `PolynomialRing`,
  `EllipticCurve` — exact). If any sympy path is used (`groebner(..., modulus=q)`) it is exact modular
  arithmetic, but its `d_gb` is solver-dependent and stays SECONDARY; the PRIMARY D_ff is always the
  exact `macaulay_stats` rank profile. Any `float(...)`, true division, `**0.5`, `math.*` in the signal
  path is a violation.
- **Float carve-out (size-only, no key in path, EMPIRICAL arm only):** the flat-vs-linear scaling fit
  and permutation-bootstrap bookkeeping use float LS ranked against an integer-count permutation null,
  reporting a size never a threshold verdict on the data — `# noqa: float — (stat) monotone statistic
  ranked against a matched permutation null; inputs are exact integer D_ff`. The STRUCTURAL arm (§6) has
  NO float.
- `check_no_float.sh` must PASS on the runner before any confirmatory cell.

---

## 9. PRE-COMMITMENT (filled BEFORE the run — one row per outcome)

| # | Outcome (firing plant §5a fires and equivalence §5b holds unless stated) | Conclusion (pre-committed) | Grade |
|---|---|---|---|
| **A (empirical, gate PASS)** | §3 gate PASSES; pooled `ΔΔ_ff > 0`, sign-flip p<0.05, stable across primes, and the CM advantage GROWS with |V| across ≥3 resolved levels (flat-vs-linear favours growth vs bootstrap) | The μ₃ symmetrization lowers D_ff of the j0 Semaev system MORE than the size-shrink baseline, CM-specifically and growingly, at model scale — a real syzygy-structure finding and the necessary-not-sufficient COMPONENT motivating the full IC-cost probe. NOT a lever/secp claim on its own; extrapolation caveat §6 attached. | EMPIRICAL (DERIVED if tied to the covariance syzygy in §6) |
| **B (empirical, gate PASS, constant)** | §3 PASS; `ΔΔ_ff > 0`, p<0.05, but CONSTANT (no growth across |V|) OR not CM-specific (double difference ≈ 0) | Bounded/size-shrink degree offset; a structural curiosity, NOT a lever component (a constant shift does not touch the exponential; non-CM-matched ⇒ not the covariance). Report bound + scope. | EMPIRICAL — bounded, scoped |
| **C (empirical null, gate PASS)** | §3 PASS; controls fire; `ΔΔ_ff` sign-flip p>0.05 with power for a ≥1-step effect | **Scoped COMPONENT NULL:** at (q-band, m, |V|-grid), quo-matched, the μ₃ symmetrization does NOT lower D_ff beyond the size-shrink baseline, with stated power. Explicitly NOT a closure of the CM/Semaev avenue — D_ff is one IC-cost component; the isotypic staircase *shape* (P2b) is the un-projected subspace and remains open (§1 caveat). | EMPIRICAL — scoped component null (NOT avenue closure) |
| **D (structural, gate FAIL)** | §3 gate FAILS (dynamic range < 3 steps / < required levels) → empirical arm INADMISSIBLE; STRUCTURAL arm §6 run | Verdict = the DERIVED first-fall statement (μ₃ covariance introduces / does not introduce an early invariant-block syzygy), CM-specific by the analytic matched control, corroborated by low-degree spot-checks. Report the derivation + spot-check agreement + extrapolation caveat. A derived DROP → mechanism signal (grade DERIVED/CITED pending FGHR verifier); a derived NO-DROP → scoped structural null, not a closure. | DERIVED / CITED (pending owed gates) — or scoped structural null |
| **E (equivalence-only signature)** | Non-CM μ₃-reduction FAILS its equivalence control §5b while CM passes | The invariant-variable reduction is equivalence-preserving ONLY on the CM curve — itself the μ₃ signature. Report qualitatively with power+scope; no degree double-difference formed. | EMPIRICAL — qualitative μ₃ signature, scoped |
| **F (VOID)** | Firing plant §5a does not fire, OR equivalence §5b fails on CM, OR N1/N2 fires, OR primary cells UNRESOLVED (Dmax-censored) where μ₃ would matter | **VOID** — instrument uninformative. State the tractability boundary (largest resolved (m,|V|,q)). No null reported. | VOID |
| **G (VOID-underpowered scaling)** | §3 PASS marginally but < 3 |V|-levels resolve in the time box | **VOID-underpowered** for the scaling verdict; report the resolved cells + range; a per-|V| result does not become a scaling claim. | VOID-underpowered |

**No grade in this table moves UP until the owed gates clear.** A run under an unavailable gate is
`[PROVISIONAL — <gate> owed]` in the grade slot and produces evidence only, never a promotion
(CLAUDE.md §2a).

---

## Owed gates (BEFORE any grade moves up)

1. **Second independent `experiment-designer` read** of this v1 before any RETAINED/DERIVED promotes
   (frame layer is not self-auditable, CLAUDE.md §2b).
2. **`citation-verifier`** on: Petit–Quisquater first-fall-degree assumption; Faugère–Gaudry–Huot–Renault
   symmetrized Semaev degree reduction (the §4/§6 template); Caminata–Gorla (solving degree ≥ last-fall,
   for the secondary d_LF read-out); and the "no competitive prime-field summation-poly index calculus is
   known" line (Semaev; Amadori–Pintore–Sala 2017) — the extension-field LFD literature must NOT be cited
   as a prime-field secp bound (category error).
3. **`compile-diff`** if folded into a master compendium.

**Meta:** a null here is a scoped COMPONENT result on D_ff, not a verdict on μ₆; a positive is a
component/mechanism signal that motivates the full-cost probe, not a lever. Neither closes the CM/Semaev
avenue (Trap D, §1 subspace caveat).

---

**Provenance.** Pre-registered via the `experiment-designer` gate (context-isolated), 2026-08-30, with a
main-session correction that switched the verdict statistic to first-fall degree + added the up-front
tractability gate + the structural fallback. The gate independently surfaced (and this spec reconciles)
that first-fall degree is FORCED curve-independent for the BARE contrast (`RESULT_semaev_dsolv_statistic_power_v1`)
and that P2 (`RESULT_mu6_solving_degree_v1`) already found the bare ω-covariance last-fall Δ=0 — hence
the object here is strictly the μ₃-SYMMETRIZATION (invariant-variable) effect on D_ff, size-shrink-
controlled. SPEC ONLY — no confirmatory datum computed.
