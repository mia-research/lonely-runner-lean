# PREREG — C-center: a finite center / component group in the geometric monodromy, read as an EXACT ζ₃-ratio membership contrast across CM type

**Date:** 2026-08-21. **Status: SPEC ONLY.** No `ρ(a)`, no char-poly, no membership
count has been computed on any curve for this spec. Nothing runs until the
`experiment-designer` gate returns on *this* file. **No confirmatory statistic was computed
in producing this spec.**

**Freeze protocol:** at run start the runner prints the SHA-256 of this file into the RESULT and
opens `PREREG_monodromy_center_glv_ratio_v1_DEVIATIONS.md`. Any change to statistic, null, filter,
scope, or falsification after freeze is a disclosed deviation.

**Reuses (do not re-derive):**
- exact membership machinery `g_k = deg gcd(L*(T), L*(ζ_k T))`, multi-modular lower bound + char-0
  resultant certificate `Res_T(L*, L*(ζ_k T)) = 0` in `ℤ[x]/(Φ_N(x), Φ_k(x))`
  (`RESULT_120deg_resultant_certificate_v1`, `verify_120deg_resultant_certificate_v1.sage`);
- the arm arithmetic and cofactor facts A1/A2/A3, iso-class selection, and firing/order controls
  C-ORDER / C-PLANT / C-REPRO / C-EXACT from `PREREG_jclass_120deg_discriminator_v2.md` §§1,3,6.
- neutral facts (given, NOT re-tested): 1-point marginal = SU(2)/Sato–Tate to 4–5 sig figs over
  49,833 cells at p=100003 (`RESULT_monodromy_sato_tate_at_scale_v1`); pooled level-spacing
  consistent with iid Sato–Tate, no GUE repulsion (`RESULT_semicircle_null_and_verification_v1`).
  The **connected component acting as SU(2) is GIVEN**; the **finite center / π₀ is the sole target.**

---

## 0. Two design findings stated FIRST (object-level; they shape every arm below)

**(D-TAUT) The GLV-equivariance relation ρ(a)↔ρ(λa) is at high risk of being FORCED by construction,
so it is NON-verdict-bearing.** The record defines the monodromy cells as the `(N−1)/6` **μ₆-cosets on
J0, "where λ acts"** (`RESULT_monodromy_sato_tate_at_scale_v1` §; `RESULT_semicircle_null` on the
`L=(N−1)/6` free class reps). If `a` and `λa` lie in the **same** μ₆-coset then `ρ(λa)=ρ(a)` is an
identity of the construction, not a center property, and the matched null that permutes the `a↔λa`
partnering **destroys that identity exactly as it would destroy a real signal** — the residue-vs-
component tautology (`feedback_residue_vs_component_tautology_2026_07_14`: shuffle exposes nothing
when it breaks the artifact like signal). **Therefore the GLV-equivariance arm is EXPLORATORY only**,
gated behind control **C-DISJOINT** (§6), and never contributes to the verdict.

**(D-SEL) The raw J0 concentration `q_{J0}` is partly KNOWN and selection-confounded; the verdict is a
CM-TYPE CONTRAST, not the raw J0 rate.** `RESULT_n1_120deg_exact_v1` already records `g₃=2` at every
**census-surviving** cell of 22 primes on `y²=x³+7`. "Surviving" is a filtered subset (V=0 census +
repeated-root removal); the survival filter may itself select ρ=ζ₃ cells, so a bare "J0 concentrates
at ζ₃ beyond a center-free SU(2) null" can fire from **selection**, not from a center. The verdict
therefore rests on the **contrast** `Q₃(J0) − Q₃(reference)` where the reference carries the identical
filter but a different / absent CM type (§2 J1728, JGEN). The discrete OFFSET VALUE — *which* root of
unity, μ₃ vs μ₄ vs none — is the object a selection/pooling artifact cannot manufacture.

---

## 1. OBJECT

The **finite center and component group π₀ of the geometric monodromy** `G_geom` of the
Fourier-transform sheaf family `{H¹_c(E, L_{χ₂(y)} ⊗ L_{χ_a})}_a`, rank-4 lisse, Frobenius eigenvalues
`{α₁,α₂,α₃,α₄}` pure of weight 1, `α = √p·e^{iθ}`. The connected component is GIVEN (acts as SU(2) in
the trace). We probe the DISCRETE center via a fixed algebraic relation on the eigenvalue
configuration: whether a cross-pair eigenvalue ratio is an EXACT primitive cube root of unity.

**Disjointness / tautology check.** Feature = exact μ₃-membership indicator `I₃(cell)` (below).
Target = presence of a nontrivial finite center. `I₃` is an *arithmetic* Frobenius fingerprint;
inferring a *geometric-monodromy center* from it is licensed only by the CM-type contrast (§2) — the
inference `geometric ⇐ arithmetic` is scoped, not assumed (see §7). The **within-cell** ratio is a
different observable from the **pooled single-angle** spectrum the spacing test used; that
orthogonality (§ below) is why this is not the already-run test. The GLV arm's tautology risk is
carved out in D-TAUT and is non-verdict-bearing.

**Why orthogonal to the level-spacing null (the crux).** The pooled 2-point / level-spacing null
(`RESULT_semicircle_null`) operates on **one eigenangle per cell, pooled across cells** (the V1 trace
angle `t(a)=Im V₁/2√p`), testing consecutive-gap statistics against a marginal-varying semicircle. `I₃`
is a **fixed exact algebraic relation between the two pair-angles WITHIN a single cell** (θ_β−θ_α =
±120° *exactly*, as an identity in the splitting field). Two configurations with identical 1-point
marginals AND identical pooled spacing (SU(2) trivial-center vs SU(2)×{Z/3}) give `I₃`-rate 0 vs
positive: the discrete center is a measure-zero algebraic event that no continuous spacing/marginal
statistic can resolve. This statistic therefore **cannot reduce to** the spacing test.

## 2. STATISTIC (exactly one verdict statistic; arms are its references)

Per cell define the **exact μ₃-membership indicator**
`I₃(cell) = [ g₃(cell) ≥ 1 ]`, `g₃ = deg gcd(L*(T), L*(ζ₃ T))`,
computed by the reused machinery. **Certification direction is one-sided and enforced**
(`CORRECTION_120deg_census_certification_direction_v1`): `I₃ = 1` is asserted ONLY with a char-0
resultant certificate `Res_T(L*,L*(ζ₃T))=0` in `ℤ[x]/(Φ_N,Φ₃)`; a multi-modular `g₃≥1` without
certificate is logged `g₃ ≤ bound, uncertified` and does NOT set `I₃=1`. `I₃ = 0` (`min_l g₃,l = 0`)
is exactly certified. The pairing-definition ambiguity is **dissolved**: `g₃` counts ζ₃-related root
pairs over the whole multiset, independent of any representative or factor ordering.

Per arm/prime, the **concentration rate** `Q₃(arm) = (#cells with I₃=1) / (#cells on frozen filter)`.

**THE verdict statistic (single, pooled, targeted — not a max-over-cells):**
`Δ₃ = Q₃(J0) − Q₃(REF)`, REF = the matched-filter center-free reference (primary REF = J1728 μ₃-rate;
secondary REF = JGEN μ₃-rate; tertiary REF = the resampled center-free surrogate of §3). Distribution
of `Δ₃` under the matched null (§3) is a two-proportion / label-permutation law; verdict = its exact
permutation tail. **No maximization over k**: k=3 is pinned for J0 by its μ₆ automorphism; k=4 is
pinned separately for the J1728 self-check (§4). No max over cells; `Q₃` is pooled.

## 3. MATCHED CONTROL (preserves SU(2) marginal + all Weil/integrality/filter structure; destroys ONLY the discrete offset)

The null must reproduce every structure the real data has EXCEPT a nontrivial finite center.
- **Preserves:** Weil purity `|α|=√p`; integrality of `L*∈ℤ[T]`; the determinant/functional-equation
  relation `{α,ᾱ,β,β̄}`; the SU(2) 1-point marginal (each pair-angle semicircle); the **identical
  census/survival filter** (V=0 census + repeated-root removal) applied cell-for-cell.
- **Destroys:** any fixed cross-pair discrete offset (the center). Implementation: **resample the
  second pair-angle θ_β independently from the empirical semicircle marginal**, holding θ_α and the
  filter fixed, forming a surrogate `L*_null ∈ ℤ[T]` (nearest integer-quartic on the |root|=√p locus),
  then applying the SAME `g₃`/certificate machinery and the SAME filter. This preserves the marginal
  and the filter and destroys only the θ_β−θ_α coupling.
- **NOT a spacing null.** This null never touches consecutive-gap statistics; it is a within-cell
  cross-pair decoupling. It is explicitly distinct from `RESULT_semicircle_null`'s pooled spacing null.
- **q₀ is MEASURED, never assumed 0.** The surrogate μ₃-coincidence rate `q₀ = Q₃(null)` is estimated
  on the SAME filter; the "708 accidental g=2 multisets under an unpinned rule" warning
  (`jclass_v2` §6 C-NEG) forbids assuming `q₀=0`. `Δ₃` is measured against `q₀`, and `Q₃(J0)` is never
  read against a bare 0.
- **CM-type references (the empirical center-free / different-center nulls):** J1728 (μ₄ CM, no μ₃)
  and JGEN (no CM) carry the identical construction, pairing rule, filter, and statistic. If the
  ζ₃-membership is a genuine μ₃-center fingerprint it is ABSENT on both.

## 4. PLANTED (firing) CONTROL — must fire before any arm number is read

- **C-FIRE-ζ₃ (positive):** inject synthetic `L*` whose multiset is `{α, ζ₃α, −ᾱ, −ζ̄₃ᾱ}` (ratio forced
  to ζ₃) through the FULL downstream (embedding → census → repeated-root filter → `g₃` → certificate).
  Requirement: `I₃=1` with char-0 certificate at 100% of planted cells that survive the filter, and
  ≥1 planted cell survives. **If it does not fire, the null is uninformative — full stop (Outcome 3).**
- **C-WRONG-ORDER (negative-order):** inject `{α, ζ₄α, −ᾱ, ζ̄₄ᾱ}` (ratio forced to ζ₄, a NON-μ₃ order).
  Requirement: `I₃=0` (μ₃) at every planted cell AND the parallel μ₄ check reads `g₄≥1` certified — the
  machinery fires on the true order and stays silent on the wrong one.
- **C-PLANT / C-ORDER / C-EXACT / C-REPRO:** reused from `jclass_v2` §6, all previously PASS/FIRE; the
  runner re-asserts them on this port and prints their status.
- **C-DISJOINT (gates the EXPLORATORY GLV arm only):** before any GLV statistic is read, establish on
  the center-free surrogate that `a` and `λa` are DISTINCT monodromy cells with `ρ(λa)` NOT forced
  equal to `ρ(a)` (i.e. `λa` is not in `a`'s μ₆-coset). If this control does NOT fire, the GLV arm is a
  tautology (D-TAUT) and is retired for this run; the verdict is unaffected (it never depended on it).

## 5. POWER (numbers, pinned now)

- **Scope of n:** full rank-4 `L*` requires exact `V₁` AND `V₂` (O(p²) exact exp-sum), feasible only at
  moderate p. Frozen primes = the validated `jclass_v2` band; cells per J0 prime = `(N−1)/6` μ₆-cosets
  minus filtered cells (order 10¹–10² per prime at 30<p<250), pooled over the discovery primes
  (§6) → pooled `n` on the order of several hundred to low 10³.
- **Binomial detection (concentration vs measured q₀):** at pooled `n=1000`, α=10⁻³ (two-sided
  z=3.29), a center-free q₀: null count `= q₀·n`, sd `=√(q₀(1−q₀)n)`. Minimum detectable rate
  `q* = q₀ + 3.29·√(q₀(1−q₀)/n)`. Worked: q₀=0.01 → q*≈0.0195; q₀=0.05 → q*≈0.073; q₀=0 (exactly
  certified null) → any single certified hit is significant, `q*≈−ln(0.01)/n≈4.6×10⁻³`. Power ≥0.99 at
  `q ≥ q* + 2.33·sd/n`.
- **The center alternative is q=1 (structural):** a genuine Z/3 center forces `I₃=1` on EVERY cell, so
  the alternative is `Q₃(J0)≈1`; against any q₀<1 reference at n≥~20 the two-proportion contrast `Δ₃`
  is detected with power →1. **This is the regime the design is aimed at** and it is over-powered.
- **Discriminator power:** `Δ₃ = Q₃(J0) − Q₃(J1728)`; if center is CM-type-specific,
  `Q₃(J0)≈1, Q₃(J1728)≈q₀` → `Δ₃≈1`, detected at any n≥~20 per arm at α=10⁻³.
- **The FRACTIONAL-center regime (0<q<1) is the low-power corner and is reported as such**: below
  `q*` the run states "not distinguishable from center-free at this n" — a scoped power statement,
  not "no center."
- **OOS:** discovery primes freeze `Δ₃` sign and the certificate threshold; confirmation primes
  (held out, §6) must reproduce the sign and the arm ordering. A `Δ₃` that flips OOS = not a center.

## 6. SCOPE

- **Arms & selection rule (data-blind), reused verbatim from `jclass_v2` §2** so the validated
  pipeline and its cofactor controls apply: **J0** `y²=x³+B`, μ₆, cofactor 1 (N prime), least 2
  distinct F_p-iso classes; **J1728** `y²=x³+Ax`, μ₄, cofactor 2 (`χ₂(−A)=−1`, N=2n′, n′ prime,
  cyclic); **JGEN-1/JGEN-2** j∉{0,1728}, μ₂, cofactors 1 and 2 as the internal cofactor control.
  Cofactor cannot be matched across CM type (A1/A2/A3); JGEN-1 vs JGEN-2 measures the cofactor effect
  and **voids** the J0/J1728 comparison if they disagree (F-VOID, §7).
- **Character-order stratification:** on cofactor-2 arms every cell carries `ord(a)∈{2,n′,2n′}`;
  `Q₃` reported per order.
- **Primes FROZEN:** discovery = all `p ≡ 1 mod 12`, `30 < p < 250` (`p≡1 mod 3` for J0 ordinary,
  `p≡1 mod 4` for J1728 μ₄; `1 mod 12` matches both). Confirmation (held out, not looked at until
  discovery frozen) = `p ≡ 1 mod 12`, `250 < p < 1000`.
- **a-scope:** `a≠0` only (`0∉(ℤ/N)*`, and the a=0 anchor's rigidity is destroyed by the twist —
  `RESULT_120deg_anchor_from_mlaw_v1` §5). This reads ζ₃ as a candidate center property ACROSS a≠0
  cells; it is **NOT** a proof of the uniform 120° law over a (that is separately OPEN — context note).
- Every number the run emits carries `(arm, p-band, iso-class count, cell count, ord(a) stratum)`.
- **No crypto/extraction/ECDLP claim** anywhere; this pins π₀/center, nothing about secp's p.

## 7. FALSIFICATION (evaluated in order; first that applies is the verdict)

- **F-STOP.** C-FIRE-ζ₃ does not fire, or C-WRONG-ORDER leaks μ₃, or C-EXACT fails ⇒ null
  uninformative, **no verdict**, re-instrument. (A run that did not fire its control did not happen.)
- **F-VOID.** JGEN-1 and JGEN-2 disagree on `Q₃` ⇒ cofactor drives the statistic ⇒ the J0/J1728
  contrast is **void**; reported as void, no center conclusion.
- **F-NULLMATCH.** `Q₃(J0) ≈ Q₃(J1728) ≈ Q₃(JGEN)` all elevated together ⇒ the elevation is a
  construction/pooling artifact common to all arms, the null is mismatched, statistic uninformative
  for the center ⇒ **STOP, re-derive matched null** (do not read `Δ₃`).
- **F-CENTER-ABSENT (the falsification the task names).** `Δ₃` inside the matched-null band
  (`Q₃(J0) ≤ q₀ + 3.29·sd`) with C-FIRE-ζ₃ fired ⇒ **no finite Z/3 center detected on this signal at
  power [q*, n]**; this positively pins the center/π₀ toward **trivial-on-μ₃** at the stated scope. A
  valid, positively-stated result (no dismissal vocabulary).
- **F-CENTER-μ₃ (center detected, CM-type-specific).** `Δ₃ = Q₃(J0) − Q₃(J1728) > 0` beyond null AND
  Q₃(J1728,μ₃)≈q₀ AND Q₃(JGEN,μ₃)≈q₀, sign reproduced OOS ⇒ **nontrivial finite center containing μ₃**
  in the arithmetic monodromy signature, tracking CM-by-ℤ[ω]; report `Q̂₃` with full scope.
- **F-CENTER-strong.** additionally J1728 self-check fires μ₄ (`g₄≥1` certified) and JGEN fires
  neither ⇒ strongest characterization: **center = μ_{Aut-order}, a function of base-curve CM type.**
- **F-UNANTICIPATED.** any certified `I₃=1` on JGEN with distinct roots and `e₁≠0` (μ₃ present without
  CM), or an off-arm order not in {μ₃,μ₄} ⇒ **no verdict**, cell reported verbatim `(p,A,B,a,ord,g_k)`,
  spec reissued. (Routes an unanticipated value to a re-spec, never a post-hoc gloss.)

**Abstention is a finding, not a closure** (`feedback_prereg_abstention_is_the_finding`): F-CENTER-ABSENT
pins toward trivial at a stated power; it does not "close" the uniformity question (out of scope §6).

## 8. EXACTNESS

Signal/verdict path is int-only: `L* ∈ ℤ[T]` from exact point count / exact exp-sum; `g₃`/`g₄` via
multi-modular `deg gcd` (lower bound) + char-0 resultant certificate in `ℤ[x]/(Φ_N,Φ_k)` (exact
integer). `check_no_float.py` (C-EXACT) must pass on the ported files. **Float carve-out (analytic
size only, no key/verdict in path):** eigenangles θ as float64 enter ONLY (a) the EXPLORATORY GLV
ranking against a permutation null (C-DISJOINT-gated), and (b) reporting/plots. The verdict statistic
`Δ₃` and every `I₃` are computed entirely in exact integer arithmetic; no float threshold decides any
membership.

## 9. PRE-COMMITMENT (filled BEFORE the run)

| outcome | reading (positively stated, scoped) | grade |
|---|---|---|
| **F-STOP** | control did not fire → null uninformative, re-instrument; **no verdict** | — |
| **F-VOID** | cofactor drives `Q₃`; J0/J1728 contrast **void**; report void | — |
| **F-NULLMATCH** | elevation common to all arms → matched-null mismatch; STOP, re-derive null | — |
| **F-CENTER-ABSENT** | no Z/3 center detected on this signal at power `[q*,n]`; pins π₀/center **toward trivial-on-μ₃**, scope §6 | `[EMPIRICAL — exact, scoped, positively-stated null]` |
| **F-CENTER-μ₃** | nontrivial finite center ⊇ μ₃ in the arithmetic monodromy signature, tracking CM-by-ℤ[ω]; `Q̂₃`, scope §6 | `[EMPIRICAL — exact, scoped]` |
| **F-CENTER-strong** | center = μ_{Aut-order} as a function of base-curve CM type (J0→μ₃, J1728→μ₄, JGEN→none) | `[EMPIRICAL — exact, scoped]` |
| **F-UNANTICIPATED** | value outside {μ₃,μ₄}-per-CM-type; cell reported verbatim; **spec reissued** | — |

**Secondary / EXPLORATORY (never verdict-bearing):** the GLV-equivariance relation ρ(a)↔ρ(λa),
reported ONLY if C-DISJOINT fires, under an `EXPLORATORY` header, as structural characterization with
its own matched (a↔λa permutation) null; it cannot move the center verdict (D-TAUT).

**Would NOT license** (regardless of outcome): (i) the decomposition `H¹≅W⊕W⊗ξ` — no eigenvalue
statistic distinguishes it from its semisimplification (`jclass_v2` §0.1); (ii) uniformity in a at
secp's p (this is p<1000); (iii) any leakage/ECDLP consequence; (iv) promotion of any mechanism above
its current grade; (v) a geometric-monodromy conclusion beyond what the CM-type contrast licenses (the
arithmetic⇐geometric inference is scoped, §1).
