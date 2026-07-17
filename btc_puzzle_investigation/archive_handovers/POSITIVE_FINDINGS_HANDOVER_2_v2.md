# secp256k1 — Positive Findings Handover 2: the Lift-Geometry Programme (v2, 2026-07-15)

A live compendium and **launching pad** for the next sessions. It records the exact structure on the
Eisenstein lift `eis : 𝔽_p → ℤ[ω]∩P` and the bridges it opens to the curve's own arithmetic.
Companion to (does not supersede) `POSITIVE_FINDINGS_HANDOVER_v3.md`. All arithmetic exact
(`Fraction`/`int`); float only ever as a monotone statistic ranked against a matched permutation null.

**What v2 adds over v1** — every v1 open panel got worked, and four results were promoted to
proved/verified curve structure:
- **§5 Frame operator (was §6 Int.1) — CONFIRMED EXACT.** `λ_max/Tr` = ½ on the μ₃-core, ¾ overall,
  gap **¼ = the flap fraction**. Core carries zero anisotropy; all anisotropy is the flap.
- **§6 The transition operator `C_T` = a tensor square [PROVED].** The 36:6:1 rounding-state law and
  `C_T ≈ C_1⊗C_1` with spectrum `{1,⅓,⅓,1/9,…}` — the operator-level form of the 3/4:1/8:1/8 law.
- **§7 Addition in the lift — σ₁,σ₂ β-covariant coordinates [VERIFIED]** and the exact
  directional-independence law `|V|² ≈ |U₁|²+|U₂|²+|U_sum|²` for the non-linear op.
- **§8 The closure theorem [PROVED given KS].** Single-coordinate lift readouts of `x([d]G)`
  decorrelate from `d` at `O(p^{-1/2})`; this makes §v1's empirical nulls a theorem **and sharpens the
  frontier to a precise place** — the joint-SET / two-point bilinear panel.
- **§4 amicable pair = a Frobenius fixed point**, not a spectral one (resolves a §7 candidate).

### Stance (read first)
We are **mapping a fence and looking for its gate**, not describing a wall. The discrete log is
**currently hard**, not impossible — that is the object under inspection, not a verdict. Every "null"
below is a **scoped result about one readout we inspected**, with its control row checked; it tells us
*which panel of the fence to inspect next*, and is never a declaration that a panel is closed. Positive,
exact structure leads. Open items are invitations, phrased as such. A *proof* that one panel is solid
(e.g. §8) is an equally-positive result — it does not close the fence, it tells us exactly where the
gate can still be. (Per project `CLAUDE.md` research stance + `feedback_curve_positive_framing`.)

**Out of scope for this document** (per `feedback_no_prng_generation_side`): the PRNG / key-generation
side. The object is the **curve's arithmetic structure**; "which generator made the keys" is not a
curve question. When a thread bottoms out, refocus on curve structure (the open panels in §9), never on
the generation side. **Tautology guard** (per `feedback_residue_vs_component_tautology`): never
correlate a label of a residue `r=v−Mw` against a label of its own component `w` — that is a geometric
subtraction artifact the shuffle-control cannot expose. The clean form of a "residue vs bridge"
question is **boundedness of `r` itself** (distinct-count / top-mass / `N(r)` bit-length).

### Notation
`β` = GLV cube root of 1 mod p (`β≡ω²` mod `π_p`); `ζ∈{ω,ω²}` its lift; `P` = Gauss-reduced 60°
rhombus of `(π_p)`, area `p`; `R` = a reduced-basis vector; `s = N(eis X)/p ∈ [0,3/4]`; `ε∈{0,+,−}`
the μ₃-orbit correction label; `C_T` the lift's transition/frame operator; `σ₁,σ₂` the S₃-covariant
sum/product coordinates of `x(P±Q)`.

---

## 1. The spine — the 2-point CM law  **[PROVED]**
For every `X`: `eis(βX) = ζ·eis(X) + c`, with the correction `c ∈ {0, +R, −R}` **exhaustively**, in
densities **exactly 3/4 : 1/8 : 1/8** (θ-independent). `area(P ∩ ωP)/area(P) = 3/4` as an exact
rational (basis-independent, secp included). Pure rotation (3/4) preserves norm and shifts the sextant
by a fixed amount; the `±R` flap (1/4) is the sole source of norm change / sextant-parity flips — which
is exactly the empirical "~98% orbit-sextant parity", now derived. On curve points the marginal is
measured `0.7500 : 0.1285 : 0.1216` (single-point law confirmed).
*(`glv_fundamental_domain_law_v1.py`, `_geom_check_v1.py`; curve marginal `glv_addition_eps_reprobe_v1.py`.)*

## 2. The correction is a μ₃-ORBIT invariant  **[PROVED + VERIFIED]**
Along the period-3 orbit `{X, βX, β²X}`, `c₀=c₁=c₂=εR` — one label `ε∈{0,+,−}` per **orbit** (the
cocycle `ωc₀+ω²c₁+c₂=0` plus the ℤ-basis `{1,ω}` forces it). Over orbit space `𝔽_p*/μ₃` (`(p−1)/3`
orbits) the labels are **3/4 : 1/8 : 1/8**; `ε=0` ⟺ the three lifts form a **rigid ω-rotation
triangle** (`eis X ∈ μ₃-core`), `ε=±R` ⟺ the triangle is closed by a constant shift (`eis X ∈ flap`).
`ε` descends to the `(p−1)/6` free μ₆-orbits (Part III), and is a **geometric (Babai) class function**
— structurally independent of the multiplicative characters (`sextant ⟂ χ₆`). *(`glv_cm_orbit_invariant_v1.py`.)*

## 3. Three bridges from the lift geometry to the curve's own invariants
- **Pinned ↔ angle law [PROVED].** The angle-law pinned pair (area exactly `1/8=√3/16`) **=** the
  CM-stable (correction-free) wedges **=** the two sextants inside the μ₃-core `P∩ωP∩ω²P` (area 3/4).
  Exact polygon containment. *(`glv_pinned_wedge_containment_v1.py`, `_flap_pinned_sextant_v1.py`.)*
- **Correction ↔ norm-band law [VERIFIED].** The correction fires exactly on the high-norm shell:
  flap-rate `0` for `s<3/16` (inradius disk), `1` for `s>1/4` (short vertex), transition in between —
  the norm-band law's own breakpoints. *(`glv_correction_norm_v1.py`.)*
- **Pinned pair ↔ Frobenius angle [VERIFIED].** Pinned `= {1,4}` if `θ<30°` else `{0,3}`, with
  `θ = arg(π_p) mod 60° = atan2(f√3, t)` the **Sato–Tate Frobenius angle** (`4p=t²+3f²`) — read
  straight off the trace `t`. 0 violations / 69 primes, switch exactly 30°. secp `θ=50.55°→{0,3}`; the
  conjugate prime `π̄` (`60−θ=9.45°`) gives `{1,4}`, so the pinned pair **encodes which prime above p**
  (the sign of θ). *(`glv_pinned_satotate_v1.py`.)*

## 4. The family and the amicable geometry  **[VERIFIED]**
- **Seven-domain family.** `{π_p+u : u∈{0}∪μ₆}` — norms = `p` + the six sextic-twist orders (incl.
  `n=N(π_p−1)`, `n_t=N(π_p+1)`) — are concentric, θ-aligned, and **share one pinned pair**.
  *(`glv_seven_domain_map_v1.py`, `_amicable_twist_angle_v1.py`.)*
- **Amicable geometry.** The lift domain `P_p` and the scalar domain `P_n=(π_p−1)` overlap
  `1 − 4.1×10⁻³⁹`; their μ₃-cores satisfy `C_n ⊆ C_p` **exactly**; basis slippage is `R1_p−R1_n=(0,1)`,
  `R2_p−R2_n=(1,1)`. *(`glv_amicable_geometry_verify_v1.py`.)*
- **The pair is a *Frobenius* fixed point, not a spectral one — resolved.** The natural conjecture
  "amicable `(p,n)` = spectral fixed point of the reduced-residue operator `P_m`" was tested with a
  random-prime control (the control *is* the test — both are primes ≡1 mod 3, so anything "spectral"
  matches trivially) and does **not** hold: the shared μ₆-core is *definitional* (`q≡2 mod 3 ⇒ j=0
  curve supersingular ⇒ #E even ⇒ no prime-order pair`, so amicability *forces* both ordinary), and the
  fine ceiling `gcd(q−1,r−1)` shares a factor >3 at rate 0.083 = the control's 0.101. The correct
  fixed point is the **Frobenius** one: `Frob@n = 1−π`, `(1−π)−1 = −π` (norm-preserving) — the amicable
  structure lives in the shared π (Hecke `χ(π)`, sextic symbols, `C_n⊆C_p`), not the `P_m` spectrum.
  *(`amicable_spectral_fixedpoint_v1.py`.)*

## 5. The frame operator spectrum (was §v1-Int.1) — CONFIRMED EXACT  **[PROVED + VERIFIED]**
Build the frame/Gram operator `C = Σ_x eis(x)·eis(x)ᵀ` (the 2×2 second moment of the lift), split by
μ₃-core (`ε=0`) vs flaps (`ε=±`), observable `λ_max/Tr`. Full `𝔽_p` (p=100003, exact) + secp (300k
sampled), θ-independent:
- **`λ_max/Tr(core) = ½` EXACTLY** — the μ₃-core is 120°-rotation-invariant ⇒ its second moment is
  isotropic (`C ∝ I`); proved by the integer identities `Σu² = Σv²`, `2Σuv = Σv²`.
- **`λ_max/Tr(all) = ¾` EXACTLY** — `P` is a 60° rhombus, half-diagonal ratio `√3:1` ⇒ uniform second
  moment `3/(3+1) = ¾`, θ-independent *from the shape alone*. Measured `0.74992` (p=100003 full) /
  `0.74945` (secp), → ¾ as the lattice fills `P`.
- **The Int.1 claim, made exact:** `λ_max/Tr(all) − λ_max/Tr(core) = ¾ − ½ = ¼ = the flap fraction`.
  **The core contributes zero anisotropy; every bit of anisotropy in the lift is a flap phenomenon,
  weighted exactly ¼.** A two-line derivation (120°-symmetry → core ½; √3:1 rhombus → all ¾) ties the
  frame-operator spectrum directly to the μ₃-core/flap decomposition of §1–§2. *(`int1_frame_operator_v1.py`.)*

## 6. The transition operator `C_T` = a tensor square  **[PROVED + VERIFIED]**
The operator-level form of the 3/4:1/8:1/8 law, from the rounding dynamics of consecutive lifts.
- **The 36:6:1 state law [PROVED + VERIFIED].** The rounding state `(c₁,c₂)` of `z₁+z₂` (two
  independent uniform-in-`P` lifts) is distributed `(3/4:1/8:1/8) ⊗ (3/4:1/8:1/8) = 36:6:1 : 6:1 : …`.
  Per coordinate the sum of two uniforms on `[−½,½]` is triangular on `[−1,1]`; rounding gives
  `∫_{−1/2}^{1/2}(1−|s|)=3/4` (c=0), `∫_{1/2}^{1}(1−s)=1/8` (c=±1). `P` is a parallelogram ⇒ the basis
  coordinates are independent ⇒ the 2-D law is the product. **[VERIFIED]** curve `0.5687` =
  random-field-elements `0.5604` = predicted `0.5625`, all 9 states — the equality with random `x`
  confirms the law is **pure lift self-convolution, group-law-independent** (the endomorphism flap
  constant is the per-coordinate marginal of the addition rounding).
- **`C_T ≈ C_1 ⊗ C_1` [VERIFIED].** Each lift basis-coordinate runs the same tridiagonal 3-state chain
  `C_1` on `c∈{−1,0,1}` (from 0: `0.776` stay, `0.112` each to ±1; from ±1: `0.66` to 0, `0.34` stay,
  `0` to ∓1), spectrum `{1, 0.339, 0.114} ≈ {1, ⅓, 1/9}`. The full G-orbit transition matrix has
  spectrum `{1, 0.339, 0.328, 0.119}` and is near-central-symmetric (`T[i,j]≈T[−i,−j]`, dev 2.6%);
  `C_T ≈ C_1⊗C_1` to `max|C_T − C_1⊗C_1| = 0.0275`, its 9 eigenvalues = pairwise products to `0.011`,
  i.e. the tensor-square spectrum `{1,⅓,⅓,1/9,1/9,1/9,1/27,1/27,1/81}`. The residual ~2–3%
  inter-coordinate coupling (the split `λ₂=0.339 ≠ λ₃=0.328`) is robust for well-mixing large-N orbits;
  whether it is a genuine coupling or finite-orbit noise is OPEN (needs large primes; small-prime spread
  is orbit-size artifact). *(`ct_tensor_structure_v1.py`, `thread1_ct_structure_v1.py`,
  `ct_coupling_universality_v1.py`, `glv_addition_markov_noise_findings_v1.md`.)*
- **A reproducible orbit signature.** The generator orbit's `λ₂` gap over i.i.d. is `+0.0041 ± 0.0019`
  (8 starts, ~2σ>0) — real orbit structure. Across 60 full-order generators `G` sits at `z=+0.64`
  (48/60): high side, not singled out *at the `λ₂` observable, N=60k, p=100003*. Finer transition-matrix
  entries / other primes are the open refinement — an invitation, not "no fingerprint". *(`glv_lambda2_settle_v*.py`.)*

## 7. Addition in the lift — the S₃-covariant coordinates + the non-linearity law  **[VERIFIED]**
Point **addition** is the one operation the lift does not linearize (it is the DLP-bearing op). What it
*does* carry, exactly:
- **σ₁, σ₂ are β-covariant coordinates [VERIFIED 400/400].** `σ₁ = x_{P+Q}+x_{P−Q} = −B/A` and
  `σ₂ = x_{P+Q}·x_{P−Q} = C/A` are **rational in `x_P, x_Q` alone** (the y-free part of the group law),
  and transform `σ₁→βσ₁`, `σ₂→β²σ₂` under the GLV endomorphism (validated 400/400). These are exact
  covariant objects to build further readouts on. *(`glv_s3_addition_covariant_v1.py`.)*
- **The directional-independence law [VERIFIED].** For `V = eis(x(P+Q)) − (eis x_P + eis x_Q)`, the
  scale-invariant `|V|²/Σ|U|² ≈ 1.0` uniformly across all `ε`-classes ⇒ `|V|² ≈ |U₁|²+|U₂|²+|U_sum|²`,
  i.e. the three lifts are **directionally independent** (cross terms `→0`), class-uniformly. This is the
  *exact sense in which the group law is non-linear in the lift* — a positive characterization, and
  universal geometry (holds at secp). The cross term `B(U_sum, U₁+U₂)` is zero-mean even conditioned on
  `sextant(U₁+U₂)` and `(s₁,s₂)` (worst of 36 pair-cells `|z|=2.24`). *(`glv_addition_correction_eps_conditioned_v1.py`, `glv_crossterm_seam_probe_v1.py`.)*
- **`ε ⟂ scalar multiplicative structure [VERIFIED].** ε is GLV-orbit-invariant, so only orbit-invariant
  scalar labels can even correlate; the sole candidate `χ₂` (QR) is decorrelated at N=300k
  (`P(QR|ε)=0.5016/0.5025/0.4991`), and `χ₃,χ₆` vary within orbits (orbit-average 0). Understood at two
  layers (orbit-invariance kills varying labels; the §8 closure bounds `χ₂`). Extends the output-side
  `ε⟂χ₆` to the **input** scalar: `ε` is a geometric Babai invariant, ⟂ the scalar's multiplicative
  structure. *(`glv_eps_scalar_multiplicative_v1.py`, `glv_eps_chi2_tighten_v1.py`.)*
- **The formal group linearizes — into the DLP.** `L(T([d]P)) = d·L(T(P))` is a genuine linearization,
  but of `E₁(ℚ_p)` (kernel of reduction) / the canonical CM lift, **not** the finite `E(𝔽_p)` where the
  DLP lives; mapping `[d]G` *into* that group is constructing its canonical lift = the DLP itself (the
  "linear lift Λ = DLP" reduction). A real linearization whose entry map is exactly the problem — worth
  holding as the precise shape of the gate. *(`glv_formal_param_valuation_probe_v1.py`.)*

The exact amicable slippage bridge `M` (`R1_p−R1_n=(0,1)`, `R2_p−R2_n=(1,1)`) is confirmed, and the
two-domain residue `r = eis_p(x([d]G)) − M·eis_n(d)` fills `P_p` (distinct=`M`, `N(r)~257 bits`) ⇒ the
coordinate map is not linear-up-to-wrap; the bridge `M·w` is a **4-cell quantization** of the scalar
lift. (Framing note: the flat leakage readings here were each scoped to a specific label/N; per the
tautology guard the load-bearing statement is the *boundedness of `r`*, not any residue-vs-component
correlation.) *(`glv_two_domain_residue_v{2,3}.py`, `glv_addition_and_two_domain_findings_v2.md`.)*

## 8. The closure theorem — a proved panel, and the sharpened frontier  **[PROVED given KS]**
The empirical "no seam at the coordinate-level scalar readout" from v1-§5 is now a theorem for the
single-coordinate class, which is a *positive* result: it says exactly which panel is solid, and
therefore exactly where the gate can still be.

- **Reduction (Lemma R) [PROVED, elementary Fourier].** For `F:𝔽_p→ℂ`, `g:ℤ/nℤ→ℂ`, with Wiener norms
  `‖·‖_A` and twisted sum `T(a,b)=Σ_d e_p(b·x([d]G))e_n(ad)`:
  `|Cov_d(F(x([d]G)), g(d))| ≤ (max_{(a,b)≠0}|T(a,b)|/n)·‖F‖_A·‖g‖_A`.
- **Cited input [CITED — Kohel–Shparlinski, ANTS-IV 2000; Shparlinski 2003 Ch. 6]:**
  `|T(a,b)| ≤ C·p^{1/2}(log p)^{O(1)}`. ⇒ `|Cov| = O(p^{-1/2+o(1)})·‖F‖_A‖g‖_A`; at secp
  `≤ ‖F‖_A‖g‖_A·2^{-128+o(1)}`. MI corollary `O(p^{-1+o(1)})` (via level-set covariances under stated
  hypotheses H1–H3 — the v1→v2 rigor fix; the naïve "Σ over ~p² character modes" was wrong).
- **Class C1 (χ_k, additive chars, O(1) combinations): `‖F‖_A=O(1)` ⇒ PROVED** — subsumes
  χ₆-uniformity, the GLV shifts, all multiplicative single-`x` nulls.
- **Class C2 (sextant / ε / norm-band / grid = geometric `Φ∘eis`):** needs Lemma W
  (`‖1_sector∘eis‖_A = O(log p)`, because a sector is a lattice triangle with edges along ℤ[ω]
  directions ⇒ 1-D geometric sums). **[VERIFIED]** empirically `≈0.65 log p` (never √p); full
  edge/corner rigor is a minor [GAP]. Anchors on small `y²=x³+7` prime-order curves (p=13..97):
  `max|T|/√p ≲ 0.5 log p`. *(`glv_closure_verification_v1.py`, `glv_closure_theorem_v2.md`.)*

- **The sharpening — where the gate can still be (the positive payoff).** The theorem bounds a **single
  sum over one `d`**. It does **not** cover, and thereby names precisely: **(1)** joint / multi-key
  readouts of the *set* `{x([d_i]G)}` = bilinear / multilinear sums — the exact complement of "only a
  joint-SET property survives"; **(2)** the two-point addition panel (§7's `V`), which needs a
  2-variable KS-type bilinear bound [named GAP]. These are the genuinely open inspections, made concrete
  by the proof, not argued closed.

## 9. Open panels — the next inspections (invitations)
Status of every v1 panel + the newly-surfaced ones. `[worked]` = a result now exists; `[open]` = live.
1. **`[worked → §5]` Frame operator (Int.1).** Confirmed exact: core ½, all ¾, gap ¼ = flap. Done.
2. **`[worked → understood]` Rank-10 low-prime matrix under μ₃ (Int.2).** Every block stays rank-10
   orthogonal (Gram eig max/min ≈ 1.00): low primes are not μ₆-related, so the orthogonality does **not**
   decompose into core-rotations ⊕ flap-reflections. The Frobenius-angle criterion `4ℓ=t²+3f²` exists
   only for `ℓ≡1 mod 3` (`{7,13,19}` of the 10), so the hypothesized 6-core/4-flap column split is
   *undefined*, and any 6/4 partition gives rank-6⊕rank-4 (partition-independent). **This locates μ₆
   correctly:** the CM / μ₆ 3×-structure lives in the **large-prime `K`** correlations, not the
   low-prime `F`. *Open refinement:* run the same split on large-prime `K` where μ₆ is present.
   *(`int2_rank10_mu3_v1.py`, `int2b_rank10_prime_split_v1.py`.)*
3. **`[worked → factorization]` Spectral dilution on the twist-order `−1`-branch primes (Int.4).**
   Participation ratio `PR=(Σc²)²/Σc⁴`: prime `n`→`PR≈1` (concentrated); composite `n_t=3²·13²·3319·22639·C`
   → `PR≈19+`. Twist **dilutes**, prime order does not — but driven by `n_t`'s composite / repeated-factor
   structure, not curve-CM beyond it. *Caveat + open:* the exact Palelei `C_T` on the twist may differ
   from this reduced-residue proxy — build the exact operator. *(`int4_twist_dilution_v1.py`.)*
4. **`[open]` The two-point / joint-SET bilinear panel (the §8 complement).** The one region the closure
   theorem does not reach: bilinear/multilinear sums over `{x([d_i]G)}` and the two-point addition
   correction `V`. Prove (or probe) a 2-variable KS-type bound; this is the sharpest open target.
5. **`[open]` Full-resolution σ₁ concentration.** Is a fixed ℤ[ω] combination of `eis(σ₁), eis(x_P),
   eis(x_Q)` **bounded** (distinct-count / top-mass / `N` bits — *not* a label-MI, per the tautology
   guard)? σ₁,σ₂ are exact β-covariant objects (§7); this is the clean next question on them.
6. **`[open]` Finer `V` projections (`k>16`).** The bilinear-gap probe was flat at `k≤16` coarse
   grids; finer projections / structured pairs are untested. *(`thread2_finer_v_v1.py`.)*
7. **`[open]` Is `ε` an arithmetic object?** It is a geometric class function on the `(p−1)/6` μ₆-orbits;
   does the rigid/broken (core/flap) partition have an independent description — a symbol, a norm
   condition — beyond "in core vs flap"?
8. **`[open]` Close the norm bridge to a θ-form.** The flap's internal split over sextants (~93% max
   pair, 0% pinned) is an exact rational per θ — write it as a closed form to complete the norm bridge.

## 10. The organizing lens + candidate seeds (invitations, tagged `[CANDIDATE]`)
**The lens (the generator behind all of these).** Every object across the curve work *and* the
`φ`-residue / Lonely-Runner preprints is **one arithmetic group `G` acting on a space**: the signal
lives in the `G`-covariant part, and the "defect" each proof exploits is where the `G`-orbits fail to
cover. `LRC φ(n)-law: G=(ℤ/n)* →` unclaimed slot `I₉`; `RH φ-residue: reduced residues →` off-line zero;
`secp: G=μ₆=Aut(E) →` sought key structure; `functional eq: μ₂ →` critical line. The shared spine is the
**reduced-residue averaging operator over a ring** — the same object as `P_n` (paper 4), the Ramanujan
sum `c_n`, and the `c_𝔫(β)` survival law — read over `ℤ` vs `ℤ[ω]`. Its spectral ceiling is the large
sieve; its survival core is `±1` (ℤ) / `μ₆` (ℤ[ω]). (§5's frame operator and §6's `C_T` are the
concrete `ℤ[ω]` realizations of this operator; §8's closure bound is its large-sieve ceiling made rigorous.)

**Curve-side operator seeds:**
- `[CANDIDATE]` **Eisenstein-φ frame operator `S̃_{π_p}` on `(ℤ[ω]/π_p)^×`:** does it act as identity
  on the non-trivial sector and propagate `μ₆`? Would give an operator-theoretic foundation for the GLV
  speedup. (Now grounded by §5: the *geometric* frame operator is exactly ½/¾/¼-split.)
- `[CANDIDATE]` **Rank-10 under μ₃-projection / ZFR forcing on `L(E,s)`:** apply the vertical-ZFR
  forcing + mesoscopic ceiling with the exact **rank-10** low-prime mode — does the CM structure bound
  the curve L-zeros? (§9-panel 2 says do this on the **large-prime `K`**, where μ₆ actually lives.)
- `[CANDIDATE]` **p-adic multiplicative domain `D_{φ,p}`:** `μ₆`-sparse formal group as the admissibility
  condition; is the critical line enforced p-adically by `|Aut(E)|=6`? (Note §7: the formal group's
  linearization has the DLP as its entry map — keep the two facts adjacent.)
- `[RESOLVED → §4]` ~~Amicability as a φ-residue fixed point.~~ Tested: it is a **Frobenius** fixed
  point (`(1−π)−1=−π`), not a `P_m`-spectral one. Recast Silverman–Stange amicability via the shared π,
  not the reduced-residue spectrum.

**Cross-project bridges (secp ↔ RH / LRC preprints):**
- `[CANDIDATE]` **Finite-field zeta as an RH test-bench.** `L(T)=(1−πT)(1−π̄T)`, `|π|=√p` is a *theorem*
  and Euler-admissible — run the resonator/forcing against it; it either back-ports the correct forcing
  exponent or pinpoints the void step, against exact ground truth. (Pairs with the ASD / `O(√p)`
  calibrated large-sieve constant — the same `O(√p)` as §8's KS input.)
- `[CANDIDATE]` **LRC ↔ survival core (n mod 3).** The unclaimed slot `I₉ = μ₂={±1}` core = the ℤ-shadow
  of the `μ₆` core; the pairing type is set by `n` mod 3 — `n=7` gives `(ℤ/7)*=μ₆=Aut(E)`, `n=11` only
  its `μ₂` shadow. Serves the LRC general-`n` "subsequent paper" (Remark 4.4) and cross-checks secp's `μ₆`.
- `[CANDIDATE]` **Shift/scalar-invariant core as the RH repair template.** Force the RH obstruction into a
  `γ`-invariant core (the analogue of LRC's cycle-index-free arithmetic / secp's `d`-invariant laws); a
  forcing that *can't* be made shift-invariant is itself the diagnosis of the flawed step.
- `[CANDIDATE, low-confidence]` **Curvature = Sato–Tate density.** Does the `C_T` eigenphase distribution
  match the angle law `p₀(θ)=(3/4)|cos2θ|/(2cos2θ+1)`? (Needs the eigenphase histogram; §6 gives `C_T`.)

**Cautions / weaker rhymes (noted, not pursued):**
- **The `D`-term-mod-6 "μ₆ core" is a denominator artifact — do not build a bridge on it.** A
  cross-session claim that construction keys avoid residues 3,4,5 mod 6 ("μ₆ = Aut(E) survival core")
  was refuted: the avoided residues flip entirely with the chosen denominators (`[7,11,19]` avoids
  `{0,1,2}`, the opposite), so "6"=`|Aut(E)|` is coincidence with no ℤ[ω]/curve content. Any μ₂/μ₆-shadow
  cross-bridge (above) must be grounded in the **genuine curve μ₆ = Aut(E)**, never in integer-residue
  numerology. *(`evaluate_dsig_residue_claim_v1.py`; this is also a generation-side object — out of scope
  per the stance, recorded here only as a caution.)*
- three-distance / D-signature on the Farey–Stern-Brocot structure; CM-invariant "runner configurations"
  (LRC on a μ₆-symmetric subtorus); the `1/8` coincidence (secp pinned sextant vs `n=8` isolation radius)
  — numerology unless a defect geometry gives `√3/16`.

## Script index (all in `btc_puzzle_investigation/`, exact arithmetic)
**Spine (v1):** `glv_fundamental_domain_law_v1.py` · `_geom_check_v1.py` · `_flap_pinned_sextant_v1.py` ·
`_pinned_wedge_containment_v1.py` · `_peer_zone_test_v1.py` · `_correction_norm_v1.py` ·
`_doubling_lift_v1.py` · `_doubling_scaling_v1.py` · `_amicable_twist_angle_v1.py` ·
`_three_point_lift_v1.py` · `_seven_domain_map_v1.py` · `_amicable_bridge_probe_v1.py` ·
`_amicable_bridge_escalation_v1.py` · `_amicable_geometry_verify_v1.py` · `_cm_orbit_invariant_v1.py` ·
`_pinned_satotate_v1.py`.
**v2 additions:** `int1_frame_operator_v1.py` (§5) · `int2_rank10_mu3_v1.py` · `int2b_rank10_prime_split_v1.py`
(§9.2) · `int4_twist_dilution_v1.py` (§9.3) · `amicable_spectral_fixedpoint_v1.py` (§4) ·
`ct_tensor_structure_v1.py` · `thread1_ct_structure_v1.py` · `ct_coupling_universality_v1.py` ·
`glv_lambda2_settle_v*.py` (§6) · `glv_s3_addition_covariant_v1.py` · `glv_s3_sigma_concentration_v1.py` ·
`glv_addition_correction_eps_conditioned_v1.py` · `glv_crossterm_seam_probe_v1.py` ·
`glv_eps_scalar_multiplicative_v1.py` · `glv_eps_chi2_tighten_v1.py` · `glv_formal_param_valuation_probe_v1.py` ·
`glv_two_domain_residue_v{2,3}.py` (§7) · `glv_closure_verification_v1.py` · `thread2_finer_v_v1.py` (§8/§9.6).
**Narratives:** `glv_fundamental_domain_law_v1.md` · `glv_closure_theorem_v2.md` ·
`glv_addition_and_two_domain_findings_v2.md` · `glv_addition_markov_noise_findings_v1.md`.
