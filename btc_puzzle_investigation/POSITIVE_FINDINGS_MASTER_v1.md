> **⛔ FROZEN — NOT CURRENT.** This file is a historical snapshot. The single current-state
> document is **`CLAIMS.md`**. Do not read status, grades, or open items from here; do not
> write a successor version of this file. (Frozen 2026-09-01.)

# secp256k1 — Master Positive-Findings & Structure Compendium (v1, 2026-07-17)

**Consolidates and supersedes Handovers 1–4** (`POSITIVE_FINDINGS_HANDOVER_{,2_,3_,4_}v*`). One
document: everything we **know** (proved / verified) about the secp256k1 curve's arithmetic
structure, laid out positive-first and code-ready. Empirical nulls and heuristics are Appendices A–B,
each a **scoped fact with its firing control — never a closure by declaration**. Where a bound
appears it is a **magnitude**, not "no structure."

**Stance.** Mapping a fence and locating its gate — the DLP is *currently* hard, the object of study.
Positive exact structure leads. A *proof* that a panel is solid (e.g. the closure, Part V) is an
equally positive result: it says exactly where the gate can still be. Out of scope: the PRNG /
generation side (a curve question only). Signal-path arithmetic exact (`int`/`Fraction`); float only
as an analytic-size character-sum magnitude or a monotone statistic vs a matched permutation null.

**Grades:** `[PROVED]` rigorous · `[PROVED|KS]` given the cited Kohel–Shparlinski/Weil bound ·
`[VERIFIED]` exact/numeric at tested scale · `[CITED]` literature · `[HEURISTIC]`/`[EMPIRICAL]` (App.).

---

# PART I — CONSTANTS & CODE-READY DEFINITIONS

```
p = 2^256 − 2^32 − 977                                              (field prime, p≡1 mod 6)
n = 0xFFFF...BAAEDCE6AF48A03BBFD25E8CD0364141                       (group order, prime)
E : y^2 = x^3 + 7   (j=0, CM by Z[ω], ω=e^{2πi/3}, |Aut(E)|=6)
t = p+1−n = 432420386565659656852420866390673177327               (Frobenius trace)
π = a + bω,  a = 367917413016453100223835821029139468249,
             b = 303414439467246543595250775667605759171,  N(π)=p, 2a−b=t
4p = t^2 + 3f^2,  f = 3·79·349·2698097·1359580455984873519493666411 (90-bit tail prime)
p−1 = 2·3·7·13441·C ;  n−1 = 2^6·3·149·631·107361793816595537·174723607534414371449·34194...
π_n = π−1  (prime above n; N(π−1)=n).  n_t = 2(p+1)−n = 3^2·13^2·3319·22639·C' (quad-twist order)
Reduced ℤ[ω]-basis of L=(π_p):
 R1=(−303414439467246543595250775667605759171, 64502973549206556628585045361533709078)
 R2=( 64502973549206556628585045361533709078, 367917413016453100223835821029139468249)
```
- **Curve/scalar.** `d ↔ [d]G=(x_d,y_d)` bijection `ℤ/n ↔ E(F_p)` (full order n). Imports:
  `ecc_secp256k1` (`P=p`, `N_ORDER=n`, `scalar_mul`); `int1_frame_operator_v1.build(p)→(eis,eps)`;
  `lift_sextant_rhombus_law_proof_v2.reduced_basis(p)→(R1,R2)`.
- **Characters.** `e_p(t)=exp(2πi t/p)`, `e_n(t)=exp(2πi t/n)`; `χ_k(a)=a^{(p-1)/k}` → k-th roots of
  1 (`χ₂`=Legendre). Curve character `χ_a(P):=e_n(a·d(P))` — the DLP frequency.
- **Eisenstein lift.** `eis(x)` = rep of `x∈F_p≅ℤ[ω]/(π_p)` in the 60° rhombus `P={uR₁+vR₂:u,v∈[−½,½)}`.
  Exact coeffs: `DET=R₁[0]R₂[1]−R₁[1]R₂[0]`, `u=(z₀R₂[1]−z₁R₂[0])/DET`, `v=(z₁R₁[0]−z₀R₁[1])/DET`,
  `z=eis(x)`; norm `N(z)=u²−uv+v²`, `s=N(eis x)/p∈[0,¾]`. Flap `ε(x)=eps(x)∈{0,±}`.
- **GLV/CM.** `β=g^{(p-1)/3} mod p` (β≡ω² mod π_p), `λ∈ℤ/n`, `λ³=1`, `x_{λd}=β·x_d`; μ₃=⟨β⟩ on x;
  μ₆=Aut=⟨β,−1⟩; [−1] fixes x, negates y. `eis(βx)=ω·eis(x)` reduced.
- **Cap/flap.** `flap ⟺ |u−v|>½` (orientation `|u+v|>½` at some primes — detect vs ε). `σ(x)=sign(u−v)`
  on flap else 0. Sextant = 60°-sector of eis(x).
- **Twisted sums.** `T(a,b)=Σ_d e_p(b x_d)e_n(a d)`; `U(a,b,c)=Σ_d e_p(b x_d+c y_d)e_n(a d)`, `T=U(·,·,0)`.
  `Corr_F(a)=(1/n)Σ_d F(P_d)e_n(-a d)`. **`xy:=x·y`** — ODD in d, μ₃-weight 1. `s_y=+1 if y<p/2 else −1` (ODD).
- **Semaev.** `S₃(a,b,c)=(a−b)²c²−2((a+b)(ab)+2·7)c+((ab)²−28(a+b))`; `S_{m+1}` by resultants.
- **Key coordinate.** `A=2^{bits−1}`, `band_offset=d−A`; `(n,k)`=`argmin_{n≤256}|n(d−A)−kA|`;
  `derr=|n(d−A)−kA|`; `D_terms`=greedy unit-fraction (invertible d-signature); curve-identity `D` in
  `[n]P=(n+k)Q+(n·D)G`, `r=nD−(2^{N−1}k mod n)`. Datasets: `solved_keys_augmented_v1.csv` (82, known d),
  `constructed_keys_fullrange_v1.csv` (36k, known d, +`a_glv,b_glv,sextant,chi6X/Y,chi2Y`), `..._100k_exact.csv`.
- **Transfer operator.** label `l(d)`; `M[i,j]=#{d:l(d)=i,l(d+1)=j}/#{d:l(d)=i}`; `|λ₂|~1/√n`=thermal.
  Valid null = ABSOLUTE `|λ₂|` decay + multi-shuffle z (NOT shuffle-ratio on 2-state, NOT `np.roll`).

---

# PART II — THE EISENSTEIN LIFT LAWS  `[PROVED]`

- **Rhombus theorem (universal).** Both reduced basis vectors have norm exactly `p`; `P` is a **60°
  rhombus**, edge `√p`, area `p√3/2`. `eis` bijects `F_p → ℤ[ω]∩P` uniformly. (300 primes + secp.)
- **One-parameter angle law.** Sextant histogram = function of `θ=arg(π_p) mod 60°`; opposite sectors
  equal; three pairs sum ½. **Pinned pair = exactly `1/8` (= √3/16, θ-independent)**; free
  `p₀(θ)=(¾)|cos2θ|/(2cos2θ+1)`, `3/8−p₀`. secp pinned `{0,3}`, θ=50.55°.
- **Norm-band law.** `s=N(eis x)/p` universal: support `[0,¾]`, **mean `1/6` exactly**, density `2π/√3`
  on `[0,3/16]`, breakpoints `3/16, ¼, ¾`.
- **All nontrivial `χ_k` exactly uniform** (fibers `(p−1)/k`); `Σζ₆^{χ₆}=0`.
- **GLV = lift × cube-root.** `φ(x,y)=(βx,y)`, β≡ω²; `χ₆(βx)=χ₆(x)+4`, `χ₃(βx)=χ₃(x)+1`, χ₂ fixed;
  orbit-sextant ~98% same parity.
- **Summation-poly [ω]-covariance.** `S₃(βx)=β·S₃` (weight 1); `S₄(βx)=S₄` (weight 0, invariant);
  irreducible/ℚ(b), degree `2^{m−2}` per var. `y`: `χ₂(y_{n−d})=−χ₂(y_d)`, `f(λd)=f(d)`.
- **Cap Law.** `ε(x)≠0 ⟺ |u−v|>½`; forced by hexagonal geometry (ω-matrix `M=[[0,−1],[1,−1]]`);
  core/flap densities ¾ : ⅛ : ⅛; shape constants (½,¾,33,3/16,¼,1/6) are θ-independent lattice geometry.
- **σ μ₃-invariant** (`σ(βx)=σ(x)`, unconditional) + `σ(−x)=−σ(x)` ⇒ σ = μ₂-isotypic part of μ₆.

*(`lift_sextant_rhombus_law_proof_v2.py`, `lift_chi6_uniform_law_proof_v1.py`, `norm_band_law_proof_v1.py`,
`glv_orbit_structure_proof_v1.py`, `cap_law_proofs_v1.md`.)*

---

# PART III — CM / ENDOMORPHISM / L-FUNCTION / TWIST / AMICABILITY  `[PROVED / VERIFIED / CITED]`

- **`End(E)=ℤ[ω]`, maximal** (φ²+φ+1=0 ⇒ ℤ[ω]⊆End; h(−3)=1). **μ₆ acts FREELY** on `E\{O}`:
  `(n−1)/6` free orbits. **MOV embedding degree `ord_n(p)=(n−1)/6` (254-bit)** — sextic index 6=|μ₆|
  again (`ord_n(2)=(n−1)/64`, `ord_p(t)=(p−1)/6`). Isogeny class all order n [CITED Tate].
- **Sextic identities.** `u=−1` is the unique unit with `N(π+u)=n`; `π_n=π−1`; sextic classes
  `[7/π_p]₆=ζ₆⁵`, `[7/π_n]₆=ζ₆`; exact 4-D character `ε=ζ₆^{3−[28/π]₆}`. Frobenius angle
  `cosθ=t/(2√p)=0.6354`, θ=50.55°.
- **L-function & its RH.** `L(T)=1−tT+pT²=(1−πT)(1−π̄T)`, **`|π|=√p`** (Hasse=Weil, a theorem) ⇒ zeros
  on `Re(s)=½`. Supersingular `a_ℓ=0 ⟺ ℓ≡2 mod3`.
- **Formal-group logarithm (exact).** `L(T)=Σ_{k≥0} 7^k·C(3k,k)/(6k+1)·T^{6k+1}` — **μ₆-sparse**
  (exponents ≡1 mod 6, forced by Aut(E)); family `Σ b^k C(3k,k)/(6k+1)T^{6k+1}` for `y²=x³+b`.
  Formal group law `F(T₁,T₂)=T₁+T₂−7(3T₁T₂⁶+…)`, no linear cross-term, μ₆-sparse. **`L(T[d]P)=d·L(T P)`**
  linearizes `E₁(ℚ_p)` (the reduction kernel) — *not* `E(F_p)`; mapping `[d]G` into it = the DLP.
- **ASD / Honda bridge.** At split `ℓ=6k+1`: `7^k·C(3k,k)≡a_ℓ (mod ℓ)` (supercongruence, 147/147).
- **Twist structure.** Six sextic twists (Frobenius `u·π_p`, u∈μ₆); **b=7 ↔ u=1+ω unique prime-order**;
  quad-twist `n_t=2(p+1)−n`. **Frobenius sieve:** `ℓ|n_t ⟺` Frobenius eigenvalue `−1 mod ℓ`.
- **Amicability.** `(p,n)` is an amicable pair: `#E(F_n)=p` exactly. It is a **Frobenius fixed point**
  `(1−π)−1=−π` (norm-preserving), NOT a reduced-residue-spectral one; the coordinate map φ:E(F_p)→F_n **is
  the DLP** (transfers no advantage). Amicable geometry: `P_p`,`P_n=(π−1)` overlap `1−4.1e−39`, `C_n⊆C_p`
  exactly, slippage `R1_p−R1_n=(0,1)`, `R2_p−R2_n=(1,1)`.

*(`sextic_identities_verify.py`, `secp256k1_Lfunction_intersections.md`, `secp256k1_formal_group_finding.md`,
`secp256k1_arithmetic_v4.md`, `cm_twist_order_divisibility_*`, `cm_amicable_correspondence_v1.py`,
`amicable_spectral_fixedpoint_v1.py`.)*

---

# PART IV — THE LIFT-GEOMETRY PROGRAMME (2-point CM law, frame operator, C_T)  `[PROVED / VERIFIED]`

- **The 2-point CM law (spine).** `eis(βX)=ζ·eis(X)+c`, `c∈{0,+R,−R}` **exhaustively**, densities
  **exactly ¾ : ⅛ : ⅛** (θ-indep); `area(P∩ωP)/area(P)=¾`. Pure rotation (¾) preserves norm/shifts
  sextant; the `±R` flap (¼) is the sole norm-change / sextant-parity flip.
- **The correction is a μ₃-ORBIT invariant.** One label `ε∈{0,+,−}` per orbit `{X,βX,β²X}`; over
  `F_p*/μ₃` the labels are ¾:⅛:⅛; ε=0 ⟺ core, ε=± ⟺ flap; a geometric (Babai) class function, ⊥ χ₆.
- **Three bridges.** pinned ↔ angle-law (`⅛=√3/16` = CM-stable wedges = μ₃-core sextants); correction ↔
  norm-band (flap-rate 0 for s<3/16, 1 for s>¼); **pinned pair ↔ Frobenius angle** (`{1,4}` if θ<30° else
  `{0,3}`; encodes which prime above p; 0 violations/69 primes).
- **Frame operator spectrum.** `C=Σ_x eis(x)eis(x)ᵀ`: **`λ_max/Tr(core)=½` exactly** (μ₃-core isotropic),
  **`λ_max/Tr(all)=¾` exactly** (60° rhombus, √3:1), gap **`¼ = the flap fraction`**. Core carries zero
  anisotropy; all anisotropy is the flap.
- **`C_T` = a tensor square.** Rounding-state law `(¾:⅛:⅛)⊗(¾:⅛:⅛)=36:6:1`; `C_T≈C_1⊗C_1`, per-coord
  chain `C_1` spectrum `{1,⅓,1/9}`; tensor spectrum `{1,⅓,⅓,1/9,…}`. Confirmed curve=random-field
  (0.5687≈0.5625) ⇒ pure lift self-convolution, group-law-independent.
- **Addition in the lift.** `σ₁=x_{P+Q}+x_{P−Q}=−B/A`, `σ₂=x_{P+Q}x_{P−Q}=C/A` — rational in `x_P,x_Q`
  alone, β-covariant (`σ₁→βσ₁`, `σ₂→β²σ₂`, 400/400). Directional-independence law:
  `|V|²≈|U₁|²+|U₂|²+|U_sum|²` (cross terms →0) for `V=eis(x_{P+Q})−(eis x_P+eis x_Q)`.

*(`glv_fundamental_domain_law_v1.py`, `glv_cm_orbit_invariant_v1.py`, `glv_pinned_satotate_v1.py`,
`int1_frame_operator_v1.py`, `ct_tensor_structure_v1.py`, `glv_s3_addition_covariant_v1.py`.)*

---

# PART V — THE LEAKAGE FRONTIER & ITS CLOSURE  `[PROVED / PROVED|KS / =ECDLP]`

- **Central result: leakage is COMPUTATIONAL, not information-theoretic.** The aligned readout
  `F̂(b)=conj(T(a₀,b))/|T(a₀,b)|` has no cancellation: `Corr(a₀)=(1/n)Σ_b|T(a₀,b)|` ≈ 0.37 (x-only) /
  **0.93 (joint x,y)** vs ~0.01 generic. Info about d is fully present & bounded-recoverable; only the
  DLP-cost of building `F̂` (needs `T` ⇒ all x_d) protects. Phase alignment — not Wiener norm — is the
  sole axis (χ₂ saturates `‖F‖_A≤√p‖F‖_∞` and provably does not leak).
- **★ Prime-order rigidity — the one theorem `[PROVED]`.** `E` prime order ⇒ no proper subgroup ⇒:
  the only coarse readout that **chains** (`f(P+Q)=φ(f(P),f(Q))`) is `d` itself; `σ⊥s_y` exact
  (fixed-point-free); amicable Hom=0; Semaev `C_t` smooth genus-1. Four costumes, one fact.
- **★★ The closure (capstone).**
  1. *Reduction (exact):* `Corr_F(a)=⟨F,χ_a⟩_d`; **concentration** `C(F)=max_a|Corr_F|/‖F‖₂=Ω(1)` ⟺ F
     correlates `Ω(‖F‖₂)` with a character `χ_{a₀}=e_n(a₀d)`. The `χ_a` **are the additive cocycles** ⇒
     **spectral-concentration ≡ chaining ≡ correlation-with-a-cocycle-character — ONE door.**
  2. *Bound `[PROVED|KS]`:* any `F=ψ∘f`, deg(f)≤D, has `|Corr_F(a)|=O_D(√p·polylog/n)=` floor (KS/Weil).
     Covers all bounded-degree readouts incl high-Wiener χ₂ (direct sum, not the vacuous Wiener bound)
     and `e_p(xy)`. Empirically the best cheap readout is `e_p(xy)`, `C/floor` FLAT ≈1.3 over p=211→6007,
     while the planted aligned control grows 6→27.
  3. *The escapee is the DLP:* the only `C=1` readout is `e_n(a₀d)` — not bounded-degree = the discrete
     log. For general poly-time readouts, "no concentration" **⟺ ECDLP hard** (Boneh–Shparlinski).
- **The door map** (each shut, specific reason): additive-subgroup (prime order) · MOV (254-bit) ·
  anomalous (`#E≠p`) · Weil-descent (prime field) · H² carry (coordinate null, control z=849) ·
  **spectral concentration (PROVED|KS for bounded-degree, =ECDLP for the rest).**
- **Closure theorem (single-coordinate, given KS).** `|Cov_d(F(x_d),g(d))|≤(max|T|/n)‖F‖_A‖g‖_A`;
  with KS ⇒ `O(p^{-1/2+o(1)})`, MI `O(p^{-1+o(1)})`. Extends from x-readouts to (x,y) readouts via Part V-2.
- **Character-sum bounds.** `Σ_b|T(a,b)|²=p(n−2)`; Parseval `Σ_a|Corr_F|²=‖F‖₂²`. **T_y/U bound
  `[PROVED|KS]`:** `max_a|U(a,b,c)|=O(√p·polylog)` uniform over (b,c) (bx+cy is pole-order-≤3). `Corr(a₀)=√(πn)/2`.

*(`phase_structure_T_v1.py`, `joint_set_cocycle_v1.py`, `carry_cocycle_v1.py`, `cheap_partial_shadow_v1.py`,
`spectral_concentration_hunt_v1.py`, `spectral_concentration_closure_v1.md`, `glv_closure_theorem_v2.md`,
`t_y_maxbound_v1.py`.)*

## The `xy` object — real structure  `[PROVED / VERIFIED]`
`xy=x·y` is **odd-in-d + μ₃-weight-1** — the symmetry type of the *odd half* x cannot see. The **odd/even
d-spectrum carry EXACTLY equal mass** (`avg|U(·,·,c≠0)|²/avg|U(·,·,0)|²=1.0004`; `avg_a|U|²=n` ∀(b,c)) —
the shadow is a full equal half. `xy` is the single-key **D-shadow** (`(X·Y)mod m↔D_terms`, KNOWN_FACTS),
and **`e_p(xy)` is provably the most T-aligned cheap readout** (beats χ₂/χ₃/χ₆/ε; C/floor bounded 1.3 by
Part V). The joint (x,y) aligned readout leaks 0.93. Real alignment — bounded by the closure to exactly
where every cheap readout must sit.

---

# PART VI — SEMAEV / INDEX-CALCULUS  `[PROVED / PROVED|KS]`
- `S₃` irreducible/ℚ; `Δ(t)=−86704128·(t³+7)⁴` ⇒ `C_t` smooth genus-1 for every t (prime order).
- **First-fall degree of `{S_{m+1}=0, g(x_i)=0}` is CURVE-INDEPENDENT `[PROVED, general m]`:** Semaev
  polys **isobaric** under `wt(x_i)=1,A=2,B=3` (S₃ wt4, S₄ wt12) ⇒ leading form free of A,B ⇒ first-fall
  = leading-form invariant [CITED BFS] ⇒ no CM/GLV elimination lever beyond `|Aut|≤6`.
- **S₄ leading form = the cusp `y²=x³` summation polynomial** (→ additive summation Σuᵢ=0 at infinity);
  every S₄ fibre singular exactly on the diagonal xᵢ=xⱼ (generic to symmetric polys).

*(`semaev_elimination_v1.py` — Sage.)*

---

# PART VII — SUBSTRATE (cross-domain scaffolding)  `[PROVED criticality + VERIFIED]`
secp at criticality (Weil `|π|=√p`); `|T|²`~Porter–Thomas (thermal, rigid, no scar); transfer spectrum
fully mixing beyond μ₆ (no metastable soft mode; `|λ₂|~1/√n`). The user's LRC→φ(n)→Berry–Keating→ζ
programme spans **two substrates, bridged**: chaotic-GUE (ζ zeros, secp) vs rigid-arithmetic (LRC φ(n)
totatives = hard-gap; Berry–Keating `{πk²}` = picket-fence). "One programme" = the bridge, not one substrate.
*(`masked_structure_findings_v18/v24.md`, `substrate_crossdomain_v1.py`.)*

---

# PART VIII — HOW IT ALL FITS
1. **Prime-order rigidity** ⇒ the only chaining readout is `d`.
2. **KS/Weil** ⇒ every bounded-degree cheap readout is spectrally flat (√p floor).
3. (1)+(2) ⇒ **the closure:** concentration = chaining = correlation-with-a-character; no cheap readout
   concentrates; the escapee is the DLP. Every classical door + the carry are shut.
4. All the real structure (lift laws, CM/L-function/formal-group, GLV/μ₆, 2-point law, frame/C_T, Semaev-
   isobaric, `xy` odd+μ₃ equal-mass, amicable) is genuine and `μ₆`/√p-bounded — it does not reduce d
   **because of** (1)+(2), a theorem, not a dismissal.
5. **Security = the DLP = cheap spectral concentration**, the sole residual not reducible to proved
   structure — precisely located, not an open haze.

---

# PART IX — SCRIPTS / REPRODUCTION
Foundational: `ecc_secp256k1.py`, `int1_frame_operator_v1.py` (build/eis/eps), `lift_sextant_rhombus_law_proof_v2.py`.
Lift laws: `lift_chi6_uniform_law_proof_v1.py`, `norm_band_law_proof_v1.py`, `glv_orbit_structure_proof_v1.py`,
`cap_law_proofs_v1.md`. CM/L-fn: `sextic_identities_verify.py`, `secp256k1_formal_group_finding.md`,
`cm_amicable_correspondence_v1.py`. Lift-geometry: `glv_fundamental_domain_law_v1.py`,
`glv_cm_orbit_invariant_v1.py`, `glv_pinned_satotate_v1.py`, `ct_tensor_structure_v1.py`,
`glv_s3_addition_covariant_v1.py`. Leakage/closure: `phase_structure_T_v1.py`, `xy_interference_U_v1.py`,
`t_y_maxbound_v1.py`, `cheap_partial_shadow_v1.py`, `joint_set_cocycle_v1.py`, `carry_cocycle_v1.py`,
`spectral_concentration_hunt_v1.py`, `glv_closure_theorem_v2.md`, `spectral_concentration_closure_v1.md`.
Semaev: `semaev_elimination_v1.py` (Sage). Transfer/substrate: `conservation_spectrum_v2.py`,
`substrate_crossdomain_v1.py`. Difference-set: `difference_set_xy_geometry_v1.py`, `bilinear_jointset_harness_v1.py`.
Datasets: §I. Discipline: exact int/Fraction signal path; every detector tested on BOTH real-82 and 36k
(known-d); every null needs a firing control + power/scaling number.

---

# APPENDIX A — EMPIRICAL NULLS (scoped facts, firing controls — NOT closures)
Each bounds a *magnitude* about *that object at that scale with a control that fired*; Part V explains
why cheap readouts must sit at the floor. Single-key `(X,Y)→n,k,D` ~1e-5 bits (controls fire); bilinear-
additive joint sum flat O(n) (planted rank-1 fires); H² carry not coordinate-leaked (control z=849);
difference-set μ₃/cubic/xy geometry generic (AP control fires 13–36×); no metastable soft mode in any x-
or y-readout (`|λ₂|~1/√n`, multi-shuffle z; σ·s_y & fine joint decay 1/√n); finer-m (mod≤64) difference
scan null (scalar control z=1050); phase-hunt beyond μ₆ null (9 CM/Frobenius candidates); GLV/CM ⊥ key-
coordinate on the 82; derr↔cap = a bit-length confound (dissolves at fixed bits P=0.34–0.89). λ₂ transfer
eigenvector ~50% μ₃-cov / λ₃ up to 85% (real, broadband, no closed form — OPEN, not closed).

# APPENDIX B — HEURISTICS & OPEN PANELS (invitations)
`[HEURISTIC]`: "genus-1 ⇒ no index-calc lever" (Diem 2011); aligned-leak critical exponent (~flat;
`1/√log p` retracted). **Open panels (invitations):** the two-point/joint-SET bilinear bound (2-variable
KS) at finer resolution; full-resolution σ₁,σ₂ boundedness (`N(r)` bits, not label-MI); is ε an arithmetic
object (a symbol/norm condition beyond core/flap)?; large-prime `K` rank-10 μ₃ split; the C_T inter-
coordinate coupling (λ₂≠λ₃, ~2–3%) — genuine or finite-orbit noise; the unconditional version of the
Part V closure (needs Weil–Deligne+KS reproved). Candidate cross-project seeds (secp↔RH/LRC): finite-field
zeta as an RH test-bench (`|π|=√p` exact ground truth); LRC ↔ survival core (n mod 3 sets the μ₆/μ₂ shadow).

# APPENDIX C — CITED INPUTS (verify before relying)
Kohel–Shparlinski / Lange–Shparlinski general-`f` character-sum bound; Weil–Deligne; Boneh–Shparlinski
(MSB hardcore); MOV/Tate embedding-degree; BFS first-fall/degree-of-regularity; Diem 2011.

---
*Full proofs & detail: `cap_law_proofs_v1.md`, `masked_structure_findings_v1–v32.md`, `glv_*` narratives,
and the four superseded handovers now in `archive_handovers/`. Nested memory index: `memory/btc_puzzle_INDEX.md`.*
