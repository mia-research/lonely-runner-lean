> **⛔ FROZEN — NOT CURRENT.** This file is a historical snapshot. The single current-state
> document is **`CLAIMS.md`**. Do not read status, grades, or open items from here; do not
> write a successor version of this file. (Frozen 2026-09-01.)

# secp256k1 — Master Positive-Findings & Structure Compendium (v2, 2026-07-17)

> ## ⚠ SCALE BANNER — READ BEFORE ANY CLAIM BELOW
> **Every empirical result in this document was measured at `p = 211 → 10⁵` (leakage/closure
> scaling at `p = 211 → 6007`; the `C_T` drill at `p = 100003 ≈ 2¹⁷`). Nothing here was measured at
> secp's `p ≈ 2²⁵⁶`** — a gap of **239 binary orders of magnitude**. A structure that only switches
> on near `2²⁵⁶` would not show in any test cited here, and no test here has *any* power against
> that hypothesis. *(H3 open frontier #5, verbatim: "Everything at **secp's actual p** — all
> scaling here is small-to-moderate p; a structure that only switches on near `2²⁵⁶` would not
> show.")* This caveat governs Parts II, IV, V, VII and Appendix A globally. It was dropped in
> v1; its restoration is the single most important change in v2.

**Supersedes v1** (`POSITIVE_FINDINGS_MASTER_v1.md`), which is retained for diff. v1 was a lossy
compile: it liquidated Handover 3's five live frontiers and five of its six retractions. See
`DEGRADATION_AUDIT_H3_TO_MASTER_v1.md`. **The live frontier list (§X) and the retraction ledger
(§XI) are restored verbatim and are load-bearing sections of this document, not appendices.**

**Compile rule (binding on all successors).** A handover or master may **not** delete a
predecessor's open item or retraction. It may only (a) carry it forward verbatim, or (b) mark it
`resolved-by <artifact>` / `bounded-by <artifact>` naming the script/proof. Losing an open item with
no artifact cited is a defect regardless of whether any claim is wrong. Grades may move **down**
freely; a grade moving **up** requires a named artifact in the same edit.

**Anomaly-Drill rule (binding on all §X work).** A frontier is investigated as an **Anomaly Drill**:
the output is the **mathematical characterization** of the object, never a verdict. Specifically —
1. **Report magnitudes; never convert a magnitude into a verdict.** A `√p` bound or a `1/√n` decay
   is a statement about *size*. It is not "no structure". Structure lives in the **symmetry type,
   eigenvector, and subspace** — a drill must say *where* the object lives, not only how big it is.
2. **Every bound carries its power.** "z=−0.2" is meaningless without "we would have detected an
   effect of size X". A bound with no power statement is not a result.
3. **Every bound carries its scope**: which orbit, generator, prime, estimator, and `n`. And the
   scale banner is total — no measurement at `p≈10⁵` constrains `p≈2²⁵⁶`.
4. **The control must fire.** A null is uninformative until a matched surrogate/planted control
   demonstrates the test could have seen the thing.
5. **A drill ends in one of three things:** a sharper law, a bounded magnitude with its power, or a
   named next probe. **Never in a closure.** Banned as drill conclusions: *safe, generic, benign,
   tautological, obstructed, at-the-floor-therefore-nothing, closed, shut.*
6. **Dissolution is a positive result.** When an anomaly dissolves, it dissolves *into a sharper
   law* — state the law and its new precision (see §X.6 / Part IV `C_T`), not "nothing there".

**Stance.** Mapping a fence and locating its gate — the DLP is *currently* hard, the object of
study. Positive exact structure leads. Out of scope: the PRNG / generation side (a curve question
only). Signal-path arithmetic exact (`int`/`Fraction`); float only as an analytic-size character-sum
magnitude or a monotone statistic vs a matched permutation null.

**Grades:** `[PROVED]` rigorous · `[PROVED|KS]` given the cited Kohel–Shparlinski/Weil bound ·
`[VERIFIED]` exact/numeric **at tested scale — see banner** · `[CITED]` literature ·
`[CITED|KS]` follows from a cited bound, not independently checked · `[HEURISTIC]` / `[EMPIRICAL]` ·
`[UNREPRODUCED]` stated in a source but not reproducible here.

**Verification status of v2.** Every decidable math claim was re-checked in
`_master_v2_math_verify.py` (27 checks) + `_glm_audit_v1.py`. Results: **25 pass, 1 was my test's
bug (now fixed and passing), 1 does not reproduce and is re-graded `[UNREPRODUCED]` below.**

---

# PART I — CONSTANTS & CODE-READY DEFINITIONS  `[VERIFIED — all re-checked exactly]`

```
p = 2^256 − 2^32 − 977                                              (field prime, p≡1 mod 6)  ✓prime
n = 0xFFFF...BAAEDCE6AF48A03BBFD25E8CD0364141                       (group order)             ✓prime
E : y^2 = x^3 + 7   (j=0, CM by Z[ω], ω=e^{2πi/3}, |Aut(E)|=6)
t = p+1−n = 432420386565659656852420866390673177327               (Frobenius trace)          ✓
π = a + bω,  a = 367917413016453100223835821029139468249,
             b = 303414439467246543595250775667605759171,  N(π)=p ✓, 2a−b=t ✓
4p = t^2 + 3f^2 ✓,  f = 3·79·349·2698097·1359580455984873519493666411   (tail prime, 91-bit ✓)
p−1 = 2·3·7·13441·C ✓ (C prime ✓) ;  n−1 = 2^6·3·149·631·...
π_n = π−1  (prime above n; N(π−1)=n ✓).  n_t = 2(p+1)−n ✓ = 3^2·13^2·3319·22639·C' (C' prime ✓)
Reduced ℤ[ω]-basis of L=(π_p):
 R1=(−303414439467246543595250775667605759171, 64502973549206556628585045361533709078)
 R2=( 64502973549206556628585045361533709078, 367917413016453100223835821029139468249)
```
*(Correction vs v1: the tail prime of `f` is **91-bit**, not 90-bit. Verified.)*

- **Curve/scalar.** `d ↔ [d]G=(x_d,y_d)` bijection `ℤ/n ↔ E(F_p)` (full order n). Imports:
  `ecc_secp256k1` (`P=p`, `N_ORDER=n`, `scalar_mul`); `int1_frame_operator_v1.build(p)→(eis,eps)`;
  `lift_sextant_rhombus_law_proof_v2.reduced_basis(p)→(R1,R2)`.
- **Characters.** `e_p(t)=exp(2πi t/p)`, `e_n(t)=exp(2πi t/n)`; `χ_k(a)=a^{(p-1)/k}`; `χ₂`=Legendre.
  Curve character `χ_a(P):=e_n(a·d(P))` — the DLP frequency.
- **Eisenstein lift.** `eis(x)` = rep of `x∈F_p≅ℤ[ω]/(π_p)` in the 60° rhombus
  `P={uR₁+vR₂:u,v∈[−½,½)}`. `DET=R₁[0]R₂[1]−R₁[1]R₂[0]`, `u=(z₀R₂[1]−z₁R₂[0])/DET`,
  `v=(z₁R₁[0]−z₀R₁[1])/DET`; norm `N(z)=u²−uv+v²`, `s=N(eis x)/p∈[0,¾]`. Flap `ε(x)∈{0,±}`.
- **GLV/CM.** `β=g^{(p-1)/3} mod p` (β≡ω² mod π_p), `λ∈ℤ/n`, `λ³=1`, `x_{λd}=β·x_d`; μ₃=⟨β⟩ on x;
  μ₆=Aut=⟨β,−1⟩; [−1] fixes x, negates y. `eis(βx)=ω·eis(x)` reduced.
- **Cap/flap.** `flap ⟺ |u−v|>½`. `σ(x)=sign(u−v)` on flap else 0. Sextant = 60°-sector of eis(x).
- **Twisted sums.** `T(a,b)=Σ_d e_p(b x_d)e_n(a d)`; `U(a,b,c)=Σ_d e_p(b x_d+c y_d)e_n(a d)`,
  `T=U(·,·,0)`. `Corr_F(a)=(1/n)Σ_d F(P_d)e_n(-a d)`. **`xy:=x·y`** — ODD in d, μ₃-weight 1.
  `s_y=+1 if y<p/2 else −1` (ODD).
- **Semaev.** `S₃(a,b,c)=(a−b)²c²−2((a+b)(ab)+2·7)c+((ab)²−28(a+b))`; `S_{m+1}` by resultants.
  **`[VERIFIED]` — this formula is CORRECT as written.** It is the specialization to `A=0,B=7` of
  `S₃=(x₁−x₂)²x₃²−2[(x₁+x₂)(x₁x₂+A)+2B]x₃+[(x₁x₂−A)²−4B(x₁+x₂)]`. `A=0` kills the `+A`/`−A` **inside**
  two other slots; the `2B` term is a **separate slot** and survives as `2·7`. Vanishes on
  **1406/1406** collinear secp triples; deleting the `2·7` gives **0/1406**. *(An external review
  in 2026-07 asserted `2·7` was a typo. It is not. Do not "fix" it — S₄ is a resultant of two S₃s,
  so the error would silently propagate into every Part VI claim.)*
- **Key coordinate.** `A=2^{bits−1}`, `band_offset=d−A`; `(n,k)`=`argmin_{n≤256}|n(d−A)−kA|`;
  `derr=|n(d−A)−kA|`; `D_terms`=greedy unit-fraction; curve-identity `D` in `[n]P=(n+k)Q+(n·D)G`,
  `r=nD−(2^{N−1}k mod n)`. Datasets: `solved_keys_augmented_v1.csv` (82),
  `constructed_keys_fullrange_v1.csv` (36k), `..._100k_exact.csv`.
- **Transfer operator.** label `l(d)`; `M[i,j]=#{d:l(d)=i,l(d+1)=j}/#{d:l(d)=i}`; `|λ₂|~1/√n`=thermal.
  Valid null = ABSOLUTE `|λ₂|` decay + multi-shuffle z (NOT shuffle-ratio on 2-state, NOT `np.roll`).

---

# PART II — THE EISENSTEIN LIFT LAWS  `[PROVED — continuum; VERIFIED at small p]`

**Scope note (new in v2).** The shape constants below are **exact statements about the continuum
rhombus geometry**. At finite `p` they hold up to a discretization error that vanishes as `p→∞`.
v1 wrote "exactly" without this distinction, which reads as a finite-`p` identity. It is not one —
**measured**: mean `s` deviates from `1/6` by `7.7e-3` at `p=211`, `1.2e-4` at `p=1009`, `4e-7` at
`p=10⁶`. For secp (`p≈2²⁵⁶`) the continuum value is the right one; but **every test we ran was at
small `p`, where these constants are not exact** (see banner).

- **Rhombus theorem (universal) `[VERIFIED, exact at every p tested]`.** Both reduced basis vectors
  have norm **exactly `p`** — this one **is** exact at finite `p` (re-verified independently for
  p=13…331, and secp). `P` is a 60° rhombus, edge `√p`, area `p√3/2`. `eis` bijects `F_p → ℤ[ω]∩P`.
- **One-parameter angle law `[PROVED — continuum]`.** Sextant histogram = function of
  `θ=arg(π_p) mod 60°`; opposite sectors equal; three pairs sum ½. Pinned pair `= 1/8` (`= √3/16`,
  θ-independent); free `p₀(θ)=(¾)|cos2θ|/(2cos2θ+1)`, and `3/8−p₀`. secp pinned `{0,3}`, θ=50.55°.
  **secp values, computed exactly** (`cos2θ = t²/2p − 1`, a rational — no rounding):
  ```
  cos2θ     = −0.192572688042775637582913548821578218236893969447106423010991
  p₀        =  0.234900268152131105489408666073932216267297499086645306612437
  3/8 − p₀  =  0.140099731847868894510591333926067783732702500913354693387563
  pinned    =  0.125                                    (sum over 6 sextants = 1.000000)
  ```
  *(Recorded because an external review circulated `p₀≈0.23480`, from a rounded `cosθ=0.6354`.
  That value is wrong in the 4th decimal; testing a dataset against it would fake a deviation.)*
- **Norm-band law `[PROVED — continuum]`.** `s=N(eis x)/p`: support `[0,¾]`, **mean `1/6` in the
  continuum limit** (NOT exact at finite `p` — see scope note + measurements above), density `2π/√3`
  on `[0,3/16]`, breakpoints `3/16, ¼, ¾`.
- **All nontrivial `χ_k` exactly uniform `[PROVED]`** (fibers `(p−1)/k` — exact at finite p); `Σζ₆^{χ₆}=0`.
- **GLV = lift × cube-root `[VERIFIED]`.** `φ(x,y)=(βx,y)`, β≡ω²; `χ₆(βx)=χ₆(x)+4`, `χ₃(βx)=χ₃(x)+1`,
  χ₂ fixed; orbit-sextant ~98% same parity.
- **Summation-poly [ω]-covariance `[VERIFIED — re-checked symbolically in v2]`.** `S₃(βx)=β·S₃`
  (weight 1) ✓; `S₄(βx)=S₄` (weight 0, invariant) ✓; `S₃` irreducible/ℚ(b) ✓; `deg_{x₁}S₄=4=2^{m−2}` ✓.
  `y`: `χ₂(y_{n−d})=−χ₂(y_d)`, `f(λd)=f(d)`.
- **Cap Law `[PROVED — continuum]`.** `ε(x)≠0 ⟺ |u−v|>½`; forced by hexagonal geometry (ω-matrix
  `M=[[0,−1],[1,−1]]`); core/flap densities ¾ : ⅛ : ⅛ (continuum area ratios); shape constants
  (½,¾,33,3/16,¼,1/6) are θ-independent lattice geometry.
- **σ μ₃-invariant `[PROVED]`** (`σ(βx)=σ(x)`) + `σ(−x)=−σ(x)` ⇒ σ = μ₂-isotypic part of μ₆.

*(`lift_sextant_rhombus_law_proof_v2.py`, `lift_chi6_uniform_law_proof_v1.py`, `norm_band_law_proof_v1.py`,
`glv_orbit_structure_proof_v1.py`, `cap_law_proofs_v1.md`; v2 re-checks in `_master_v2_math_verify.py`.)*

---

# PART III — CM / ENDOMORPHISM / L-FUNCTION / TWIST / AMICABILITY

- **`End(E)=ℤ[ω]`, maximal `[PROVED]`** (φ²+φ+1=0 ⇒ ℤ[ω]⊆End; h(−3)=1). **μ₆ acts FREELY** on
  `E\{O}`: `(n−1)/6` free orbits. **MOV embedding degree `ord_n(p)=(n−1)/6` `[VERIFIED — 254-bit]`** —
  sextic index 6=|μ₆| again. `ord_n(2)=(n−1)/64` ✓, `ord_p(t)=(p−1)/6` ✓. Not anomalous (`#E=n≠p`) ✓.
  Isogeny class all order n `[CITED — Tate]`.
- **Sextic identities `[VERIFIED]`.** `u=−1` is the unique unit with `N(π+u)=n`; `π_n=π−1` ✓;
  sextic classes `[7/π_p]₆=ζ₆⁵`, `[7/π_n]₆=ζ₆`; exact 4-D character `ε=ζ₆^{3−[28/π]₆}`. Frobenius
  angle `cosθ=t/(2√p)=0.6354`, θ=50.55°.
- **L-function & its RH `[CITED — Hasse/Weil, a theorem]`.** `L(T)=1−tT+pT²=(1−πT)(1−π̄T)`, `|π|=√p`
  ⇒ zeros on `Re(s)=½`. **Supersingular `a_ℓ=0 ⟺ ℓ≡2 mod 3` `[VERIFIED]` — for primes of GOOD
  reduction only (`ℓ ∤ 42`).** *(v2 correction: v1 stated this unrestricted. At `ℓ=7` (bad
  reduction, `7|B`) `a_7=0` while `7≡1 mod 3`, so the unrestricted claim is false as written.
  Verified on all 92 good-reduction primes < 500.)*
- **Formal-group logarithm (exact) `[VERIFIED]`.** `L(T)=Σ_{k≥0} 7^k·C(3k,k)/(6k+1)·T^{6k+1}` —
  **μ₆-sparse** (all exponents ≡1 mod 6 ✓, forced by Aut(E)); family `Σ b^k C(3k,k)/(6k+1)T^{6k+1}`
  for `y²=x³+b`. Formal group law `F(T₁,T₂)=T₁+T₂−7(3T₁T₂⁶+…)`, no linear cross-term, μ₆-sparse.
  **`L(T[d]P)=d·L(T P)`** linearizes `E₁(ℚ_p)` (the reduction kernel) — *not* `E(F_p)`; mapping
  `[d]G` into it = the DLP.
- **ASD / Honda bridge `[VERIFIED]`.** At split `ℓ=6k+1`: `7^k·C(3k,k)≡a_ℓ (mod ℓ)` — re-verified
  **58/58** split primes < 700 in v2.
- **Twist structure `[VERIFIED]`.** Six sextic twists (Frobenius `u·π_p`, u∈μ₆); **b=7 ↔ u=1+ω
  unique prime-order**; quad-twist `n_t=2(p+1)−n` ✓. **Frobenius sieve:** `ℓ|n_t ⟺` Frobenius
  eigenvalue `−1 mod ℓ`.
- **Amicability `[VERIFIED — arithmetic]` / `[OPEN — transfer]`.** `(p,n)` is an amicable pair:
  `#E(F_n)=p` exactly. The mechanism, written unambiguously:
  ```
  Frob@n := 1 − π      (norm-n element:  N(1−π) = 1 − t + p = n   ✓ verified exactly)
  (1 − π) − 1 = −π                         [subtraction, NOT an inverse]
  #E(F_n) = N(Frob@n − 1) = N(−π) = N(π) = p    ✓ verified exactly
  ```
  *(v2 correction: v1 rendered this `(1−π)−1=−π`, which invites reading `−1` as an exponent. An
  external review did read it that way and declared it "algebraically impossible". As an inverse it
  would be; as written it is the standard `#E = N(π−1)` identity. Spaces are load-bearing here.)*
  **Scope — RESTORED from H3.** What is ruled out is the **group-homomorphism** case only
  (`Hom=0`, coprime orders). **The non-homomorphic correspondence is UNANALYZED — see §X.3.**
  v1's "the coordinate map φ:E(F_p)→F_n **is the DLP** (transfers no advantage)" is a claim over
  **all** maps and is **withdrawn**: it re-asserts a wall H3 had explicitly retracted as a strawman
  (§XI.4). The lift obstruction that would protect the transfer is `[HEURISTIC]` (xedni), not proven.
  Amicable geometry `[VERIFIED]`: `P_p`,`P_n=(π−1)` overlap `1−4.1e−39`, `C_n⊆C_p`, slippage
  `R1_p−R1_n=(0,1)`, `R2_p−R2_n=(1,1)`.

*(`sextic_identities_verify.py`, `secp256k1_Lfunction_intersections.md`, `secp256k1_formal_group_finding.md`,
`secp256k1_arithmetic_v4.md`, `cm_twist_order_divisibility_*`, `cm_amicable_correspondence_v1.py`,
`amicable_spectral_fixedpoint_v1.py`.)*

---

# PART IV — THE LIFT-GEOMETRY PROGRAMME  `[PROVED continuum / VERIFIED at small p — see banner]`

- **The 2-point CM law (spine).** `eis(βX)=ζ·eis(X)+c`, `c∈{0,+R,−R}` exhaustively, densities
  ¾ : ⅛ : ⅛ (θ-indep, continuum); `area(P∩ωP)/area(P)=¾`. Pure rotation (¾) preserves norm/shifts
  sextant; the `±R` flap (¼) is the sole norm-change / sextant-parity flip.
- **The correction is a μ₃-ORBIT invariant.** One label `ε∈{0,+,−}` per orbit `{X,βX,β²X}`; over
  `F_p*/μ₃` labels are ¾:⅛:⅛; ε=0 ⟺ core, ε=± ⟺ flap; a geometric (Babai) class function, ⊥ χ₆.
- **Three bridges.** pinned ↔ angle-law (`⅛=√3/16` = CM-stable wedges = μ₃-core sextants);
  correction ↔ norm-band (flap-rate 0 for s<3/16, 1 for s>¼); **pinned pair ↔ Frobenius angle**
  (`{1,4}` if θ<30° else `{0,3}`; 0 violations / 69 primes).
- **Frame operator spectrum.** `C=Σ_x eis(x)eis(x)ᵀ`: `λ_max/Tr(core)=½` (μ₃-core isotropic),
  `λ_max/Tr(all)=¾` (60° rhombus, √3:1), gap `¼ = the flap fraction`. Core carries zero anisotropy;
  all anisotropy is the flap. *(Continuum ratios — same scope note as Part II.)*
- **`C_T` = a tensor square `[VERIFIED — precision stated, v2]`.** Rounding-state law
  `(¾:⅛:⅛)⊗(¾:⅛:⅛)=36:6:1`; per-coord chain `C_1` spectrum `{1,⅓,1/9}`; tensor spectrum
  `{1,⅓,⅓,1/9,…}` with a **doubly degenerate ⅓**. Curve=random-field (0.5687≈0.5625) ⇒ pure lift
  self-convolution, group-law-independent. **v2 sharpens `≈` to a measured precision**
  (`ANOMALY_DRILL_01`): at `p=100003`, `n=99666`, the degenerate-block trace `λ₂+λ₃ = 0.666742` vs
  `2/3` (**7.5e-5**), and `Tr(S|block) = +0.029 ≈ 0` for the coordinate swap `S` — the block splits
  into exactly one swap-EVEN and one swap-ODD channel, as the tensor law requires. Pooled G² test
  of the factorization: **p=0.40** (indistinguishable from an independent-coordinate surrogate).
  **The ~2–3% residual v1 called UNEXPLAINED is at the estimator floor — a coupling-free surrogate
  reproduces it (z=+1.6 / +0.1). Any coupling is <≈2% at n≈10⁵. This bounds a MAGNITUDE at
  `p≈2¹⁷`; it says nothing at `2²⁵⁶` and does not close §X.6.**
- **Addition in the lift.** `σ₁=x_{P+Q}+x_{P−Q}=−B/A`, `σ₂=x_{P+Q}x_{P−Q}=C/A` — rational in
  `x_P,x_Q` alone, β-covariant (`σ₁→βσ₁`, `σ₂→β²σ₂`, 400/400). Directional-independence law:
  `|V|²≈|U₁|²+|U₂|²+|U_sum|²` (cross terms →0) for `V=eis(x_{P+Q})−(eis x_P+eis x_Q)` — **measured
  for random pairs at `k≤16` only** (§X.7).

*(`glv_fundamental_domain_law_v1.py`, `glv_cm_orbit_invariant_v1.py`, `glv_pinned_satotate_v1.py`,
`int1_frame_operator_v1.py`, `ct_tensor_structure_v1.py`, `glv_s3_addition_covariant_v1.py`.)*

---

# PART V — THE LEAKAGE FRONTIER AND WHAT IS BOUNDED

*(v2: v1 titled this "…& ITS CLOSURE" and closed with a "door map (each shut)". That frame entered
at Handover 4 and appears in no earlier handover. It is removed — not because any bound is wrong,
but because the frame asserted a completeness the bounds do not have. What each bound covers is
stated; what it does not cover is §X.)*

- **Central result: leakage is COMPUTATIONAL, not information-theoretic `[VERIFIED]`.** The aligned
  readout `F̂(b)=conj(T(a₀,b))/|T(a₀,b)|` has no cancellation: `Corr(a₀)=(1/n)Σ_b|T(a₀,b)|` ≈ 0.37
  (x-only) / **0.93 (joint x,y)** vs ~0.01 generic. Info about d is fully present; only the DLP-cost
  of building `F̂` (needs `T` ⇒ all x_d) protects. Phase alignment — not Wiener norm — is the sole
  axis (χ₂ saturates `‖F‖_A≤√p‖F‖_∞` and does not leak).
- **★ Prime-order rigidity — the one theorem `[PROVED]`.** `E` prime order ⇒ no proper subgroup ⇒
  the only coarse readout that **chains** (`f(P+Q)=φ(f(P),f(Q))`) is `d` itself; `σ⊥s_y` exact
  (fixed-point-free); amicable **Hom**=0 (homomorphic case only — §X.3); Semaev `C_t` smooth genus-1
  (mechanism now explicit — Part VI).
- **The bound (was "the closure (capstone)").**
  1. *Reduction (exact) `[PROVED]`:* `Corr_F(a)=⟨F,χ_a⟩_d`; **concentration**
     `C(F)=max_a|Corr_F|/‖F‖₂=Ω(1)` ⟺ F correlates `Ω(‖F‖₂)` with a character `χ_{a₀}=e_n(a₀d)`.
     The `χ_a` **are the additive cocycles** ⇒ spectral-concentration ≡ chaining ≡
     correlation-with-a-cocycle-character.
  2. *Bound `[PROVED|KS]` — restated from the source text, v2:* for **ψ a nontrivial ADDITIVE
     character of `F_p`** and **f nonconstant**, `deg(f)≤D`, `F=ψ∘f` has
     **`|Corr_F(a)| ≤ 2D·√p/n`** — an **explicit** constant, **no polylog**.
     *(Kohel–Shparlinski ANTS-IV 2000, Thm 1 + eq (3), verified against the source: `|S(ω,ψ,f)| ≤
     2deg(f)q^{1/2}`; PDF `kohel_shparlinski_ants4_2000.pdf`, SHA-256 `645d9022e029…5d8d2a`.)*
     Covers `e_p(xy)` (`deg=5`). **⚠ Does NOT cover `χ₂`:** KS's `Ψ` is explicitly the group of
     **additive** characters `ψ(z)=e_p(Tr(αz))`, and its proof runs through an **Artin–Schreier**
     extension. `χ₂`=Legendre is **multiplicative** and is not of that form. v1's "covers all
     bounded-degree readouts **incl. high-Wiener χ₂**" overreached this citation — χ₂'s flatness
     rests on the separate `‖F‖_A≤√p‖F‖_∞` argument above, not on KS. *(This does not assert χ₂
     leaks; it says a different argument carries it. See §XI.10.)*
     Empirically the best cheap readout is `e_p(xy)`, `C/floor` FLAT ≈1.3 over **p=211→6007**,
     while the planted aligned control grows 6→27.
  3. *What escapes the bound:* the only `C=1` readout we know is `e_n(a₀d)` — not bounded-degree;
     it is the discrete log. **`[GAP]` For general poly-time (non-bounded-degree) readouts we have
     NO reduction.** *(v1 asserted "no concentration **⟺ ECDLP hard** (Boneh–Shparlinski)". The
     `⟸` direction is trivial: ECDLP easy ⇒ `e_n(a₀d)` is cheap and concentrates. The `⟹` direction
     — concentration ⇒ extraction — is a real reduction that Boneh–Shparlinski does not prove at
     that generality (B–S is an MSB/hardcore-bit result for Diffie–Hellman). The biconditional is
     **withdrawn**; the gap is named. This line was inherited verbatim from H4 §94–96, not
     introduced by the v1 compile.)*
- **Doors with a specific known reason `[VERIFIED / CITED]`** *(a list of what has been checked —
  NOT a claim of completeness; v1's "each shut" framing is withdrawn)*: additive-subgroup (prime
  order) · MOV (254-bit, verified) · anomalous (`#E≠p`, verified) · Weil-descent (prime field) ·
  H² carry (coordinate null, control z=849).
- **Covariance bound (single-coordinate, given KS) `[PROVED|KS]`.**
  `|Cov_d(F(x_d),g(d))|≤(max|T|/n)‖F‖_A‖g‖_A`; with KS ⇒ `O(p^{-1/2+o(1)})`, MI `O(p^{-1+o(1)})`.
  Extends from x-readouts to (x,y) readouts via V-2.
- **Character-sum bounds.** `Σ_b|T(a,b)|²=p(n−2)`; Parseval `Σ_a|Corr_F|²=‖F‖₂²`.
  **★ `T_y/U` bound — `[PROVED|KS]`, VERIFIED AGAINST THE SOURCE (v2).**
  ```
  max_{a, (b,c)≠(0,0)} |U(a,b,c)|  ≤  4√p + 1        — uniform in (b,c), NO polylog
  ```
  *Artifact: `kohel_shparlinski_ants4_2000.pdf` (SHA-256 `645d9022e029…5d8d2a`), Thm 1 + eq (3);
  read and re-derived, not taken on report.* The mechanism, since v1 asserted it without one:
  - KS define `S(ω,ψ,f) = Σ_{P∈E(F_q), f(P)≠∞} ω(P)ψ(f(P))` with **`ω ∈ Ω = Hom(E(F_q),ℂ*)`**,
    `ω(mP+ℓQ) = e_M(am)e_L(bℓ)`. **`E`/secp has PRIME order** ⇒ `M=n, L=1` ⇒ **`ω([d]G) = e_n(a·d)`
    IS our discrete-log twist.** So KS covers the **mixed** sum, over the **FULL** group — not a
    partial sum, so there is no `O(n)` degradation at `N=n`. With `Tr=id` on a prime field,
    `ψ=e_p` and `f=bx+cy`: `S(ω,ψ,f) = U(a,b,c)` **exactly**.
  - Quantifier: eq (3) is `|S(ω,ψ,f)| ≤ 2deg(f)·q^{1/2}` — **universally quantified with an
    explicit constant**. There is no implied constant that could fail to be uniform. This is the
    strong form ("C depends only on deg f"), not the pointwise form ("for each f there is C(f)").
  - `deg(bx+cy) = 3` for `c≠0` (pole divisor `3·(O)`, single prime divisor, `m₁=n₁+1=4` since
    `gcd(3,p)=1` ✓) ⇒ `|U| ≤ 4√p`; `deg(bx) = 2` for `c=0` ⇒ `|U| ≤ 3√p`. Our `U` sums `d∈ℤ/n`
    including `d=0` where `P=O` is a pole (KS excludes it) ⇒ `+1`.
  - **No exceptional `(b,c)` can escape**, for any `p`. H3's frontier asked whether one could
    (§X.2); the answer is no, and it has been in the literature since 2000.
  **⚠ Attribution corrected:** this is **Kohel–Shparlinski, NOT "KS / Lange–Shparlinski".** L–S
  (JMC 2007) Lemma 2.4 bounds the **untwisted** sum `Σ_P χ(f(P))` — no `ω(P)` factor — and does
  **not** cover the mixed sum. Every "KS/L–S" pairing on this bound was wrong. See §XI.11.
  `Corr(a₀)=√(πn)/2`.

*(`phase_structure_T_v1.py`, `joint_set_cocycle_v1.py`, `carry_cocycle_v1.py`, `cheap_partial_shadow_v1.py`,
`spectral_concentration_hunt_v1.py`, `spectral_concentration_closure_v1.md`, `glv_closure_theorem_v2.md`,
`t_y_maxbound_v1.py`.)*

## The `xy` object — real structure  `[VERIFIED]`
`xy=x·y` is **odd-in-d + μ₃-weight-1** — the symmetry type of the *odd half* x cannot see. The
**odd/even d-spectrum carry equal mass** (`avg|U(·,·,c≠0)|²/avg|U(·,·,0)|²=1.0004`; `avg_a|U|²=n`
∀(b,c)) — the shadow is a full equal half. `xy` is the single-key **D-shadow**
(`(X·Y)mod m↔D_terms`, KNOWN_FACTS), and `e_p(xy)` is the most T-aligned cheap readout tested
(beats χ₂/χ₃/χ₆/ε; C/floor ≈1.3 at p=211→6007). The joint (x,y) aligned readout leaks **0.93**.

**This is an OPEN lead, not a bounded one.** v1 wrote: "Real alignment — bounded by the closure to
exactly where every cheap readout must sit." That answers a different question. The bound is over
**bounded-degree** readouts; H3's question was whether a **cheap** readout captures a **fraction**
of the 0.93 alignment. Restored as §X.1 — H3 called it the **highest-value lead**.

---

# PART VI — SEMAEV / INDEX-CALCULUS

- **`S₃` irreducible/ℚ `[VERIFIED]`.**
- **`C_t` smooth genus-1 for every `t ∈ F_p` `[VERIFIED — mechanism now explicit]`.** v2 re-derived
  this independently:
  ```
  disc_{x₂} S₃(x₁,x₂,t) = 16·(t³+7)·(x₁³+7)          [verified symbolically]
  ⇒ C_t is a double cover of the x₁-line branched at x₁³=−7 (3 pts) + ∞  ⇒  genus 1
  ⇒ C_t singular  ⟺  t³+7 = 0
  n odd prime ⇒ E(F_p) has no 2-torsion ⇒ x³+7 has no root in F_p ⇒ −7 is not a cube mod p ✓
  ⇒ t³+7 ≠ 0 for every t ∈ F_p  ⇒  C_t smooth for every t.
  ```
  **The "(prime order)" parenthetical in v1 was load-bearing and unexplained: prime order is exactly
  what makes this true.** It is Part V's prime-order rigidity appearing again — a real unification,
  now with its mechanism stated instead of asserted.
- **`Δ(t) = −86704128·(t³+7)⁴` — RE-GRADED `[UNREPRODUCED]`.** The **roots** reproduce (`t³=−7`,
  which is all the smoothness claim needs). The **constant and exponent do not**: an independent
  derivation via the Weierstrass model `y²=x³+7c³`, `c=16(t³+7)`, gives
  `Δ = −355140108288·(t³+7)⁶`. Both are `−432·B'²`-shaped and differ by model normalization
  (`86704128 = 2¹⁶·3³·7² = −432·49·2¹²`). The literal v1 formula is not reproducible here and is
  not relied on by any downstream claim. Flagged for a Sage re-derivation.
- **First-fall degree — RE-GRADED `[HEURISTIC + CITED]` (was `[PROVED, general m]` in v1).**
  What is **verified symbolically in v2**: Semaev polys are isobaric under `wt(xᵢ)=1, wt(A)=2,
  wt(B)=3` — `S₃` single weight **4** ✓, `S₄` single weight **12** ✓ ⇒ the leading form is free of
  `A,B`. What is **not proved**: that "leading form free of A,B" ⇒ "first-fall degree is
  curve-independent". **That `⇒` is the load-bearing step and it is not a theorem** — first-fall
  degree depends on the whole ideal, not the leading form alone; the step leans on
  `[CITED BFS]` first-fall/degree-of-regularity. **H3 stated the Gröbner structure is UNTOUCHED
  (§X.4).** Going "untouched" → `[PROVED, general m]` in one handover with no new artifact is
  precisely the move the compile rule forbids. The conclusion "no CM/GLV elimination lever beyond
  `|Aut|≤6`" inherits this grade.
- **S₄ leading form = the cusp `y²=x³` summation polynomial `[VERIFIED]`** (→ additive summation
  `Σuᵢ=0` at infinity); every S₄ fibre singular exactly on the diagonal `xᵢ=xⱼ` (generic to
  symmetric polys).

*(`semaev_elimination_v1.py` — Sage; v2 re-checks in `_master_v2_math_verify.py`.)*

---

# PART VII — SUBSTRATE (cross-domain scaffolding)  `[VERIFIED at small p — see banner]`
secp at criticality (Weil `|π|=√p`); `|T|²`~Porter–Thomas (thermal, rigid, no scar); transfer
spectrum fully mixing beyond μ₆ (no metastable soft mode; `|λ₂|~1/√n`). The LRC→φ(n)→Berry–Keating→ζ
programme spans **two substrates, bridged**: chaotic-GUE (ζ zeros, secp) vs rigid-arithmetic
(LRC φ(n) totatives = hard-gap; Berry–Keating `{πk²}` = picket-fence). "One programme" = the bridge,
not one substrate.
*(`masked_structure_findings_v18/v24.md`, `substrate_crossdomain_v1.py`.)*

---

# PART VIII — HOW IT ALL FITS  (what is established, and what it does not establish)

1. **Prime-order rigidity `[PROVED]`** ⇒ the only chaining readout is `d`. This is the spine: it
   also forces `C_t` smooth (Part VI) and `σ⊥s_y`, and it bounds the amicable transfer **only in
   the homomorphic case**.
2. **KS/Weil `[PROVED|KS]`** ⇒ every **bounded-degree** cheap readout is spectrally flat (√p floor),
   at the scales tested.
3. (1)+(2) ⇒ concentration ≡ chaining ≡ correlation-with-a-character, **for bounded-degree
   readouts**. For general poly-time readouts there is **no reduction in hand** (`[GAP]`, V-3).
4. The mapped structure (lift laws, CM/L-function/formal-group, GLV/μ₆, 2-point law, frame/C_T,
   Semaev-isobaric, `xy` odd+μ₃ equal-mass, amicable) is real and `μ₆`/√p-bounded **where it has
   been measured — at p=211→6007** (banner).
5. **What this does NOT say.** It does not say the doors are exhaustively mapped; it does not say
   the DLP is the sole residual; it does not say ECDLP is hard. Seven live frontiers follow. v1's
   "Security = the DLP … precisely located, not an open haze" is **withdrawn**: an open-questions
   list whose only items are a citation, a scale caveat, and the object of study is a closure
   verdict written in the grammar of an open list.

---

# PART IX — SCRIPTS / REPRODUCTION
Foundational: `ecc_secp256k1.py`, `int1_frame_operator_v1.py`, `lift_sextant_rhombus_law_proof_v2.py`.
Lift laws: `lift_chi6_uniform_law_proof_v1.py`, `norm_band_law_proof_v1.py`,
`glv_orbit_structure_proof_v1.py`, `cap_law_proofs_v1.md`. CM/L-fn: `sextic_identities_verify.py`,
`secp256k1_formal_group_finding.md`, `cm_amicable_correspondence_v1.py`. Lift-geometry:
`glv_fundamental_domain_law_v1.py`, `glv_cm_orbit_invariant_v1.py`, `glv_pinned_satotate_v1.py`,
`ct_tensor_structure_v1.py`, `glv_s3_addition_covariant_v1.py`. Leakage: `phase_structure_T_v1.py`,
`xy_interference_U_v1.py`, `t_y_maxbound_v1.py`, `cheap_partial_shadow_v1.py`,
`joint_set_cocycle_v1.py`, `carry_cocycle_v1.py`, `spectral_concentration_hunt_v1.py`,
`glv_closure_theorem_v2.md`, `spectral_concentration_closure_v1.md`. Semaev:
`semaev_elimination_v1.py` (Sage). Transfer/substrate: `conservation_spectrum_v2.py`,
`substrate_crossdomain_v1.py`. Difference-set: `difference_set_xy_geometry_v1.py`,
`bilinear_jointset_harness_v1.py`.
**v2 verification:** `_master_v2_math_verify.py` (27 checks), `_glm_audit_v1.py` (S₃/amicable/sextant).
Discipline: exact int/Fraction signal path; every detector on BOTH real-82 and 36k; every null needs
a firing control + power/scaling number.

---

# PART X — LIVE FRONTIERS  (restored from H3 verbatim; **this is not an appendix**)

**H3's items 1–5 are reproduced word-for-word. Handover 4 deleted 1, 3 and 4 with no artifact; the
v1 master deleted 5. None was resolved.** Items 6–7 are carried from H2 §9 as still-live.

1. **A *cheap partial* version of the joint (x,y) shadow.** *(H3 verbatim)* "The full aligned
   readout needs `T` (=DLP), but the y-sign bit is free and the joint shadow is real (0.93). Can a
   cheap readout capture a *fraction* of that alignment? This is the one object found this arc
   where 'compute a bit of the shadow cheaply' is not immediately circular. **Highest-value lead.**"
   → *Status: OPEN. Not addressed by the Part V bound (which covers bounded-degree readouts, a
   different question). Concrete next step: compute `C(s_y)` and `C(e_p(xy mod p))` on the 36k, both
   cheap and free, against a matched permutation null.*
2. **The odd-half / T_y max-bound.** *(H3 verbatim)* "an exceptional non-cancelling `(b,c)` would be
   real structure. No literature bound is known to cover the y-twisted sum." And, from H3's
   HEURISTIC section: "only the *average* `|U|²=n` is shown; that `max_a|U(a,b,c)|` is
   `O(√p·polylog)` **uniformly over all (b,c)** is not verified. If some exceptional `(b,c)` fails
   to cancel, that is structure the average hides. **This is a live un-bounded corner.**"
   → ***Status: RESOLVED-BY `kohel_shparlinski_ants4_2000.pdf` (KS ANTS-IV 2000, Thm 1 + eq (3)),
   2026-07-17.*** The source was read and the derivation re-done independently. **No exceptional
   `(b,c)` can fail to cancel: `max_{a,(b,c)≠(0,0)} |U(a,b,c)| ≤ 4√p + 1`, uniform, explicit
   constant, no polylog** — better than the `O(√p·polylog)` we claimed. KS's `ω∈Hom(E(F_p),ℂ*)`
   factor **is** the `e_n(ad)` twist on a prime-order curve, so the theorem covers exactly our
   mixed sum, over the full group. H3 wrote "**No literature bound is known to cover the y-twisted
   sum**" — a statement about our knowledge, not the literature. The bound has existed since 2000.
   **This is the FOURTH time an obstacle dissolved on reading the source (CLAUDE.md §5).**
   Weil alone indeed cannot bound this sum (`e_n(ad)` is not algebraic in the coordinates) — KS is
   the right machinery, and it is now verified rather than cited. See §XI.11 for the attribution
   correction this surfaced.*
3. **Non-homomorphic amicable map.** *(H3 verbatim)* "only the homomorphic case is ruled out; the
   CM relation `π_n=π_p−1` as a *non-group-hom* correspondence is unanalyzed."
   → *Status: OPEN. v1 asserted the map "transfers no advantage" — withdrawn (§XI.4 retracted this
   wall as a strawman). The protecting lift obstruction is `[HEURISTIC]` (xedni), not proven.*
4. **`S₄⁺` elimination / first-fall-degree.** *(H3 verbatim)* "(real index-calculus bottleneck) —
   heavier than anything this arc; `S₃`/`S₄`/`S₅` yield-counting is generic, but the Gröbner
   structure is untouched."
   → *Status: OPEN. v1's `[PROVED, general m]` is re-graded `[HEURISTIC + CITED]` (Part VI). The
   isobaric fact is verified; the implication to first-fall degree is not.*
5. **Everything at secp's actual p.** *(H3 verbatim)* "all scaling here is small-to-moderate p; a
   structure that only switches on near `2²⁵⁶` would not show."
   → *Status: OPEN and global. Promoted to the document banner.*
6. **The `C_T` inter-coordinate coupling.** `λ₂=0.339 ≠ λ₃=0.328` (~2–3%) against the tensor-square
   prediction `C_T=C_1⊗C_1`, which forces `λ₂=λ₃`. Arithmetic coupling, or finite-orbit noise?
   → *Status: **OPEN — `bounded-by ANOMALY_DRILL_01`** (`ANOMALY_DRILL_01_CT_SPLIT_v1.md`,
   `_anomaly_drill_ct_split_v2.py`). **Not resolved.** At `p=100003`, `n=99666`, full orbit: a
   matched independent-coordinate surrogate (zero coupling by construction) reproduces the effect —
   `max|C_T−C_1⊗C_2|` z=+1.59, `δ=|λ₂−λ₃|` z=+0.13; pooled G² = 16.80 on 16 df, **p=0.40**
   (surrogate 18.1±6.9, z=−0.19); swap-even/odd channels z=−0.55/+0.34. Both real and surrogate
   scale as `n^(−0.59)`. **Any coupling is <≈2% at n≈10⁵ for this orbit/generator/prime and these
   estimators.** Positive by-product: the tensor law is CONFIRMED more tightly than v1 claimed —
   block trace `λ₂+λ₃ = 0.666742` vs `2/3` (**7.5e-5**), and `Tr(S|block) = +0.029 ≈ 0` where
   `S:(c₁,c₂)→(c₂,c₁)`, i.e. the degenerate block splits into exactly one swap-EVEN and one
   swap-ODD channel, as the tensor structure requires (opposite signs 6/6 across primes). **Scale
   caveat is total: `p=100003 ≈ 2¹⁷`; this drill has NO power against a coupling that switches on
   near `2²⁵⁶` (§X.5).** Next: aim `‖D_odd‖_F` (1-dim targeted, `n^(−1/2)` power) at `n~10⁶–10⁷`;
   vary generator/prime/`b` before believing the bound.*
7. **The two-point / joint-SET bilinear bound (2-variable KS).** The Part V bound is a **single sum
   over one `d`**. It does not cover joint/multi-key readouts of the *set* `{x([dᵢ]G)}` — the exact
   complement of "only a joint-SET property survives" — nor the two-point addition panel (`V`).
   *(H2 §8, preserved.)* → *Next step: the directional-independence law was measured for **random**
   pairs at `k≤16`; test **structured** pairs (`Q=[2]P`, `[3]P`, μ₆-sextant-aligned) at `k=32,64`.*

**Also live (from H2 §9, lower stakes):** full-resolution `σ₁,σ₂` boundedness (`N(r)` bits, not
label-MI); is `ε` an arithmetic object (a symbol/norm condition beyond core/flap)?; large-prime `K`
rank-10 μ₃ split; an unconditional version of the Part V bound (needs Weil–Deligne + KS reproved —
this is a `[GAP]`, not merely "cited"). Cross-project seeds (secp↔RH/LRC): finite-field zeta as an
RH test-bench (`|π|=√p` exact ground truth); LRC ↔ survival core (n mod 3 sets the μ₆/μ₂ shadow).

---

# PART XI — RETRACTION LEDGER  (restored verbatim from H3; **do not re-claim these**)

*(H3 recorded six retractions "so they are not re-claimed". v1 carried one. Item 4 was re-claimed
by v1 Part III — the exact failure this ledger exists to prevent. It is restored in full and is
binding.)*

1. χ₂ "doubling transport law" → the **textbook duplication formula** (x(2P) is a rational function
   of x alone for any short-Weierstrass curve). CITED, not a finding.
2. Test-A cubic-moment "null" → **zero statistical power** (N=82 needs f=1.0 to detect anything).
3. G "tested the blind corner" → tested a **proxy** (`d mod k`, an already-known-null hardcore bit).
4. v11 amicable "wall" → **strawman**; only the group-*homomorphism* case was ruled out (coprime
   orders), which is not even the mechanism any transfer uses.
   **⚠ RE-CLAIMED BY v1** ("the coordinate map φ:E(F_p)→F_n is the DLP (transfers no advantage)") —
   withdrawn again in v2. See §X.3.
5. v14 "the ‖F‖_A gap is the only analytic door" → **wrong**; Wiener norm is a red herring (v15).
6. v17 "6–7σ soft shadow" → a **null-mismatch artifact** (a shuffle null that destroyed the
   μ₆-invariance the readout has by definition). Against the correct μ₆-invariant null, z≈0.
7. *(new, v2)* aligned-leak scaling `~1/√log p` → **retracted**; data drift 0.85→0.73 over too small
   a p-range, never confirmed. (H3 had this `[PARTIAL]`; v1 correctly retracted it — the one place
   v1 was stricter than its source.)
8. *(new, v2)* `[PROVED, general m]` first-fall curve-independence → **withdrawn** to
   `[HEURISTIC + CITED]`; the isobaric fact is verified, the implication is not (Part VI).
9. *(new, v2)* "no concentration ⟺ ECDLP hard" → **withdrawn**; `⟸` trivial, `⟹` has no reduction
   in hand (Part V-3).
10. *(new, v2, from the KS source check)* "the KS bound **covers χ₂**" → **withdrawn**. KS's `Ψ` is
    the group of **additive** characters `ψ(z)=e_p(Tr(αz))`; the proof is via an **Artin–Schreier**
    extension. `χ₂`=Legendre is **multiplicative** and is not in `Ψ`. A multiplicative analogue
    would need a Kummer argument — a different theorem, which we do not cite. **Do not re-claim
    that KS bounds χ₂.** (χ₂'s flatness is carried by the separate `‖F‖_A` argument; that is
    untouched by this.)
11. *(new, v2, from the KS source check)* "**Kohel–Shparlinski / Lange–Shparlinski** general-`f`
    bound" as the citation for the mixed/twisted sum → **withdrawn**. **L–S does not cover the
    mixed sum**: its Lemma 2.4 (JMC 2007, `lange_shparlinski_jmc_2007.pdf`) bounds the *untwisted*
    `Σ_P χ(f(P))`, with no `ω(P)` factor. **KS alone carries this.** Do not re-pair them. The
    incorrect pairing was in `t_y_maxbound_v1.py:11-15` and at four places in v1.

---

# APPENDIX A — EMPIRICAL NULLS (scoped facts with firing controls — NOT closures)

> **Critical caveat — RESTORED from H3 verbatim:** "every one of these used a *misaligned* readout,
> so each is a scoped fact about that readout at that scale, **provably consistent with a hidden
> aligned leak**."
>
> *(v1 replaced this sentence with "Part V explains why cheap readouts must sit at the floor" — a
> closure statement, inside the appendix titled "NOT closures". The Part V bound covers
> bounded-degree readouts; it does not explain away a hidden aligned leak, which is the exact thing
> H3 said these nulls are consistent with.)*

Each bounds a *magnitude* about *that object at that scale with a control that fired* — **at
p=211→6007** (banner). Single-key `(X,Y)→n,k,D` ~1e-5 bits (controls fire); bilinear-additive joint
sum flat O(n) (planted rank-1 fires); H² carry not coordinate-leaked (control z=849); difference-set
μ₃/cubic/xy geometry generic (AP control fires 13–36×); no metastable soft mode in any x- or
y-readout (`|λ₂|~1/√n`, multi-shuffle z; σ·s_y & fine joint decay 1/√n); finer-m (mod≤64) difference
scan null (scalar control z=1050); phase-hunt beyond μ₆ null (9 CM/Frobenius candidates — the only
*known* computable phase structure is the μ₆ symmetry group); GLV/CM ⊥ key-coordinate on the 82;
derr↔cap = a bit-length confound (dissolves at fixed bits P=0.34–0.89). λ₂ transfer eigenvector
~50% μ₃-cov / λ₃ up to 85% (real, broadband, no closed form — **OPEN, not closed**).

Also scoped (H3): hybrid sum `χ_k`×additive ≈2√p; scalar-mult `ψ(d)`; cubic-moment / S3 tensor;
bilinear difference-set (powered to 1.4%); joint (x,y) *magnitude* distribution (CM=non-CM);
3-point group law / collinearity; index-calculus relation yield (β-invariant lever 1.5×, bounded)
and S₄/S₅ decomposition (β-lever → 1.0); easy-target predictability (no lever).

# APPENDIX B — HEURISTICS
`[HEURISTIC]` "genus-1 ⇒ no index-calc lever" (Diem 2011) — the standard prime-field heuristic; not
a theorem. `[HEURISTIC]` the canonical-**lift** obstruction (xedni) protecting the amicable transfer
— heuristic, not proven (H3; dropped by v1, restored here — it is what §X.3 turns on).

# APPENDIX C — CITED INPUTS (verify before relying)
- **✅ Kohel–Shparlinski**, *On Exponential Sums and Group Generators for Elliptic Curves over
  Finite Fields*, ANTS-IV 2000, LNCS 1838, 395–404. **VERIFIED 2026-07-17** against the source —
  on disk as `kohel_shparlinski_ants4_2000.pdf`, SHA-256
  `645d9022e029055271ae60387518b440075fad282886d8baa9df35f5b55d8d2a`.
  Thm 1: `|S(ω,ψ,f)| ≤ Σ mᵢdeg(𝔓ᵢ)q^{1/2}`, `mᵢ ≤ nᵢ+1` with equality iff `(nᵢ,q)=1`;
  eq (3): `|S(ω,ψ,f)| ≤ 2deg(f)q^{1/2}`, and `(1+deg f)q^{1/2}` for single-prime-divisor polar
  support. `S(ω,ψ,f)=Σ_{P, f(P)≠∞} ω(P)ψ(f(P))`, `ω∈Hom(E(F_q),ℂ*)`, `ψ` **additive**, `f`
  **nonconstant**. Carries Part V-2 **and** the `T_y` bound (§X.2, resolved).
  **Scope, from the text: additive ψ only — NOT χ₂ (see §XI.10).**
- **⚠ Lange–Shparlinski**, *Distribution of some sequences of points on elliptic curves*, JMC 1
  (2007) 1–11 — on disk as `lange_shparlinski_jmc_2007.pdf`, SHA-256 `f29c524a9670…c6edec`.
  Lemma 2.4 bounds the **UNTWISTED** sum only. **NOT load-bearing for anything we claim; do not
  cite it for the mixed sum (§XI.11).** Useful for the degree convention (`deg x=2, deg y=3`).
- *(not obtained: Lange–Shparlinski, Canad. J. Math. 57 (2005) — Cambridge renders formulas as
  images. **Not needed**: KS settles the uniformity question alone.)*
- Weil–Deligne (needed for an unconditional Part V — a `[GAP]`, not merely "cited").
- Boneh–Shparlinski (LSB/MSB hardcore) — **does not support the withdrawn `⟺` of V-3.**
- Xedni-calculus lift obstruction (Silverman 1998; Jacobson–Koblitz–Silverman–Stein–Teske 2000).
- MOV/Tate embedding-degree (embedding degree itself independently verified in v2).
- BFS first-fall / degree-of-regularity — **load-bearing for the re-graded Part VI implication.**
- Diem 2011.

---
*Full proofs & detail: `cap_law_proofs_v1.md`, `masked_structure_findings_v1–v32.md`, `glv_*`
narratives, and the handovers in `archive_handovers/`. Degradation trace v1←H4←H3:
`DEGRADATION_AUDIT_H3_TO_MASTER_v1.md`. External-review adjudication: `GLM_AUDIT_RESPONSE_v1.md`.
Nested memory index: `memory/btc_puzzle_INDEX.md`.*
