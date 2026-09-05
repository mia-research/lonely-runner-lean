> **⛔ FROZEN — NOT CURRENT.** This file is a historical snapshot. The single current-state
> document is **`CLAIMS.md`**. Do not read status, grades, or open items from here; do not
> write a successor version of this file. (Frozen 2026-09-01.)

# secp256k1 — Master Positive-Findings & Structure Map (v3, 2026-07-19)

> ## ⚠ SCALE BANNER — READ BEFORE ANY CLAIM BELOW
> **Every empirical result here was measured at small-to-moderate `p` (`p = 13 → 10⁵`; the
> class-number thread at `p < 2500`; the `C_T` drill at `p = 100003 ≈ 2¹⁷`). Nothing here was
> measured at secp's `p ≈ 2²⁵⁶`** — a gap of ~239 binary orders of magnitude. A structure that only
> switches on near `2²⁵⁶` would not show in any test cited here, and no test here has any power
> against that hypothesis. This caveat is total and governs every Part below.

> ## ⚠ LANGUAGE RULES (binding on this document and all successors, new in v3)
> This document **maps structural boundaries; it does not assess cryptographic security.** The words
> **`secure`, `closure`, `proven hard`, `unbreakable` are forbidden.** Every conclusion states
> (a) exactly what was measured, (b) the bound it achieved with its power and scope, and (c) that
> unmeasured / higher-degree / other-basis structures remain **outside the scope of the statement.**
> **"Bounded by KS" is not "ECDLP is hard"** — never equate them.
> **No dismissal by declaration.** A measurement reported as `flat` or `generic` is *a statement
> about one statistic in one basis*, never a verdict that structure is absent. Restate it as: "flat
> in basis/statistic B at scale S; interference in another basis or at higher degree is UNTESTED."
> In this problem `flat`/`generic` most often means *the right basis to see the interference has not
> been found yet.*

**Supersedes v2** (`POSITIVE_FINDINGS_MASTER_v2.md`, 2026-07-17), retained for diff. v2 is itself the
non-lossy restoration after `DEGRADATION_AUDIT_H3_TO_MASTER_v1.md`. Predecessor handovers in
`archive_handovers/`.

**Compile rule (binding on all successors).** A successor may **not** delete a predecessor's open
item or retraction. It may only (a) carry it forward verbatim, or (b) mark it `resolved-by <artifact>`
/ `bounded-by <artifact>` naming the script/proof. Losing an open item with no artifact cited is a
defect regardless of whether any claim is wrong. Grades move **down** freely; a grade moving **up**
requires a named artifact in the same edit. *(v3 was compiled against v2 with the `compile-diff`
agent; the loss report is `RESULT` note at end.)*

**Anomaly-Drill rule (binding on all frontier work).** Output = the mathematical **characterization**
of the object (symmetry type / eigenvector / subspace), never a verdict. Report magnitudes, never
convert a magnitude to a verdict; every bound carries its **power** and its **scope** (orbit,
generator, prime, estimator, `n`); the control must fire; a drill ends in a sharper law, a bounded
magnitude with its power, or a named next probe — **never in a "door shut".** Dissolution is a
positive result: an anomaly dissolves *into a sharper law* — state the law and its precision.

**Grades:** `[PROVED]` rigorous · `[PROVED|KS]` given the cited Kohel–Shparlinski/Weil bound ·
`[VERIFIED]` exact/numeric **at tested scale — see banner** · `[CITED]` literature ·
`[EMPIRICAL]` measured, not proved · `[HEURISTIC]` · `[OPEN]` · `[GAP]` no reduction in hand ·
`[UNREPRODUCED]` stated in a source, not reproducible here.

**Stance.** Mapping a structure and locating where the discrete-log lives inside it. The DLP is the
*object of study*, currently the residual. Positive exact structure leads. Out of scope: the PRNG /
generation side (a curve question only). Signal-path arithmetic is exact (`int`/`Fraction`); float
appears only as an analytic-size character-sum magnitude or a monotone statistic ranked against a
matched permutation null.

---

# PART I — CONSTANTS & CODE-READY DEFINITIONS  `[VERIFIED — exact]`

```
p = 2^256 − 2^32 − 977                                        (field prime, p≡1 mod 6)  ✓prime
n = 0xFFFF...BAAEDCE6AF48A03BBFD25E8CD0364141                 (group order)             ✓prime
E : y^2 = x^3 + 7   (j=0, CM by ℤ[ω], ω=e^{2πi/3}, |Aut(E)|=6)
t = p+1−n = 432420386565659656852420866390673177327          (Frobenius trace)          ✓
π = a + bω,  a = 367917413016453100223835821029139468249,
             b = 303414439467246543595250775667605759171,  N(π)=p ✓, 2a−b=t ✓
4p = t^2 + 3f^2 ✓,  f = 3·79·349·2698097·1359580455984873519493666411  (tail prime, 91-bit ✓)
Reduced ℤ[ω]-basis of L=(π_p):
 R1=(−303414439467246543595250775667605759171, 64502973549206556628585045361533709078)
 R2=( 64502973549206556628585045361533709078, 367917413016453100223835821029139468249)
```

- **Curve/scalar.** `d ↔ [d]G=(x_d,y_d)` bijection `ℤ/n ↔ E(F_p)` (full order n). Imports:
  `ecc_secp256k1` (`P=p`,`N_ORDER=n`,`scalar_mul`); `int1_frame_operator_v1.build(p)→(eis,eps)`;
  `lift_sextant_rhombus_law_proof_v2.reduced_basis(p)→(R1,R2)`;
  `_sigma_chi2_scan_v1.{chi2_table,build,sigma_fn}` (the σ,χ2,eis machinery used in Part VIII).
- **Characters.** `e_p(t)=exp(2πi t/p)`, `e_n(t)=exp(2πi t/n)`; `χ_k(a)=a^{(p-1)/k}`;
  `χ₂`=Legendre. Curve character `χ_a(P):=e_n(a·d(P))` — the DLP frequency.
- **Eisenstein lift.** `eis(x)` = representative of `x∈F_p≅ℤ[ω]/(π_p)` in the 60° rhombus
  `P={uR₁+vR₂:u,v∈[−½,½)}`. `DET=R₁[0]R₂[1]−R₁[1]R₂[0]`; `u=(z₀R₂[1]−z₁R₂[0])/DET`,
  `v=(z₁R₁[0]−z₀R₁[1])/DET` for `z=eis(x)`; norm `N(z)=u²−uv+v²`, `s=N(eis x)/p∈[0,¾]`.
- **GLV/CM.** `β=g^{(p-1)/3} mod p` (β≡ω² mod π_p), `λ∈ℤ/n`, `λ³=1`, `x_{λd}=β·x_d`; μ₃=⟨β⟩ on x;
  μ₆=Aut=⟨β,−1⟩; [−1] fixes x, negates y. `eis(βx)=ω·eis(x)` reduced.
- **Cap/flap (σ).** `flap ⟺ |u−v|>½`. **`σ(x)=sign(u−v)` on the flap, else 0** (orientation fixed
  by 100%-agreement with `eps`; `sigma_fn` tries `s=u−v` and `s=u+v` and keeps the one matching eps
  on every x). σ is μ₃-invariant (`σ(βx)=σ(x)`) and μ₂-odd (`σ(−x)=−σ(x)`) ⇒ σ = μ₂-isotypic part of μ₆.
- **Twisted sums.** `T(a,b)=Σ_d e_p(b x_d)e_n(a d)`; `U(a,b,c)=Σ_d e_p(b x_d+c y_d)e_n(a d)`,
  `T=U(·,·,0)`. `Corr_F(a)=(1/n)Σ_d F(P_d)e_n(-a d)`. `xy:=x·y` — ODD in d, μ₃-weight 1.
- **Class-number thread objects (Part VIII).** `FLD(p)=Σ_{x∈F_p} σ(x)χ₂(x)`;
  `T+ = {x : σ(x)=+1}` (positive flap triangle); `S+ = Σ_{x∈T+}χ₂(x)`;
  `D = Σ_{a=1}^{(p−1)/2}χ₂(a)`; `F4 = Σ_{p/4<a<p/2}χ₂(a)`; `h(−p)` = class number of ℚ(√−p)
  (by reduced-form count, verified against h(−163)=1). `t(X)=p·(u−v)` the flap coordinate,
  `M ≡ t(1) mod p` its slope; `T1 = Σ_X χ₂(X)·t(X)`.
- **Semaev.** `S₃(a,b,c)=(a−b)²c²−2((a+b)(ab)+2·7)c+((ab)²−28(a+b))`. **`[VERIFIED]` — the `2·7`
  term is CORRECT** (the `2B` slot of the general `S₃`, B=7; survives A=0). Vanishes on **1406/1406**
  collinear secp triples; deleting `2·7` gives 0/1406. Do not "fix" it.
- **Key coordinate.** `A=2^{bits−1}`, `(n,k)=argmin_{n≤256}|n(d−A)−kA|`, `derr=|n(d−A)−kA|`;
  curve-identity `r=nD−(2^{N−1}k mod n)`. Datasets: `solved_keys_augmented_v1.csv` (82),
  `constructed_keys_fullrange_v1.csv` (36k), `..._100k_exact.csv`.
- **Transfer operator.** label `l(d)`; `M[i,j]=#{d:l(d)=i,l(d+1)=j}/#{d:l(d)=i}`; `|λ₂|~1/√n`=thermal.
  **Valid null = ABSOLUTE `|λ₂|` decay + multi-shuffle z (NOT shuffle-ratio on a 2-state, NOT `np.roll`).**

---

# PART II — THE EISENSTEIN LIFT LAWS  `[PROVED — continuum; VERIFIED at small p — banner]`

Shape constants are **exact statements about the continuum rhombus geometry**; at finite `p` they
hold up to a discretization error →0 as `p→∞` (measured: mean `s` deviates from `1/6` by 7.7e-3 at
p=211, 1.2e-4 at p=1009, 4e-7 at p=10⁶).

- **Rhombus theorem `[VERIFIED, exact at every p]`.** Both reduced basis vectors have norm **exactly
  `p`** (re-verified p=13…331 and secp). `P` a 60° rhombus, edge `√p`; `eis` bijects `F_p→ℤ[ω]∩P`.
- **Angle law `[PROVED — continuum]`.** Sextant histogram = function of `θ=arg(π_p) mod 60°`; pinned
  pair `=1/8` (θ-indep); free `p₀(θ)=(¾)|cos2θ|/(2cos2θ+1)`. secp exact (`cos2θ=t²/2p−1`, rational):
  `p₀=0.2349002681…`, `3/8−p₀=0.1400997318…`, pinned `0.125`, θ=50.55°.
- **Norm-band law `[PROVED — continuum]`.** `s∈[0,¾]`, mean `1/6` (continuum), density `2π/√3` on
  `[0,3/16]`, breakpoints `3/16,¼,¾`.
- **All nontrivial `χ_k` uniform `[PROVED]`** (fibers `(p−1)/k`, exact at finite p); `Σζ₆^{χ₆}=0`.
- **GLV = lift × cube-root `[VERIFIED]`.** `χ₆(βx)=χ₆(x)+4`, `χ₃(βx)=χ₃(x)+1`, χ₂ fixed.
- **Summation-poly [ω]-covariance `[VERIFIED]`.** `S₃(βx)=β·S₃` (wt 1); `S₄(βx)=S₄` (wt 0).
- **Cap Law `[PROVED — continuum]`.** `ε(x)≠0 ⟺ |u−v|>½`; core/flap densities ¾:⅛:⅛ (continuum area).

*(`lift_sextant_rhombus_law_proof_v2.py`, `norm_band_law_proof_v1.py`, `glv_orbit_structure_proof_v1.py`,
`cap_law_proofs_v1.md`; re-checks `_master_v2_math_verify.py`.)*

---

# PART III — CM / ENDOMORPHISM / L-FUNCTION / TWIST / AMICABILITY

- **`End(E)=ℤ[ω]`, maximal `[PROVED]`.** μ₆ acts **FREELY** on `E\{O}`: `(n−1)/6` free orbits. MOV
  embedding degree `ord_n(p)=(n−1)/6` `[VERIFIED — 254-bit]`. `ord_n(2)=(n−1)/64` ✓,
  `ord_p(t)=(p−1)/6` ✓. Not anomalous (`#E=n≠p`) ✓. Isogeny class all order n `[CITED — Tate]`.
- **Sextic identities `[VERIFIED]`.** `π_n=π−1` ✓; `[7/π_p]₆=ζ₆⁵`, `[7/π_n]₆=ζ₆`; ε=ζ₆^{3−[28/π]₆}.
- **L-function & its RH `[CITED — Hasse/Weil]`.** `L(T)=1−tT+pT²`, `|π|=√p` ⇒ zeros on `Re(s)=½`.
  Supersingular `a_ℓ=0 ⟺ ℓ≡2 mod 3` **for good reduction only (`ℓ∤42`)** `[VERIFIED]`.
- **Formal-group log `[VERIFIED]`.** `L(T)=Σ 7^k C(3k,k)/(6k+1) T^{6k+1}` — μ₆-sparse (exponents
  ≡1 mod 6). `L(T[d]P)=d·L(T P)` linearizes the reduction kernel `E₁(ℚ_p)`, **not** `E(F_p)`;
  mapping `[d]G` into it = the DLP.
- **ASD/Honda `[VERIFIED]`.** `7^k C(3k,k)≡a_ℓ (mod ℓ)` at split ℓ — 58/58 primes < 700.
- **Twist `[VERIFIED]`.** Six sextic twists; `b=7↔u=1+ω` unique prime-order; `n_t=2(p+1)−n`.
- **Amicability `[VERIFIED — arithmetic] / [OPEN — transfer]`.** `#E(F_n)=p` exactly, via
  `#E(F_n)=N((1−π)−1)=N(−π)=N(π)=p` (subtraction, not an inverse; spaces load-bearing). **Scope:
  only the group-homomorphism case is ruled out (Hom=0, coprime orders). The non-homomorphic
  correspondence is UNANALYZED — §X.3.** The protecting lift obstruction is `[HEURISTIC]` (xedni).
  Amicable geometry `[VERIFIED]`: `P_n=(π−1)` overlaps `P_p` by `1−4.1e−39`, `C_n⊆C_p`, slippage
  `R1_p−R1_n=(0,1)`, `R2_p−R2_n=(1,1)`.

*(`sextic_identities_verify.py`, `secp256k1_formal_group_finding.md`, `cm_amicable_correspondence_v1.py`.)*

---

# PART IV — THE LIFT-GEOMETRY PROGRAMME  `[PROVED continuum / VERIFIED small p — banner]`

- **2-point CM law (spine).** `eis(βX)=ζ·eis(X)+c`, `c∈{0,+R,−R}`, densities ¾:⅛:⅛ (θ-indep,
  continuum). Pure rotation (¾) preserves norm; the `±R` flap (¼) is the sole norm-change / parity flip.
- **The correction is a μ₃-orbit invariant** `ε∈{0,+,−}` per orbit `{X,βX,β²X}`; ⊥ χ₆.
- **Three bridges `[VERIFIED]`.** pinned↔angle-law; correction↔norm-band; **pinned pair↔Frobenius
  angle** (`{1,4}` if θ<30° else `{0,3}`; 0 violations / 69 primes).
- **Frame operator `C=Σ_x eis(x)eis(x)ᵀ`.** `λ_max/Tr(all)=¾`; gap `¼ = flap fraction` (continuum).
- **`C_T` = a tensor square `[VERIFIED — precision stated]`.** `(¾:⅛:⅛)⊗(¾:⅛:⅛)`; tensor spectrum
  with a doubly-degenerate `⅓`. `ANOMALY_DRILL_01` (p=100003): block trace `λ₂+λ₃=0.666742` vs `2/3`
  (7.5e-5); the block splits into one swap-EVEN + one swap-ODD channel as the tensor law requires.
  **The ~2–3% `λ₂≠λ₃` residual: a zero-coupling surrogate reproduces it (z=+1.6/+0.1); pooled G²
  p=0.40.** *(Language: this bounds a MAGNITUDE — any inter-coordinate coupling is `<≈2%` **in the
  Frobenius-norm estimator, at p≈2¹⁷, this orbit/generator**. It is NOT "no coupling": a coupling
  visible only in another statistic, another basis, or near `2²⁵⁶` is untested. §X.6.)*
- **Addition in the lift.** `σ₁=x_{P+Q}+x_{P−Q}=−B/A`, `σ₂=x_{P+Q}x_{P−Q}=C/A` — rational in
  `x_P,x_Q`, β-covariant (400/400). Directional law `|V|²≈|U₁|²+|U₂|²+|U_sum|²` — **measured for
  random pairs at `k≤16` only** (§X.7).

*(`glv_fundamental_domain_law_v1.py`, `glv_cm_orbit_invariant_v1.py`, `int1_frame_operator_v1.py`,
`ct_tensor_structure_v1.py`, `_anomaly_drill_ct_split_v2.py`, `glv_s3_addition_covariant_v1.py`.)*

---

# PART V — THE LEAKAGE FRONTIER AND WHAT IS BOUNDED

- **Leakage is COMPUTATIONAL, not information-theoretic `[VERIFIED]`.** The aligned readout
  `F̂(b)=conj(T(a₀,b))/|T(a₀,b)|` has no cancellation: `Corr(a₀)≈0.37` (x-only) / **0.93 (joint x,y)**.
  Information about d is fully present; only the DLP-cost of building `F̂` (needs `T` ⇒ all `x_d`)
  bars a cheap reader. *(This is a statement about the aligned readout's cost, not about ECDLP.)*
- **★ Prime-order rigidity `[PROVED]`.** `E` prime order ⇒ the only coarse readout that **chains**
  (`f(P+Q)=φ(f(P),f(Q))`) is `d`; `σ⊥s_y` exact; amicable Hom=0 (homomorphic case only, §X.3);
  Semaev `C_t` smooth genus-1 (Part VI).
- **The bounded region.**
  1. *Reduction (exact) `[PROVED]`:* `Corr_F(a)=⟨F,χ_a⟩_d`; concentration
     `C(F)=max_a|Corr_F|/‖F‖₂=Ω(1)` ⟺ F correlates `Ω(‖F‖₂)` with `χ_{a₀}=e_n(a₀d)`.
  2. *Bound `[PROVED|KS]`:* for **ψ a nontrivial ADDITIVE character** and `f` nonconstant, `deg(f)≤D`,
     `F=ψ∘f` has **`|Corr_F(a)| ≤ 2D√p/n`** — explicit constant, **no polylog** (Kohel–Shparlinski
     ANTS-IV 2000, Thm 1 + eq (3), SHA-256 `645d9022e029…5d8d2a`). Covers `e_p(xy)` (`deg=5`).
     **⚠ Does NOT cover `χ₂`** (KS's Ψ is additive, proof via Artin–Schreier; χ₂ is multiplicative —
     §XI.10). Empirically the best cheap readout `e_p(xy)` has `C/floor ≈1.3` **in the aligned-phase
     statistic** over p=211→6007, while the planted aligned control grows 6→27.
  3. *What is outside the bound:* the only `C=1` readout known is `e_n(a₀d)` = the discrete log,
     not bounded-degree. **`[GAP]` For general poly-time (non-bounded-degree) readouts there is NO
     reduction.** *"No concentration ⟺ ECDLP hard" is WITHDRAWN (§XI.9): `⟸` trivial, `⟹` unproved.*
- **`T_y/U` bound `[PROVED|KS]` — verified against the source.**
  `max_{a,(b,c)≠(0,0)} |U(a,b,c)| ≤ 4√p + 1` — **uniform in (b,c), no polylog.** KS's
  `ω∈Hom(E(F_p),ℂ*)` is `e_n(a·d)` on a prime-order curve, so KS covers the mixed sum over the full
  group; `deg(bx+cy)=3` ⇒ `4√p`, `+1` for the `d=0` pole. **No exceptional `(b,c)` escapes** (§X.2
  resolved). *(This bounds `|U|`; it is not a statement that ECDLP is hard.)*
- **Doors with a specific checked reason** *(a list of what has been checked — NOT a claim of
  completeness)*: additive-subgroup (prime order) · MOV (254-bit) · anomalous (`#E≠p`) ·
  Weil-descent (prime field) · H² carry (control z=849).
- **Covariance bound (single-coordinate, given KS) `[PROVED|KS]`.**
  `|Cov_d(F(x_d),g(d))| ≤ (max|T|/n)‖F‖_A‖g‖_A`; with KS ⇒ `O(p^{−1/2+o(1)})`, MI `O(p^{−1+o(1)})`.
  Extends from x-readouts to (x,y) readouts via the `U` bound. *(A magnitude bound on one-coordinate
  covariance/MI at the tested scale — not a statement about ECDLP.)*
- **Character-sum identities `[PROVED]`.** `Σ_b|T(a,b)|² = p(n−2)`; Parseval `Σ_a|Corr_F|² = ‖F‖₂²`;
  for the aligned readout `Corr(a₀) = √(πn)/2`.

## The `xy` / joint-(x,y) shadow — real structure `[VERIFIED]`, and an OPEN lead
`xy=x·y` is **odd-in-d + μ₃-weight-1** — the symmetry type of the odd half x cannot see. Odd/even
d-spectra carry **equal mass** (`avg|U|²=n` ∀(b,c)). The joint aligned readout reaches **0.93**.
**This is §X.1, the highest-value lead — see Part VIII for what this session measured about it, and
what remains outside scope.**

*(`phase_structure_T_v1.py`, `xy_interference_U_v1.py`, `t_y_maxbound_v1.py`, `cheap_partial_shadow_v1.py`.)*

---

# PART VI — SEMAEV / INDEX-CALCULUS

- **`S₃` irreducible/ℚ `[VERIFIED]`.**
- **`C_t` smooth genus-1 for every `t∈F_p` `[VERIFIED — mechanism explicit]`.**
  `disc_{x₂}S₃ = 16(t³+7)(x₁³+7)` ⇒ double cover branched at `x₁³=−7`+∞ ⇒ genus 1; `n` odd prime ⇒
  no 2-torsion ⇒ `−7` not a cube mod p ⇒ `t³+7≠0` ∀t ⇒ smooth. *(Prime-order rigidity again.)*
- **`Δ(t)=−86704128(t³+7)⁴` — `[UNREPRODUCED]`.** Roots reproduce (`t³=−7`); constant/exponent do
  not (Weierstrass `y²=x³+7c³` gives `−355140108288(t³+7)⁶`). Not relied on downstream.
- **First-fall degree — `[HEURISTIC + CITED]` (was `[PROVED,general m]`, re-graded §XI.8).**
  Verified: Semaev polys isobaric (`S₃` wt 4, `S₄` wt 12) ⇒ leading form free of A,B. **Not proved:**
  that this ⇒ first-fall degree is curve-independent (leans on `[CITED BFS]`). §X.4.
- **S₄ leading form = the cusp `y²=x³` summation polynomial `[VERIFIED]`** (→ additive `Σuᵢ=0` at
  infinity); every S₄ fibre singular exactly on the diagonal `xᵢ=xⱼ` (generic to symmetric polys).

*(`semaev_elimination_v1.py` — Sage.)*

---

# PART VII — SUBSTRATE  `[VERIFIED at small p — banner]`
secp at criticality (`|π|=√p`); `|T|²`~Porter–Thomas (thermal, no scar); transfer spectrum mixing
beyond μ₆ (no metastable soft mode; `|λ₂|~1/√n`). The `LRC→φ(n)→Berry–Keating→ζ` programme spans
**two substrates, bridged**: chaotic-GUE (ζ zeros, secp) vs rigid-arithmetic (LRC φ(n) totatives =
hard-gap; Berry–Keating `{πk²}` = picket-fence). "One programme" = the bridge, not one substrate.
*(A rigid/thermal magnitude statement — not a structure-absence claim.)*

---

# PART VIII — THE σ×χ₂ CONSERVATION PROGRAMME  (new in v3, 2026-07-19)

This session started from the mantra "hunt exact conservations, follow each to the symmetry that
enforces it; telling structure lives *outside* the symmetry," applied to the μ₆=Aut(E) action.
All results below are exact-integer; parameters and definitions in Part I are sufficient to rebuild
each `.py`. Model curves are the enumerable `y²=x³+7` over small `F_p`, `p≡1 mod 6`.

## VIII.1 — The joint-(x,y) 0.93 shadow: reproduced and decomposed
*(`joint_shadow_decompose_v1.py`, `RESULT_joint_shadow_decompose_v2.md`)*
- **Reproduced `[VERIFIED]`.** The v16 headline is `rho_inf = |Corr|/‖F‖_∞` (true point-space
  sup-norm): joint **0.93–0.96**, x-only **0.29–0.36**, stable p∈{163,349,433,577}. Control: a
  planted perfect character reads `rho=1.0000` (pins the normalization).
- **Even/odd exact constraint `[PROVED]`.** `U(−a,b,c)=U(a,b,−c)`: x-only readouts are even-in-d
  (`x_{−d}=x_d`), so they see only the **even half** of the d-spectrum; the odd half needs y
  (`y_{−d}=−y_d`). Cross-orthogonality `⟨F_even,c_odd⟩=0` to 1e-15. **This is real, d-specific
  structure and it survives every control below.** The even-subspace ceiling is `‖c_even‖=1/√2`.
- **What the magnitude control measured, stated without dismissal.** A char-vs-random control (same
  phase-only reconstruction applied to the leaking character and to a random function of d) gives the
  **same scalar fidelity** (joint 0.999 vs 0.999; x-only 0.66 vs 0.67). **So the scalar reconstruction
  MAGNITUDE does not, in this statistic, separate the character from a random target** — the number
  0.93 is the coordinate geometry's phase-only reconstruction quality in the tested (scalar-fidelity)
  basis. **This is NOT "the shadow is generic/nothing."** Per the language rule: a flat scalar
  magnitude is consistent with structure in a basis not yet examined. **UNTESTED and explicitly
  outside scope:** whether the **frequency-support pattern** (which (b,c) carry the alignment, and
  their μ₃/GLV grading) separates the character from random; higher-degree joint readouts; larger p.

## VIII.2 — μ₆-isotype decomposition (exact conservations)
*(`joint_shadow_mu3_v1.py`, `RESULT_joint_shadow_mu3_v1.md`)*
- **Exact identities `[VERIFIED, error 0]`:** `x_{λd}=βx_d`, `y_{λd}=y_d`, `x_{−d}=x_d`,
  `y_{−d}=−y_d` (β paired to λ from data).
- **Character equipartition `[VERIFIED]`.** `e_n(a₀d)` energy per μ₆-isotype = exactly `1/6` in five
  isotypes; the trivial isotype carries `1/6 − (5/6)/(n−1)` — and that deficit is *exactly* the
  excluded point `d=0 = O`, the unique μ₆-fixed point. The one departure from equipartition is the
  fixed point, in the trivial isotype, →0 as p→∞. Cross-isotype orthogonality ≤1.6e-15;
  weight-1=weight-2 exactly (complex conjugation ω↔ω²).
- **The aligned readout is FORCED μ₆-symmetric `[VERIFIED]`.** Because it is built from `U`, which is
  μ₆-equivariant (`U(a,b,c)=U(λa,βb,c)`), its alignment is flat across CM weights (w0≈w1≈w2). By the
  standing principle a μ₆-equivariant readout is constant on the orbit `{±d,±λd,±λ²d}` and cannot
  separate d — and it does not. **Outside-the-symmetry, i.e. non-equivariant, readouts are the
  untested complement**, addressed next.

## VIII.3 — Cheap non-U isotype-pure readouts (the outside complement)
*(`joint_shadow_cheap_isotype_v1.py`, `RESULT_cheap_isotype_concentration_v1.md`; pre-registered by
the `experiment-designer` agent.)*
- Readouts (DLP-free, each in one μ₆-isotype, on β-non-cube primes `p≢1 mod9` so χ₃ is weight-1):
  `χ₃(x)` (1,+), `χ₃(x)²` (2,+), `Legendre(x)` (0,+), `sign(y)` (0,−), `χ₃(x)·sign(y)` (1,−),
  `χ₃(x)²·sign(y)` (2,−). Statistic: orbit-peak `R_orb` + effective-support `N_eff`. Null:
  orbit-value permutation (preserves isotype purity + value multiset; destroys d-alignment; the
  dilation `d→cd` leaves R_orb invariant and is explicitly excluded). Controls fired: identities 0,
  purity ≤1e-15, planted φ=1 → R_orb=1.
- **Result `[EMPIRICAL, scoped]`.** All 6 readouts × 9 curves (p=211→6397) **at the matched null**.
  **Bound with power and scope:** no single-orbit d-character concentration above fraction
  **φ ≈ 0.1–0.5** (the power floor, smaller at larger n), on these curves, for these
  μ₆-isotype-pure readouts. The χ₃ weight-1/2 rows showed a sub-threshold tilt at small n
  (combined p≈0.08) that **washed out at larger n** (pR 0.31–0.55) — resolved, not a signal.
  **Explicitly outside scope:** concentration below φ; larger n; the diffuse N_eff channel at large
  n; and **non-μ₆-covariant cheap readouts** (raw coordinate bits — x mod 2, high bits of x), which
  live outside this decomposition and this test says nothing about. *(Side observation, not a leak:
  `Legendre(x)` is over-dispersed — flatter than the null, pR=1.0000 — the low discrepancy of the
  quadratic character sum; the anti-concentration direction.)*

## VIII.4 — An exact conservation followed to its object: `FLD = ±6·h(−p)`
*(`_reflection_symmetry_hunt_v1.py`, `_fld_involution_hunt_v1.py`, `_fld_classnumber_check_v1.py`,
`_fld_interval_v1.py`, `_fld_L1_fold_v1.py`; `RESULT_reflection_conservation_hunt_v1.md`,
`RESULT_fld_classnumber_v2.md`.)*

The flap-sign × quadratic-character pairing `FLD(p)=Σ_x σ(x)χ₂(x)` is an **exact conservation** that
no within-F_p symmetry enforces, and following it lands on the class number of ℚ(√−p).

- **The law `[EMPIRICAL, exact match]`.** `FLD(p) = 0` unless `p ≡ 19 mod 24`; `|FLD| = 6·h(−p)`
  there. Verified: 34/34 nonzero (h up to 11) + 103/103 zero, p∈[100,2000). `p≡19 mod24` = (χ₂(2)=−1)
  ∧ (μ₃ present).
- **Reduction chain (status-tagged):**
  - `[PROVED]` p≡1 mod4 ⇒ FLD=0 (negation antisymmetry); p≡3 mod4 ⇒ `FLD = 2·S+`, `S+=Σ_{T+}χ₂`.
  - `[VERIFIED 86/86, NOT proved]` **L1:** `|S+| = F4 = Σ_{p/4<a<p/2}χ₂`.
  - `[PROVED here]` **L2:** the a→2a fold gives `E4 = D(1+χ₂(2))/(2χ₂(2))`, so
    `F4 = 0` at p≡7 mod8, `F4 = D` at p≡3 mod8.
  - `[CITED — Dirichlet]` `D = (2−χ₂(2))·h`. `[VERIFIED classical]` first moment `Σa·χ₂(a) = −p·h`.
  - Chaining ⇒ `|FLD|=6h` at p≡19 mod24, else 0 — modulo L1 alone.
- **The enforcing symmetry is outside F_p `[VERIFIED + reasoned]`.** The reflection candidate (D₆'s
  six reflections `z→ζ₆ᵏz̄`) is killed exactly (0/16 flip σ·χ₂), because conjugation `ω→ω²` does not
  descend to the prime field (no nontrivial F_p automorphism; it maps the ideal to the conjugate
  prime = the twist). The conservation is enforced by no within-F_p symmetry — its home is the
  lattice / biquadratic field ℚ(√−p,√−3), whose p mod 24 splitting is the vanishing law.
- **L1 status, no verdict either way.** Verified 86/86, not proved. Routes tried and their honest
  outcomes: single-interval image (T+ is a lattice-line∩triangle, 6–33 scattered runs — not an
  interval); multiplicative set-stabilizer (none flips σ·χ₂); first-moment/carry fold (**dissolves**:
  the carry `k=σ`, so `T1 = χ₂(M)·p(1−χ₂(2))h + p·FLD` — FLD plus a Dirichlet term, no independent
  handle on S+; verified 55/55). Neither "needs analytic machinery" nor "elementary and reachable"
  is claimed — both were asserted earlier and retracted (§XI.13). Closing L1 is an open lemma.
- **Sign of FLD `[VERIFIED consistency, not intrinsic]`.** `sign(FLD) = −χ₂(M)` (M = flap-coordinate
  slope) verified 54/54 at p≡19 mod24. It is convention-robust (orientation flip flips both sides).
  **But** χ₂(M) and sign(FLD) reduce to **none** of ~25 tested intrinsic invariants (χ₂(2/3/√−3),
  π_p components, sign(L)/χ₂(L) from `4p=L²+27M²`, χ₃(2), p mod48). So the sign-pinning reads as an
  internal consistency between two reduced-basis-dependent quantities, **not** shown to be a deeper
  arithmetic symmetry — this does not refute the "sign possibly convention-dependent" flag. Decisive
  open check: does sign(FLD) flip under π_p↔π̄_p (basis chirality)? Not yet run. **The magnitude
  `|FLD|=6h` is the intrinsic result; the sign is unresolved.**

## VIII.5 — Measured information extraction about `d` (the D1 transfer and the Aut-quotient family)
*(`d1_definitive.py`, `d1_bitmap.py` — SageMath 10.9; `RESULT_d1_information_extraction_v1.md`.)*
**A rigorous, reproducible extraction of information about the scalar `d`, measured in bits.**
Construction: `E: y²=x³+7 / F_43`, `n=31` prime; quartic Kummer cover `L=K[T]/(T⁴−(x³+7))`;
`ψ(P)=[place(x₀,v)] − [place(x₀,−v)]` with `v=√y₀` if `y₀` is a square in `F_p`, else `√(−y₀)`.
- **`ψ` is NOT a homomorphism, even up to sign** (`D₁+D₁ ≁ ±D₂`) — a genuine non-homomorphic set-map.
- **The ± collapse is intrinsic to `ψ`, not the "up to sign" convention:** image **16/31 under plain
  linear equivalence AND 16/31 up to sign** ⇒ **0.954 bits** (→ 1 bit asymptotically).
- **Bit content of the Aut-quotient family**, same curve:

  | quotient | image | bits `log₂(n/image)` |
  |---|---|---|
  | μ₂ (negation) — the level ψ attains | 16/31 | 0.954 |
  | μ₃ (GLV, `x↦βx`) | 11/31 | 1.495 |
  | μ₆ = Aut(E) | 6/31 | 2.369 |
  | asymptotic `log₂\|Aut(E)\|` | — | **2.585** |

- **The bits chain additively:** `μ₆=μ₂×μ₃`, coprime orders ⇒ asymptotically `1+log₂3=log₂6`.
- **Bound achieved, with scope.** `n` prime ⇒ `E(F_p)` has **no proper subgroups** ⇒ the only fibres
  available to a group-action quotient are `Aut(E)=μ₆` orbits ⇒ this family extracts **≤ log₂6 ≈
  2.585 bits**; measured **2.369** at `p=43`. **Outside the scope of that bound and unmeasured:**
  maps that do **not** factor through an `Aut`-quotient (§X.3); other covers `w^k=x³+7`, `k≠4`; other
  place-combinations; any `p` other than 43 — in particular nothing is measured at secp's `p≈2²⁵⁶`.
  `ψ` is non-homomorphic yet factored through μ₂ — **one instance, not a bound over that class.**
*(Recorded as a measured extraction and its size. Assessment of its use is out of scope here.)*

---

# PART IX — HOW IT FITS  (what is established; what it does not establish)

1. **Prime-order rigidity `[PROVED]`** ⇒ the only chaining readout is `d`; forces `C_t` smooth and
   `σ⊥s_y`; bounds the amicable transfer **only in the homomorphic case**.
2. **KS/Weil `[PROVED|KS]`** ⇒ every **bounded-degree** cheap readout is spectrally flat (√p floor)
   **at the scales tested**.
3. (1)+(2) ⇒ concentration ≡ chaining ≡ correlation-with-a-character, **for bounded-degree
   readouts**. For general poly-time readouts there is **no reduction in hand** (`[GAP]`, V-3).
4. New this session: the μ₆-symmetric part of the joint readout is provably flat (VIII.2), the cheap
   μ₆-isotype-pure complement is bounded above a power floor (VIII.3), and an exact conservation
   (VIII.4) turns out to be a **class number** — real structure whose enforcing symmetry lives
   outside F_p. None of this is a statement about ECDLP.
5. **What this does NOT say.** It does not say the doors are exhaustively mapped; it does not say the
   DLP is the sole residual; it does not say ECDLP is hard. The frontiers below are live. In
   particular the 0.93 shadow's **frequency-pattern** basis (VIII.1) and the **non-covariant cheap**
   readouts (VIII.3) are exactly the "right basis not yet found" places the language rule warns about.

---

# PART X — LIVE FRONTIERS  (carried verbatim from v2 §X unless a resolving artifact is named)

1. **A cheap *partial* of the joint (x,y) shadow** *(H3 verbatim)*: "…Can a cheap readout capture a
   *fraction* of that alignment? **Highest-value lead.**"
   → *Status: **PARTIALLY ADDRESSED, STILL OPEN.** VIII.3 tested the 6 μ₆-isotype-pure cheap readouts
   → no concentration above φ≈0.1–0.5 (scoped, power stated). VIII.1 showed the 0.93 scalar magnitude
   does not separate character from random in the scalar-fidelity statistic. **Still open (named,
   outside every test run):** the frequency-support/μ₃-pattern basis of the joint readout; the
   non-μ₆-covariant cheap readouts (x mod 2, high bits); sub-floor φ; larger p.*
2. **The odd-half / `T_y` max-bound.** → ***RESOLVED-BY `kohel_shparlinski_ants4_2000.pdf` (2026-07-17).***
   `max|U(a,b,c)| ≤ 4√p+1`, uniform, explicit, no polylog; no exceptional (b,c) escapes. §XI.11.
3. **Non-homomorphic amicable map.** → *OPEN. Only the homomorphic case is ruled out (§XI.4); the
   protecting lift obstruction is `[HEURISTIC]` (xedni). **One concrete instance now measured**
   (VIII.5, `d1_bitmap.py`): a non-homomorphic set-map `ψ` whose image factors through μ₂, extracting
   0.954 bits. That is one instance measured, **not** a bound over the class — the frontier stays OPEN.*
4. **`S₄⁺` / first-fall degree.** → *OPEN. `[PROVED,general m]` re-graded `[HEURISTIC+CITED]` (Part VI).*
5. **Everything at secp's actual p.** → *OPEN and global — the banner.*
6. **`C_T` inter-coordinate coupling** (`λ₂≠λ₃`, ~2–3%). → *OPEN — bounded-by `ANOMALY_DRILL_01`.
   Any coupling `<≈2%` **in the Frobenius-norm estimator at p≈2¹⁷, this orbit/generator**. A coupling
   in another statistic/basis or near `2²⁵⁶` is untested. Next: `‖D_odd‖_F` targeted at n~10⁶–10⁷,
   vary generator/prime.*
7. **Two-point / joint-SET bilinear bound (2-variable KS).** Part V's bound is a single sum over one
   `d`; it does not cover joint/multi-key readouts of the SET `{x([dᵢ]G)}` nor the two-point panel.
   → *OPEN. Next: structured pairs (`Q=[2]P,[3]P`, sextant-aligned) at k=32,64.*
8. *(new, v3)* **L1: `|Σ_{T+}χ₂| = F4`** (VIII.4). → *OPEN. Verified 86/86; a proof would complete
   `|FLD|=6h(−p)`. It is a lattice-line∩triangle character sum equal to a quarter-interval sum.*
9. *(new, v3)* **FLD-sign intrinsic-ness** (VIII.4). → *OPEN. `sign(FLD)=−χ₂(M)` verified 54/54 but
   reduces to no tested intrinsic invariant; the π_p↔π̄_p chirality check is not yet run.*

**Also live (lower stakes):** full-resolution `σ₁,σ₂` boundedness; is `ε` an arithmetic object
(symbol/norm condition)?; large-prime rank-10 μ₃ split; an unconditional Part V (needs Weil–Deligne +
KS reproved — a `[GAP]`). Cross-project: finite-field zeta as an RH test-bench; LRC↔μ₆/μ₂ shadow.

---

# PART XI — RETRACTION LEDGER  (carried verbatim from v2 §XI; do not re-claim these)

1. χ₂ "doubling transport law" → the textbook duplication formula. CITED, not a finding.
2. Test-A cubic-moment "null" → zero statistical power (N=82 needs f=1.0).
3. G "tested the blind corner" → tested a proxy (`d mod k`, a known-null hardcore bit).
4. v11 amicable "wall" → strawman; only the group-homomorphism case was ruled out. *(Re-claimed by
   v1, withdrawn again; §X.3.)*
5. v14 "the ‖F‖_A gap is the only analytic door" → wrong; Wiener norm is a red herring.
6. v17 "6–7σ soft shadow" → a null-mismatch artifact (shuffle null destroyed the μ₆-invariance the
   readout has by definition). Against the correct μ₆-invariant null, z≈0.
7. aligned-leak scaling `~1/√log p` → retracted; data drift over too small a p-range.
8. `[PROVED, general m]` first-fall curve-independence → `[HEURISTIC+CITED]`; the isobaric fact is
   verified, the implication is not.
9. "no concentration ⟺ ECDLP hard" → withdrawn; `⟸` trivial, `⟹` has no reduction in hand.
10. "KS bound covers χ₂" → withdrawn. KS's Ψ is **additive** (Artin–Schreier); χ₂ is multiplicative
    (a Kummer argument is a different theorem, not cited). χ₂'s flatness rests on the separate
    `‖F‖_A` argument. Do not re-claim KS bounds χ₂.
11. "KS / Lange–Shparlinski" pairing for the mixed sum → withdrawn. **KS alone** carries it; L–S
    Lemma 2.4 bounds the untwisted `Σ_P χ(f(P))`, no `ω(P)` factor. Do not re-pair.
12. *(new, v3)* **"L1 needs analytic machinery / an honest wall"** → withdrawn. Asserted from three
    failed elementary probes; the a→2a fold (elementary) applies to T+ (VIII.4). A difficulty verdict
    dressed as honesty.
13. *(new, v3)* **"L1 elementary and reachable through the first-moment formula"** → withdrawn. Built
    on two unchecked, narrow-sample-generalized formulas: `Σa·χ₂(a)=−p(2−χ₂(2))h` (WRONG; it is
    `−p·h`, 120/120) and `Σχ₂(a)c(a)=0` (WRONG; it is `p(1−χ₂(2))h`). The corrected algebra shows the
    first-moment thread **dissolves** — no independent handle on S+ (verified). Neither the wall nor
    the reachability claim was earned; both were flagged by the self-certifying word "honest."

*(Process note carried forward: the recurring failure mode this session was reaching for
"honest/honestly" exactly when asserting unchecked algebra or generalizing from a few primes. The fix
is to run the check the word papers over. See feedback memories `self_cert_words_audit_trigger`,
`negative_bias_enlarge_nulls`.)*

---

# APPENDIX A — EMPIRICAL NULLS (scoped facts with firing controls — NOT completeness claims)

> **Critical caveat (verbatim, H3):** "every one of these used a *misaligned* readout, so each is a
> scoped fact about that readout at that scale, **provably consistent with a hidden aligned leak**."

Each bounds a *magnitude* about *that object at that scale with a control that fired* — at
p=211→6397. Single-key `(X,Y)→n,k,D` ~1e-5 bits (controls fire); bilinear-additive joint sum flat
O(n) (planted rank-1 fires); H² carry not coordinate-leaked (z=849); difference-set μ₃/cubic/xy
geometry at the AP-control floor (control fires 13–36×); no metastable soft mode (`|λ₂|~1/√n`);
finer-m difference scan at floor (z=1050); phase-hunt beyond μ₆ at floor (9 CM/Frobenius candidates —
the only *known computable* phase structure is the μ₆ group); GLV/CM ⊥ key-coordinate on the 82;
derr↔cap = a bit-length confound (dissolves at fixed bits, P=0.34–0.89). **`λ₂` transfer eigenvector
~50% μ₃-cov / `λ₃` up to 85% (real, broadband, no closed form — OPEN, not resolved).** *(Language:
each is "at the matched floor for that readout/statistic/scale," never "nothing there"; a hidden
aligned leak, another basis, or `2²⁵⁶` is consistent with every one of them.)*

**Also scoped (carried verbatim from H3 — each a magnitude with a firing control, NOT a completeness
claim):** hybrid sum `χ_k`×additive ≈2√p; scalar-mult `ψ(d)`; cubic-moment / S3 tensor; bilinear
difference-set (powered to 1.4%); joint (x,y) *magnitude* distribution (CM=non-CM); 3-point group
law / collinearity; index-calculus relation yield (β-invariant lever 1.5×, bounded) and S₄/S₅
decomposition (β-lever → 1.0); easy-target predictability (no lever).

# APPENDIX B — HEURISTICS
`[HEURISTIC]` "genus-1 ⇒ no index-calc lever" (Diem 2011). `[HEURISTIC]` canonical-lift obstruction
(xedni) protecting the amicable transfer — what §X.3 turns on.

# APPENDIX C — CITED INPUTS (verify before relying)
- **✅ Kohel–Shparlinski**, ANTS-IV 2000, LNCS 1838, 395–404. **VERIFIED 2026-07-17** against the
  source; `kohel_shparlinski_ants4_2000.pdf`, SHA-256 `645d9022e029055271ae60387518b440075fad282886d8baa9df35f5b55d8d2a`.
  Thm 1 `|S|≤Σmᵢdeg(𝔓ᵢ)q^{1/2}`; eq (3) `|S|≤2deg(f)q^{1/2}`. `ω∈Hom(E(F_q),ℂ*)`, ψ **additive**.
  **Scope from the text: additive ψ only — NOT χ₂ (§XI.10).**
- **⚠ Lange–Shparlinski**, JMC 1 (2007) 1–11; SHA-256 `f29c524a9670…c6edec`. Lemma 2.4 bounds the
  UNTWISTED sum only. **NOT load-bearing; do not cite for the mixed sum (§XI.11).**
- Dirichlet class-number formula `h(−p)=D/(2−χ₂(2))` and first moment `Σa·χ₂(a)=−p·h` — classical,
  verified in code (Part VIII.4).
- Weil–Deligne (needed for an unconditional Part V — a `[GAP]`).
- Boneh–Shparlinski (LSB/MSB hardcore) — does **not** support the withdrawn `⟺` of V-3.
- Xedni-calculus lift obstruction (Silverman 1998; JKSST 2000). MOV/Tate. BFS first-fall. Diem 2011.

---
*Full detail: `cap_law_proofs_v1.md`, `masked_structure_findings_v1–v38.md`, `RESULT_*` files
(this session's threads), `glv_*` narratives, handovers in `archive_handovers/`. Degradation trace:
`DEGRADATION_AUDIT_H3_TO_MASTER_v1.md`. External-review adjudication: `GLM_AUDIT_RESPONSE_v1.md`.*
