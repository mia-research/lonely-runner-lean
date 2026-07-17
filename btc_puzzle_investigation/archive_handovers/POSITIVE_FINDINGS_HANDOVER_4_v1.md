# Positive-Findings Handover 4 / Project Summary — secp256k1 curve-arithmetic structure (v1)

**Date:** 2026-07-17. Supersedes nothing; this is the consolidated **structure map** — everything we
**know** (proved / verified), laid out so any object here can be coded directly. Empirical nulls and
heuristics are a short appendix, stated as **scoped facts, never closures**. Positive framing: each
structure is real; where something is bounded, that is a *magnitude*, not "no structure."

**Grades:** `[PROVED]` rigorous · `[PROVED|KS]` proved given the cited Kohel–Shparlinski/Weil bound ·
`[VERIFIED]` exact/numeric at tested scale · `[CITED]` from literature · `[HEURISTIC]`/`[EMPIRICAL]`
in appendix only.

---

# PART I — DEFINITIONS & CONSTANTS (code-ready)

**Curve.** `E: y² = x³ + 7` over `F_p`, `p = 2²⁵⁶−2³²−977`. Prime order `n = #E`, generator `G`.
`j=0`, CM by `ℤ[ω]`, `ω=e^{2πi/3}`. `d ↔ [d]G = (x_d, y_d)` is a bijection `ℤ/n ↔ E` (full order n).
Small test curves: `y²=x³+7 / F_q`, `q≡1 mod 3`, `#E` prime (so `q≡1 mod 6`).
Imports used: `ecc_secp256k1` (`P`=p, `N_ORDER`=n, `scalar_mul`); `int1_frame_operator_v1.build(p)`
→ `(eis, eps)`; `lift_sextant_rhombus_law_proof_v2.reduced_basis(p)` → `(R1,R2)`.

**Characters.** `e_p(t)=exp(2πi t/p)`, `e_n(t)=exp(2πi t/n)`. `χ_k(a)=a^{(p-1)/k} mod p` mapped to
`k`-th roots of unity (`χ₂`=Legendre). Curve character `χ_a(P):=e_n(a·d(P))` — the DLP-frequency.

**Eisenstein lift.** `eis(x)` = representative of `x∈F_p≅ℤ[ω]/(π_p)` in the fundamental domain
`P={uR₁+vR₂ : u,v∈[−½,½)}`, `{R₁,R₂}` a reduced (120°) basis of the ideal `L=(π_p)`. Coefficients
(exact `Fraction`): `DET=R₁[0]R₂[1]−R₁[1]R₂[0]`, `u=(z₀R₂[1]−z₁R₂[0])/DET`,
`v=(z₁R₁[0]−z₀R₁[1])/DET` for `z=eis(x)`. Norm `N(z)=u²−uv+v²`.

**GLV / CM.** `β∈F_p` a primitive cube root of 1 (`β=g^{(p-1)/3}`, `g` a non-cube); `λ∈ℤ/n` with
`λ³=1` chosen so `x_{λd}=β·x_d` (verify the pairing on a few d). `μ₃=⟨β⟩` acts on x by `x↦βx`;
`μ₆=Aut(E)=⟨β,−1⟩`; `[−1]` fixes x, negates y. `eis(βx)=ω·eis(x)` (reduced into P).

**Cap Law objects.** With `⟨R₁,R₂⟩=−p/2`, mult-by-ω on `L` is `M=[[0,−1],[1,−1]]`. Flap indicator
`ε(x)=eps(x)∈{0,±}`; **`flap ⟺ |u−v|>½`, core `|u−v|≤½`** (orientation flips to `|u+v|>½` at some
primes — detect against `ε`). Flap sign `σ(x)=sign(u−v)` if `|u−v|>½` else `0`. Sextant = 60°-sector
of `eis(x)`; norm-band from `N(eis(x))`.

**Twisted sums (the leakage objects).** For `a∈ℤ/n`, `b,c∈F_p`:
`T(a,b)=Σ_{d=1}^{n-1} e_p(b·x_d)·e_n(a·d)` (x-only);
`U(a,b,c)=Σ_d e_p(b·x_d+c·y_d)·e_n(a·d)` (full; `T=U(·,·,0)`).
Readout correlation: `Corr_F(a)=(1/n)Σ_d F(P_d)e_n(-a d)=Σ_b F̂(b)T(a,b)/n`.
Compute by FFT over `d`. (Float OK for these magnitudes — roots of unity, no key in path.)

**The special object.** `xy := x·y mod p`. **EVEN×ODD ⇒ `xy` is ODD in d**; under β, `x↦βx, y↦y` ⇒
`xy↦β·xy` (**μ₃-weight 1**). `s_y(d)=+1 if y_d<p/2 else −1` (ODD in d; the free compressed-pubkey bit).

**Semaev.** `S₃(a,b,c)=(a−b)²c²−2((a+b)(ab+A)+2B)c+((ab−A)²−4B(a+b))`, `A=0,B=7`. Higher
`S_{m+1}(x₁..x_m,t)` by resultants (fresh aux var per level; divide spurious square factor for m≥4).

**Key coordinate `(n,k,derr,D)`.** `A=2^{bits−1}`, `band_offset=d−A`. `(n,k)`=best rational of
`band_offset/A` over `n≤256` (`argmin |n(d−A)−kA|`, reduce by gcd). **`derr=|n(d−A)−kA|`** (residual).
`D_terms`=greedy unit-fraction (Engel) expansion of d — an **invertible** d-signature. Curve-identity
`D` in `[n]P=(n+k)Q+(n·D)G`, `r=nD−(2^{N−1}k mod n)` (a different, large/signed D). Datasets:
`solved_keys_augmented_v1.csv` (82 real, known d), `constructed_keys_fullrange_v1.csv` (36k, known d,
has `a_glv,b_glv,sextant,chi6X,chi6Y,chi2Y`), `constructed_keys_1to160_100k_exact.csv`.

**Transfer/Koopman.** Label `l(d)`=coarse fn of `P_d`; `M[i,j]=#{d:l(d)=i,l(d+1)=j}/#{d:l(d)=i}`;
`|λ₂|` near 1 & persistent = soft mode; thermal if `|λ₂|~1/√n`. Valid null = ABSOLUTE `|λ₂|` decay +
multi-shuffle z (NOT the shuffle *ratio* on 2-state labels, NOT `np.roll` — both are artifacts).

---

# PART II — THE PROVED STRUCTURE (lead with what we know)

## A. The one theorem everything rests on — prime-order rigidity `[PROVED]`
`E` has prime order ⇒ **no proper subgroup / quotient / 2-torsion**. This single fact forces:
- **Cocycle rigidity:** the only coarse readout `f` with `f(P+Q)=φ(f(P),f(Q))` (that "chains") is
  `d` itself. (Level sets would be a congruence = cosets of a subgroup; prime order forbids it.)
- **`σ ⊥ s_y` exactly:** `Σ_d σ(x_d)s_y(d)=0`, fixed-point-free (no `2d=n`).
- **Amicable homomorphism = 0** (coprime orders).
- **Semaev `C_t` smooth genus-1 for every target** (no 2-torsion x-coord).
These are one theorem in four costumes.

## B. The leakage question is COMPUTATIONAL, not information-theoretic `[PROVED|KS]`
The **aligned** readout `F̂(b)=conj(T(a₀,b))/|T(a₀,b)|` has no cancellation:
`Corr(a₀)=(1/n)Σ_b|T(a₀,b)|` ≈ 0.37 (x-only) / **0.93 (joint x,y)** vs ~0.01 generic. **The
information about d is fully present and bounded-recoverable; only building `F̂` (needs `T` ⇒ all
`x_d` ⇒ the DLP) protects.** Every "misaligned" readout sees exactly `√p` noise (Weil/KS). Phase
alignment — not Wiener norm — is the sole axis (`χ₂` saturates `‖F‖_A≤√p‖F‖_∞` and provably does not leak).

## C. ★ The unified closure of the leakage frontier `[PROVED|KS  +  =ECDLP]`
This is the capstone; it makes B precise and closes every "door."

- **Reduction (exact, unconditional):** `Corr_F(a)=⟨F,χ_a⟩_d`; **concentration** `C(F)=max_a|Corr_F|/‖F‖₂`
  is `Ω(1)` **⟺** `F` correlates `Ω(‖F‖₂)` with a single character `χ_{a₀}(P)=e_n(a₀ d)`. The `χ_a`
  **are exactly the additive cocycles.** So **spectral-concentration ≡ chaining ≡ correlation-with-a-
  cocycle-character — one door**, seen from three sides (v14 leakage ≡ v31 cocycle ≡ spectral hunt).
- **Bound (`[PROVED|KS]`):** any readout `F=ψ∘f` with `deg(f)≤D` on E has
  `|Corr_F(a)|=O_D(√p·polylog/n)=` the floor (KS/Weil mixed character sum). Covers **all** bounded-
  degree readouts including high-Wiener `χ₂` (the Wiener-norm route leaves that vacuous; the direct
  sum bounds it) and `e_p(xy)`.
- **The escapee is the DLP:** the only `C=1` readout is `χ_{a₀}=e_n(a₀d)` itself — not a bounded-
  degree coordinate function; it is the discrete log. For **general poly-time** readouts, "no
  concentration" **⟺ ECDLP hard** (a concentrated cheap F = a hardcore-predicate break,
  Boneh–Shparlinski). The residual door is not a gap — **it IS the DLP.**

**The door map** (each shut, for a specific reason): additive-subgroup (prime order) · MOV/pairing
(embedding degree ~254-bit) · anomalous (`#E≠p`) · Weil-descent (prime field) · carry/H² (coordinate
null) · **spectral concentration (this, PROVED|KS for bounded-degree, =ECDLP for the rest).**

## D. Curve / lift geometry `[PROVED]`
- **Cap Law:** `ε(x)≠0 ⟺ |u−v|>½`. Forced by hexagonal geometry (ω-matrix `M=[[0,−1],[1,−1]]`);
  core/flap densities ¾ : ⅛ : ⅛; shape constants (½,¾,33,3/16,¼,1/6) are θ-independent lattice
  geometry (zero secp arithmetic content).
- **σ is μ₃-invariant** (`σ(βx)=σ(x)`, unconditional) and `σ(−x)=−σ(x)` ⇒ σ = μ₂-isotypic part of μ₆.
- **GLV μ₃ zero:** `Σ_d ψ(d)χ₃(x_d)s_y(d)=0` exactly.
- **Lift-sextant rhombus / sextic:** sextant = exact θ-area law of a 60° rhombus; χ₆ uniform;
  sextant⊥χ₆; `NORM` mean 1/6; GLV `β≡ω²`.
- **Amicable correspondence:** `E(F_p)≅ℤ[ω]/(π_p−1)≅F_n` (partner field = CM coord ring); `π_n=1−π_p`;
  the coordinate map φ **is** the DLP (transfers no advantage).

## E. Semaev / index-calculus structure `[PROVED / PROVED|KS]`
- `S₃` irreducible/ℚ; `Δ(t)=−86704128·(t³+7)⁴` ⇒ `C_t` smooth genus-1 for every t (prime order).
- **First-fall degree of the decomposition system `{S_{m+1}=0, g(x_i)=0}` is CURVE-INDEPENDENT**
  `[PROVED, general m]`: Semaev polys are **isobaric** under `wt(x_i)=1, wt(A)=2, wt(B)=3` (S₃ wt 4,
  S₄ wt 12), so the **leading form is free of A,B**; first-fall = leading-form invariant [CITED BFS]
  ⇒ no CM/GLV elimination lever beyond `|Aut|≤6`. Matched control confirms.
- **S₄ leading form = the cusp (`y²=x³`) summation polynomial** (secp → additive-group summation
  `Σuᵢ=0` at infinity); every S₄ fibre is singular exactly on the diagonal `xᵢ=xⱼ` (generic to
  symmetric polys).

## F. Character-sum bounds `[PROVED / PROVED|KS]`
- `Σ_b|T(a,b)|²=p(n−2)` (a≠0); Parseval `Σ_a|Corr_F|²=‖F‖₂²`; `‖F‖_A≤√p‖F‖_∞`.
- **Odd-half / T_y bound:** `max_a|U(a,b,c)|=O(√p·polylog)` **uniformly over all (b,c)** `[PROVED|KS]`
  — `bx+cy` is a pole-order-≤3 rational function on E, same KS/LS class as x. Empirically: max/√p
  bounded ~3.2–3.7, sub-log-p, argmax generic (no scar), CM=non-CM.
- **`Corr(a₀)=√(πn)/2`** (Porter–Thomas Rayleigh mean) `[DERIVED+VERIFIED]`.

## G. The `xy` object — real structure (do NOT bury this) `[PROVED / VERIFIED]`
- `xy` is **odd-in-d + μ₃-weight-1** — the symmetry type of the *odd half* of the d-spectrum that x
  alone cannot see. `sign(xy)` lies 100% in that odd subspace; distinct from the μ₃-*invariant* `s_y`.
- **The odd/even d-spectrum carry EXACTLY equal mass** (`avg|U(·,·,c≠0)|²/avg|U(·,·,0)|²=1.0004`) —
  the shadow is a full equal half, not a correction. (`avg_a|U|²=n` for all (b,c) `[PROVED]`.)
- **`xy` is the single-key `D`-shadow** (`(X·Y)mod m ↔ D_terms mod m`, KNOWN_FACTS) — now with the
  structural "why" (odd+μ₃).
- **`e_p(xy)` is provably the MOST T-aligned cheap readout** (beats χ₂/χ₃/χ₆/ε at every prime;
  spectral hunt) — its `C/floor` is a bounded ~1.3 (flat over p=211→6007). Real alignment, bounded by
  §C to exactly where every cheap readout must sit.
- **The joint (x,y) aligned readout leaks 0.93** (the shadow made quantitative); barrier stays
  computational (needs `U` ⇒ DLP).

## H. Substrate (cross-domain, scaffolding) `[PROVED criticality + VERIFIED]`
secp sits at criticality (Weil: `|π|=√p`); `|T|²`~Porter–Thomas (thermal, rigid, no scar). The user's
LRC→φ(n)→Berry–Keating→ζ programme spans **two substrates bridged**: chaotic-GUE (ζ zeros, secp) vs
rigid-arithmetic (LRC φ(n) totatives = hard-gap; Berry–Keating `{πk²}` = picket-fence). "One
programme" = the *bridge*, not one substrate.

---

# PART III — HOW IT ALL FITS (the map)

1. **prime-order rigidity** (§A) ⇒ the only chaining readout is `d`.
2. **KS/Weil** ⇒ every bounded-degree cheap readout is spectrally flat (`√p` floor).
3. (1)+(2) ⇒ **§C closure:** concentration = chaining = correlation-with-a-character; no cheap readout
   concentrates; the escapee is the DLP. Every classical door + the carry are shut.
4. The **real structure** (Cap Law, GLV/μ₆, Semaev-isobaric, `xy` odd+μ₃, equal-mass odd half,
   amicable CM) is genuine and `μ₆`/`√p`-bounded — it does not reduce d **because** of (1)+(2), which
   is a theorem, not a dismissal.
5. **Security = the DLP = cheap spectral concentration**, and that is the sole thing not reducible to
   already-proved structure. It is precisely located, not an open haze.

**What is genuinely open (honest):** the *unconditional* version of §C (needs Weil–Deligne+KS
reproved — cited, not a gap); anything that only switches on near `p≈2²⁵⁶`; and the ECDLP itself,
which §C shows is exactly the residual "door."

---

# PART IV — SCRIPTS / REPRODUCTION (what computes what)

| script | object |
|---|---|
| `phase_structure_T_v1.py` | T(a,b), the aligned/leaking readout (0.37) |
| `xy_interference_U_v1.py` | U(a,b,c), the joint shadow (0.93), symmetry group |
| `t_y_maxbound_v1.py` | max|U| uniform bound (§F) |
| `semaev_elimination_v1.py` | Semaev S₃/S₄/S₅, first-fall, isobaric (§E) — **Sage** |
| `cap_law_proofs_v1.md` | Cap Law + σ μ₃ proofs (§D) |
| `conservation_spectrum_v2.py` | transfer/Koopman, soft-mode (Part I null-discipline) |
| `cheap_partial_shadow_v1.py` | closure extends to (x,y) readouts |
| `joint_set_cocycle_v1.py` | cocycle test (d = unique cocycle) |
| `carry_cocycle_v1.py` | H² carry null |
| `difference_set_xy_geometry_v1.py` | difference-set moments + AP control |
| `spectral_concentration_hunt_v1.py` | the spectral hunt (best cheap = e_p(xy), flat 1.3) |
| `spectral_concentration_closure_v1.md` | the §C analytical closure |
| `cm_amicable_correspondence_v1.py` | amicable CM correspondence (§D) |

Discipline: exact int/`Fraction` in the signal path (keys, (n,k,D), features); float only for
analytic-size character-sum magnitudes. Test every detector on **both** the real 82 and the 36k
constructed (known-d, full power). Every null needs a **firing control** and a power/scaling number.

---

# APPENDIX — empirical nulls (scoped facts) & heuristics

**Empirical nulls** (each a scoped fact about *that object at that scale with a firing control*, NOT
a closure): single-key `(X,Y)→n,k,D` to ~1e-5 bits (KNOWN_FACTS, controls fire); bilinear-additive
joint sum flat O(n) (planted rank-1 fires); H² carry not coordinate-leaked (control z=849);
difference-set μ₃/cubic/xy geometry generic (AP control fires 13–36×); no metastable soft mode in any
x- or y-readout (`|λ₂|~1/√n`, multi-shuffle z); phase-hunt beyond the μ₆ group null (9 CM/Frobenius
candidates); GLV/CM ⊥ key-coordinate on the 82; derr↔cap link = a bit-length confound (dissolves at
fixed bits). These bound *magnitudes*; §C explains why they must be at the floor.

**Heuristics** (plausible, not proven): "genus-1 ⇒ no index-calc lever" (standard prime-field belief,
Diem 2011); the aligned-leak critical exponent (~flat, `1/√log p` retracted). The λ₃ transfer
eigenvector is 85% μ₃-covariant (real) but broadband/no simple closed form — **open**, not closed.

**Cited inputs to verify before relying:** Kohel–Shparlinski / Lange–Shparlinski general-`f` bound;
Weil–Deligne; Boneh–Shparlinski (MSB hardcore); MOV embedding-degree fact.

---
*Nested memory index: `memory/btc_puzzle_INDEX.md`. Prior handovers:
`POSITIVE_FINDINGS_HANDOVER_{,2_,3_}v*`. Findings detail: `masked_structure_findings_v1–v32.md`.*
