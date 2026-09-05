# secp256k1 Curve-Structure Project — Self-Contained Summary (v1, 2026-07-28)

**What this is.** A single, self-contained, replication-oriented summary of the positive structural
findings on the curve `E : y² = x³ + 7` over `F_p` (secp256k1) and the objects derived from it. It
consolidates `POSITIVE_FINDINGS_MASTER_v4.md` (2026-07-20) + `POSITIVE_FINDINGS_ADDENDUM_1_v1.md`
(2026-07-23) + `POSITIVE_FINDINGS_ADDENDUM_2_v1.md` (2026-07-27) + the reciprocity-bridge compendium and
the post-Addendum-2 results (to 2026-07-28). It is written so a colleague **without access to our files**
can reproduce the work: every finding names its script, algorithm, exact parameters, and the numeric
table ("figure") it produced. Predecessors are retained, not deleted.

**Reproduction environment (applies to every replication block).** Python 3; signal-path arithmetic is
**exact** (`int` / `fractions.Fraction`) — no float touches a key, an `(n,k,D)` decomposition, a target,
or a feature (float appears only as an analytic-size character-sum magnitude or as a monotone statistic
ranked against a matched permutation null). `check_no_float.py` greps the signal-path files and must pass
before any test is run. Curve arithmetic: `ecc_secp256k1` (`P=p`, `N_ORDER=n`, exact-Jacobian
`scalar_mul`). Some index-calculus / eigenvalue scripts are Sage. Datasets: the 82 solved keys
(Appendix A), plus MT19937 reference sets `constructed_keys_fullrange_v1.csv` (36k) and `..._100k_exact.csv`
(the same select-bitlen→random-in-band→curve pipeline = a full-power known-generator reference).
**Data integrity: SHA-256 every dataset before use.**

---

## How to read this document

**Grades (carried verbatim from the source artifacts — never dropped or promoted here).**
`[PROVED]` rigorous · `[PROVED|KS]` given Kohel–Shparlinski · `[PROVED|WD]` given Grothendieck–Lefschetz
+ Ogg–Shafarevich + Deligne · `[VERIFIED]` exact/numeric **at tested scale** · `[CITED]` literature ·
`[EMPIRICAL]` measured, not proved · `[HEURISTIC]` · `[OPEN]` · `[GAP]` no reduction in hand.

> ### ⚠ SCALE BANNER — governs every MEASURED row
> Every empirical result was measured at small-to-moderate `p` (`p = 13 → ~10⁵`; some threads `< 2500`).
> **Nothing measured reaches secp's `p ≈ 2²⁵⁶`** — a ~239-binary-order gap. A structure that switches on
> near `2²⁵⁶` would not show in any measured test here, and no measured test has power against it. The
> **only** claims that reach secp are the scale-free/algebraic proofs with no measured input (P1, P2, P6,
> P8–P10, P13, P14, P15, A1.1, A1.2, **B1.5, B1.6**, and the bridge B1/L1/L3 of Part H) and the two
> full-scale nulls (A3.2/A3.3). **B1.1–B1.4 do NOT reach secp** — they are exact identities verified
> **per-cell at small `p`** (≤22 primes, `p≈10³`); their **uniformity** to secp is precisely the open gap
> (frontiers #26/#28), so they must not be listed among secp-reaching claims.

> ### ⚠ STANCE (this project's counter-prior — `btc_puzzle_investigation/CLAUDE.md`)
> We hunt for exploitable structure — **statistical and computational** — and our task is to find *how*
> it leaks, not to confirm that it doesn't. "ECDLP is secure / nothing here / generic / a wall" is the
> training-data reflex we work **against**, not from. A closure (dead / generic / vacuous / bounded-to-
> nothing) is a **graded claim** at the same bar as `[PROVED]`: name the object, the class of
> observable/algorithm it closes, and the power+scope, or it is an overclaim. **An empirical null is not
> a closed avenue.** This raises the bar on closures; it does **not** lower it on finds (every candidate
> keeps a matched null, a firing control, out-of-sample retest, exact arithmetic, and an explicit grade).
> **Out of scope by choice:** how the puzzle integers were selected (the PRNG / generation side).

> ### ⚠ LANGUAGE
> `flat` / `generic` = a statement about one statistic in one basis, never a verdict of absence. A `√p`
> bound is a **magnitude** (it lives in a symmetry type / eigenvector / subspace), not "no structure".
> Every bound carries its **power** and **scope**. Dissolution of an anomaly into a sharper law is a
> positive result — state the law and its precision.

**Note on the information-theoretic vs computational framing (correction applied 2026-07-28).** Master v4
§VI carried a headline "Leakage is COMPUTATIONAL, not information-theoretic `[VERIFIED]`". The precise
technical content is retained (§3 below): the aligned readout that reaches `Corr ≈ 0.93` requires a
DLP-cost object (`T`, hence all `x_d`) to build. But the **header over-generalizes** and is restated
under the counter-prior: single-instance secrecy is vacuous (`H(k|P)=0`, determinacy — the key is not
*hidden*, which says nothing about *structure*); the **ensemble/derived-feature statistical channel is
open**; and a statistical *null* cannot certify computational security (nor a break) — it runs both ways.

---

# PART A — THE STANDING LEDGER  *(reconciled across master + both addenda; status tags only)*

Each line is independently verifiable from the named artifact. No line carries an "X for ECDLP" clause.

## A.1 Proved  *(rigorous; scale-free unless a scope is noted)*

| # | statement | grade |
|---|---|---|
| P1 | `p = 2²⁵⁶−2³²−977 ≡ 3 mod 4, ≡ 1 mod 3, ≡ 7 mod 12`; `n ≡ 1 mod 4, ≡ 1 mod 3`. | `[PROVED]` |
| P2 (L1) | `Σ_{P∈E(F_p)} χ₂(y_P) = 0` exactly at every `p ≡ 3 mod 4`. **Applies at secp.** Converse FALSE. | `[PROVED]` |
| P3 | `C : w⁴=x³+B` genus 3; `Jac(C) ~ E × A_new`, `H¹(C)=H¹(E)⊕H¹_new`, `dim 2+4`. | `[PROVED]` |
| P4 | `ζ₄:(x,w)↦(x,iw)∈Aut(C)` any cubic ⇒ `Q(i)⊆End⁰(A_new)`. | `[PROVED]` |
| P5 | `x³+B` only: `ζ₃∈Aut(C)` ⇒ `Q(ζ₁₂)⊆End⁰(A_new)`, degree `4=2·dim`. | `[PROVED]` |
| P6a | Additive char-sum bound `|U(a,b,c)| ≤ (1+ord_O f)√p+1` (`=4√p+1` for `c≠0`). All `p`. | `[PROVED\|WD]`=`[PROVED\|KS]` |
| P6b | Multiplicative (Kummer): `|Σχ₂(x)e_n(ad)| ≤ 2√p`, `|Σχ₂(y)e_n(ad)| ≤ 4√p`. **KS does NOT give these.** | `[PROVED\|WD]` |
| P7 | `E` is ORDINARY (`a_p = t ≢ 0 mod p`). | `[PROVED]` |
| P8 | **Claim S** — the μ₆ curve selection rule: cross-bidegree pairings vanish. | `[PROVED]`+`[VERIFIED]` |
| P9 | **Claim F** — field-level rule: FIELD part 0 unless bidegrees match (6 sectors); CURVE part 0 unless `k` matches (3 sectors). | `[PROVED]`+`[VERIFIED]` |
| P10 | The missing `ℤ/2` is the sextic twist (`−x ↦ y²=x³−B`). | `[PROVED]` |
| P11 | **Cap Law** — flap `⟺ |u−v|>½`; core/flap densities `¾:⅛:⅛`. | `[PROVED — continuum]` |
| P12 | **CM spine** — `eis(βX)=ζ·eis(X)+c`, `c∈{0,±R}`, densities `¾:⅛:⅛`. | `[PROVED — continuum]`+`[VERIFIED]` |
| P13 | `Hom(E,A_new)=0` at secp (Tate; disjoint Newton slopes). **Now UNCONDITIONAL — N2 discharged by A1.1.** | `[PROVED]` |
| P14 | **Prime-order rigidity** — the only chaining readout is `d`; `σ⊥s_y`; every Semaev `C_t` smooth genus-1. | `[PROVED]` |
| P15 | **Reduction** — concentration `C(F)=Ω(1) ⟺ F` correlates `Ω(‖F‖₂)` with a character `e_n(a₀d)`. | `[PROVED]` |
| A1.1 | `A_new` **supersingular** at every `p≡3 mod4`, every separable cubic, **incl. secp** (μ₄/quaternion argument; no CM/`j=0`/measured input). Closes N2. | `[PROVED — scale-free]` |
| A1.2 | secp is a **Silverman–Stange amicable pair**: `#E(F_p)=N_ord` and `#E(F_{N_ord})=p`. Enforcing group = `CM(ℤ[ω]) ×` sextic-twist class of `b=7`. | `[PROVED — at 256-bit primes]` |
| A1.3 | The flap χ₂-imbalance **is a class number**: `P1: (−1)^N=χ₂(2)` `[THEOREM]`; `A=Σχ₂(s)=(2−χ₂(2))h(−p)` `[PROVED]`; P2 reduces to one identity (†). | `[PROVED]` + 1 open step |
| A1.4 | `Aut(E)`-orbit bit-ladder has a **constant** ceiling `log₂6 ≈ 2.585` bits (n prime ⇒ no proper subgroups). | `[PROVED]` |
| A1.5 | Low-complexity `(n,k,D)` stratum = the **Dirichlet reciprocal-floor lattice** `{⌊lo/q⌋}`; island boundary exactly `√lo=2^{(N−1)/2}`. | `[PROVED + VERIFIED]` |
| A1.6 | A gauge-free, basis-invariant covariant-weight form `W_cov(V)` (a trace; needs only the subspace). | `[PROVED]` |
| A1.7 | Three exact conservations of `U(a,b,c)`: alignment is an `l¹` norm; `Σ_{b,c}|U|²=p²(n−1)` (pinned + **identical for character and random** ⇒ the l² total cannot separate them; it does NOT forbid unitary concentration); `Σ_a|U(a,b,c)|²=n(n−1)` per frequency. | `[PROVED]` |
| A2.8 | `(n,k,D)` validity domain = **contractible Farey solid**, realized as a 1-D coprimality net; symmetry is `k↦n−k` (`ℤ/2`), **not μ₆**. | `[PROVED]` |
| A2.9 | Complexity filtration: exactly 3 levels `T∈{0,1,2}` (to width `7·10⁵`); the `T=1` stratum shatters into the Dirichlet lattice (generic in `L`, no 2-adic role). | `[PROVED]` |
| B1.1 | The **120° law is an EXACT identity**: `α₂/α₁=ζ₃` (`g=deg gcd(L*(T),L*(ζ₃T))=2`) at every cell of **22 primes** incl. 10 out-of-sample in secp's class `p≡7 mod12`. | `[PROVED — exact, at cells]` |
| B1.2 | **N1 mechanism** — one exact identity: `V₂=V₁²±2p` ⇒ `v=u²−¾` (Eisenstein norm form) ⇒ two Frobenius half-angles differ by exactly 120°. Forced `v∈[−¾,+¼]`, `max_a v ≤ ¼` **unconditional**. | `[PROVED — exact]` |
| B1.3 | `S_y ≤ 2` reduces to the **sign of one L-poly coefficient** (`v≤0 ⟺ e₂≥−2p`); equivalently `|V₁(a)|≤√3·√p` — a **sub-Weil bound** (86.6% of Weil `2√p`). | `[PROVED — algebra]` |
| B1.4 | The `v≤0` route to `S_y≤2` is **FALSE** — exact rational counterexamples (`p=127,163,211`); `v>0` occurs in **both** strata at ~4–6% of classes (a **suppressed** rate — retraction 41, not "generic"). **Route closed; inequality NOT refuted** (`v≤0` was sufficient, not necessary). | `[PROVED — exact]` |
| B1.5 | **Jacobi sign law** `J(χ₃,χ₄)=−p` (`p≡1 mod3`, secp's class) / `+p` (`p≡2 mod3`), both halves. Stickelberger→Kronecker→reductions. ⇒ `m=1` at secp `[CONDITIONAL]→[PROVED]` once in-file moves applied. | `[PROVED — modulo (D2); (D2) discharged, B2.1]` |
| B1.6 | The `ℓ≥5` ideal-level CM route **collapses to a rational symbol** (both bridge sides are symbols of the same rational `U=|t−1|`) — forced, derived before running. | `[PROVED — forced]` |
| B1.7 | Twist-orbit "Arm II" **dissolves** to the exact curve-independent frame identity `⟨f_a,f_b⟩=nI−J`; forced 2nd/3rd-order objects (additive autocorr `n(nδ_b−1)`, multiplicative bispectrum `≡0`). | `[PROVED — forced, exact]` |

**Citations discharged.** **B2.1** Stickelberger verified against Katre (3 caveats: proof-hypothesis
`j,k,j+k≢0 mod m`; `F_q` digit-sum form; ideal not value). **B2.4** Silverman–Stange arXiv:0912.1831 is
the `p↔#E` bridge citation; Cap Law Thm A steps 1+3 classical (Lemma C still un-located).

## A.2 Measured  *(scale banner governs every row; sample stated)*

| # | statement | sample |
|---|---|---|
| M1 | `A_new` ordinary ⟺ `p≡1 mod4`. | 24/24 |
| M2 | `gcd(L_E, L_new)=1` (disjoint Frobenius spectra — the structural basis of P13). | 18/18, both covers |
| P7′ | `ord_n(p)=(n−1)/6` exact (MOV embedding degree) `=19298681539552699237261830834781317975472927379845817397100860523586360249056`. | `[VERIFIED — 254-bit]` |
| M6 | Supersingular `ord(α²/p)` order sets: CM `{1,3}`, non-CM `{3,4}` (order 4 non-CM only, order 1 CM only, 3 shared). **Sample too small to call a law — open pattern.** | 6 primes each |
| M15 | Character equipartition: `e_n(a₀d)` energy per μ₆-isotype `=1/6` exactly (5 isotypes); the trivial-isotype deficit = the excluded fixed point `d=0=O`; cross-isotype orthogonality ≤1.6e-15. | exact |
| M3 | Saturation (max ÷ `dim·√p`): `bx+cy` (dim4) **0.876**; `bx` 0.909; `χ₂(x)` 0.947; **`χ₂(y)` (dim4) 0.470→½**. A 1.86× gap at identical dimension. | 6 primes |
| M4 | `V(a)=Σχ₂(y_P)e_n(ad)` purely real at `p≡1 mod4`, purely imaginary at `p≡3 mod4`. Parity does NOT cause the ½. | every row |
| M7 | `C_T` inter-coordinate coupling `< ~1.6%` (Frobenius-norm estimator, `n≈1.3×10⁵`, control fired). | 8 curves |
| M9 | Semaev first-fall & solving degree identical for secp/non-CM/j=1728 on matched systems (`d_ff=12`). | `p≤307, m≤4` |
| M10 | Frame operator `λ_max/Tr` exactly ½ on μ₃-core, ¾ on full lift; `¾−½=¼=` flap fraction. | exact |
| M11 | `|FLD(p)|=6·h(−p)` at `p≡19 mod24`, else 0 (modulo L1). | 34/34 + 103/103 |
| M12 | `⟨σ,χ₂⟩_FIELD=0 ⟺ p≢3 mod8`: `p≡7 mod8` **35/35 unforced** (22 in + 13 out-of-sample). | 35/35 |
| M14 | Joint `(x,y)` aligned readout reaches **0.93–0.96** — but the magnitude control gives the same fidelity for a random target (does NOT separate character from random). Even/odd constraint is the exact part. | 4 primes |
| M17 | `A_new`'s internal DLP easy: MOV embedding degree `k=ord_ℓ(p)=3` at every tested supersingular prime. | 7 primes |
| M18 | D1 lift `Q(P)=[P⁺−P⁻]` carries no affine structure: `0/666` additivity; lands on high-order elements. | 3 primes |
| M19/M20 | Coordinate-bit and μ₆-isotype-pure cheap readouts at the matched floor (`φ≈0.1–0.5`; bit `z∈[−1.05,2.34]`). | 54 cells / 1 curve |
| A2.1 | `m=b₂/p` names all four `A_new` Frobenius eigenvalues (`z⁴+mz²+1=0`); law `H1: p≡11 mod12⇒m=2` (42/42), `H2: p≡7 mod12` split by cubic residue (36/36). **`m=1` at secp** ([CONDITIONAL] → [PROVED] *pending* the offered in-file grade moves + the three Katre caveats, B1.5). | 26 primes OOS |
| A2.3 | Joint `(x,y)` symmetry group **exactly** `{parity ℤ/2}×{GLV μ₆}`; magnitude indistinguishable from a random target in **both** norms (sup and `l²`, the M14 control); 6-cell budget equipartitioned. | `p≤823` |
| A2.4 | Per-harmonic profile is **Rayleigh at `N_eff/|S|→π/4=0.7854`**; no active/starved split in the `(b,c)` basis. | 7 primes |
| A2.5 | Sub-Rayleigh deficit real (survives value-multiset control, `Z=−13.99` pooled), carried by the **low tail** (~8% near-zero excess). ⚠ the later "b=0 axis locus" refinement is **RETRACTED** (wrong null, R-post); the **diffuse aggregate ~−0.1%** survives, no locus. | 7 primes |
| A2.6 | N1: parity **refuted** as cause (both `p mod4` classes ≈½); bulk 4th moment structurally **blind**; anomaly **localized to the extremal tail** of `|V(a)|/√p`. | 10 primes |
| A2.7 | λ₃-eigenvector anomaly **dissolves**: individual vector is gauge; subspace shows no covariant excess (⅔ trivial fraction), FIELD/lattice. | `p≤3571` |
| B2.2 | The `a≠0` twisted eigenvalues are **NON-ABELIAN** (splitting field not Galois) ⇒ the `ζ₃` is **GEOMETRIC** (GL(2)/monodromy, not GL(1)/Hecke). Redirects the route (L-mono), untouched B1.1. | `p=43,67` |
| B2.3 | `V(a)` = `A_new`'s Frobenius trace twisted by the Lang torsor; absolute rigidity destroyed, **relative** survives; `2√p` cap = value of the relative rigidity; **`½ = 2/4`** accounts for M3's anomaly. | structural |
| B3.1 | 4th-moment monodromy: `E[u⁴]` consistent with full **SU(2)**, **excludes** the `3/8` (torus/CM) reduction. | 12 primes OOS |
| B3.2 | μ₃-invariance is CM-specific (`j=0` 100% μ₃-trivial energy; `j≠0` ≈⅓) — the twist-orbit nulls sit on a real CM property. | (C-JZERO) |
| B3.3 | Row-budget: a `char−MN−μ₆` layer **exists** (`Z=+70.5`); plus a reproducible ~1.55× instrument over-dispersion. §XI.17 still open. | seen-data |
| B3.4 | Cubic difference-set energy `E3` on the **real 82 keys**: pre-registered reject (`p≈0.033`, `+75` in class `β²`), reproduced vs a generator-agnostic control, but **DIFFUSE** (no locus) and 1-of-7 statistics. **Interpretation OPEN.** | n=82, secp P |

## A.3 Not established  *(open — not closed)*

| # | item | status |
|---|---|---|
| N1 | Mechanism of the ½ saturation. | **Major advance**: `½=2/4` (B2.3), `v=u²−¾` and 120° exact (B1.1/B1.2); candidate = geometric monodromy μ₃ (B2.2). **Open on uniformity** (frontier #26). |
| N2 | `A_new` supersingular at secp. | **DISCHARGED** — proved (A1.1). |
| N3 | Numerical discriminator for the CM layer L3. | Open — two designed tests failed; a real test targets the CM type. |
| N4 | Cover transfer into `Jac(C)` (Route 3). | Open — `Õ(p^{4/3})` is best-known on one cover, not a family bound. |
| N5 | Growing-degree corner of the char-sum bounds. | `[GAP]` — no reduction for general poly-time readouts. |
| N6 | Everything measured is at `p ≤ ~10⁵`. | The banner — no power at `2²⁵⁶`. |

---

# PART B — THE PROVED STRUCTURE, EXPANDED  *(with spec-only replication blocks)*

Each **Replicate** block gives the script, the algorithm in prose, the exact parameters, and the numeric
table it produces. No source is inlined (by request); the algorithm + parameters are sufficient to
re-implement. All signal-path arithmetic is exact.

## B.1 The cover, the supersingular surface `A_new`, and the CM tower  *(P3–P5, A1.1, M17, B2.2)*

The DLP-relevant multiplicative sum `V(a) = Σ_P χ₂(y_P) e_n(a·d)` does **not** live on `E`. It lives on
the cover `C : w⁴ = x³ + 7` (`w²=y`), genus 3, with `Jac(C) ~ E × A_new`, `A_new` an abelian surface
(`dim 2`). The automorphisms of `C` put `Q(i)` (via `ζ₄`, any cubic) and `Q(ζ₁₂)` (via `ζ₃`, `x³+B` only)
into `End⁰(A_new)`.

**A1.1 — `A_new` is supersingular at every `p≡3 mod4`, including secp `[PROVED — scale-free]`.** The μ₄
argument: `ζ₄:(x,w)↦(x,iw)` acts on `H¹_new` with eigenvalues `±i`; at `p≡3 mod4`, `σ(i)=i^p=−i`, so the
Frobenius-twist relation `π·ζ₄·π⁻¹ = ζ₄⁻¹` is **non-commutative**, which is incompatible with every
non-supersingular `p`-rank stratum ⇒ `p`-rank 0. Inputs are `p≡3 mod4` and `ζ₄∈Aut(C)` only — no CM,
no `j=0`, no measured input ⇒ **valid at `2²⁵⁶−2³²−977`.** This discharges N2, so P13 (`Hom(E,A_new)=0`
at secp, via Tate) is now unconditional. Remaining diligence: an independent adversarial re-derivation of
the two standard external inputs (Frobenius-twist relation; surface `p`-rank/`End⁰` dichotomy) is
outstanding.
> **Replicate:** `supersingular_mu4_mechanism_v1.py`. Algorithm: for each `p` and cubic `f`, build
> `A_new` char-poly `L_new(T)=1+b₁T+b₂pT²+…`; check **Fact 1** `b₁=−tr(π|A_new)=0` and **Fact 2**
> `b₂=m·p` with every Frobenius root `√p·(root of unity)`. Params: 6 cubics (`x³+7,x³+2,x³+11` CM;
> `x³+2x+5,x³+x+1,x³−x+3` non-CM) × 42 primes `13→199`. Figure: **42/42** supersingular at `p≡3 mod4`,
> ordinary at `p≡1 mod4`, curve-independently (the tell it is the μ₄ cover, not CM). Independent 8/8
> point-count control: `p=29,53` have `b₁=0` yet are ordinary ⇒ trace-zero necessary, not sufficient.

**M17 — `A_new`'s internal DLP is easy.** Supersingular ⇒ `H¹_new` Frobenius eigenvalues are exactly
`√p·ζ` (roots of unity), and MOV embedding degree `k=ord_ℓ(p)=3` at every tested supersingular prime.
A supersingular, easy-DLP surface sits in the Jacobian of a degree-4 cover of `E`. But Route 2 is
blocked: `Hom(E,A_new)=0` (P13), so the cover transfer carries the DLP into the `E`-component while
`A_new` receives nothing (Route 3 open — N4).
> **Replicate:** eigenvalue readout at the 7 supersingular primes `p=31,43,67,79,103,127,139`; read `ζ`'s
> order off the untwisted char-poly. Figure: `k=3` at 7/7.

**B2.2 — the `a≠0` twisted eigenvalues are non-abelian ⇒ the `ζ₃` is geometric `[VERIFIED — p=43,67]`.**
The individual `a≠0` Frobenius eigenvalues of `H¹_c(E, L_{χ₂(y)}⊗L_{χ_a})` have a splitting field that is
**not Galois over ℚ** (Kronecker–Weber: `σ(D)/D ∉ (K*)²` at a generator) ⇒ they are not cyclotomic, not
Jacobi/Gauss sums, so classical Stickelberger does **not** factorize them. They are **GL(2)/big-monodromy
type**, not GL(1)/Hecke — the signature of a non-degenerate 4-dim deformation whose `a=0` fiber is the CM
degenerate case `√p·μ₁₂`. The `α₂/α₁=ζ₃` ratio is cyclotomic even though the eigenvalues are not ⇒ the
120° law is a **monodromy/geometric** fact, which is why every eigenvalue-arithmetic (Stickelberger)
attempt aimed at the wrong object. Refuting the mechanism did not touch the proved per-cell fact (B1.1).
> **Replicate:** `RESULT_anew_twisted_eigenvalues_nonabelian_v1.md` (Sage, exact number field). Compute
> the `a≠0` eigenvalue splitting field at `p=43,67`; test the Kronecker–Weber Galois criterion; plants
> classified correctly in each field. (`p=13`/`n=7` is a small-case exception.)

## B.2 The lift geometry: rhombus, Cap Law, CM spine, frame operator  *(P11, P12, M10)*

`eis(x)` maps `F_p ≅ ℤ[ω]/(π_p)` to its representative in the 60° rhombus `P={uR₁+vR₂:u,v∈[−½,½)}`
(reduced basis `R₁,R₂`, both norm exactly `p`). Norm `N(z)=u²−uv+v²`, `s=N(eis x)/p ∈ [0,¾]`.
- **Cap Law (P11) `[PROVED — continuum]`:** the flap is geometrically forced, `ε(x)≠0 ⟺ |u−v|>½`; core/flap
  densities `¾:⅛:⅛`. `σ(x)=sign(u−v)` on the flap else 0; μ₃-invariant, μ₂-odd.
- **CM spine (P12):** `eis(βX)=ζ·eis(X)+c`, `c∈{0,+R,−R}` in exact densities `¾:⅛:⅛`; the `±R` flap (¼)
  is the sole norm-change; `ε∈{0,+,−}` is a μ₃-orbit invariant ⊥ χ₆.
- **Frame operator (M10):** `C=Σ_x eis(x)eis(x)ᵀ` has `λ_max/Tr` **exactly ½ on the μ₃-core** (a
  120°-symmetric point set is isotropic) and **¾ on the full lift**; `¾−½=¼` = the flap fraction, so all
  anisotropy is a flap phenomenon weighted exactly ¼.
> **Replicate:** `lift_sextant_rhombus_law_proof_v2.py`, `cap_law_proofs_v1.md`, `int1_frame_operator_v1.py`.
> Algorithm: build `eis`, `ε` by exact `(u,v)`; verify `|u−v|>½ ⟺ ε≠0` pointwise; compute `C` by exact
> integer sums `S_uu,S_uv,S_vv`. ⚠ the `int1_frame_operator_v1.build` β-calibration has a bug at `p=823`
> (single hardcoded probe `x=12345=3·5·823` degenerates); use `isotypic_selection_rule_v1.py`'s
> many-probe version. Figure: `flap/(p−1)→¼`; `λ_max/Tr = ½` (core), `¾` (full), θ-independent.
> **Full-scale check:** Cap Law verified `flap⟺2|A₁+sA₂|>|DET|` = `ε≠0` on **99666/99666** points at
> `p=100003`, and the ARM-0 gate passed on **secp itself** (μ₆ exceptions 0/65536, flap density in band).
> *Unforced content:* the basis-orientation constant `s∈{±1}` is calibrated per prime = 1 bit; the
> unforced agreement is `(p−1)−1` bits.

## B.3 The selection rules — Claim S and Claim F  *(P8, P9, P10)*

One rule, not five walls. A list of exact zeros (`σ⊥s_y`, GLV zeros, `eis_p/eis_n` cross-energy zeros,
"± flap counts equal", the linear x-lift→scalar channel) is **one μ₆ selection rule** (Claim S) plus a
strictly stronger **field-level rule** (Claim F). A selection rule is two-sided: it says which channels
must vanish and therefore which are *permitted* to be nonzero — the permitted-but-vanishing entries are
the live objects. **The FIELD/CURVE split is mandatory on every `j=0` entry** — reporting the total as
one number attributes a lattice fact to curve arithmetic (the central proxy guard).
> **Replicate:** `isotypic_selection_rule_v1.py`, `_field_bigrading_v1.py`. Algorithm: assign each readout
> a curve bidegree `(j,k)∈ℤ/2×ℤ/3` from `F([−1]P),F([λ]P)` and a field bidegree `(i,k)` from `F(−x),F(βx)`;
> pair and sum. Figure: Claim S verified `p=547` (54 cross-bidegree pairs, 0 violations, direct sum);
> Claim F `p=127→1249`, 16 primes: **(F1) 336/336, (F2) 180/180, 0 violations**. Of 240 non-forced FIELD
> pairs, 72 vanish (56 = ordinary `F_p*` orthogonality; 16 = the class-L×class-M cross-pairs = the one
> live σ×χ₂ object).

## B.4 The character-sum bounds — what is provably flat, and its exact scope  *(P6a, P6b, P15)*

- **Additive (P6a) `[PROVED|WD]=[PROVED|KS]`:** `|U(a,b,c)| ≤ 4√p+1`, uniform in `(b,c)`, no polylog, no
  exceptional `(b,c)`. For `F=ψ∘f`, `ψ` additive, `deg f≤D`: `|Corr_F(a)| ≤ 2D√p/n` (Kohel–Shparlinski
  Thm 1 + eq 3, SHA-256 `645d9022…`).
- **Multiplicative (P6b) `[PROVED|WD]`:** `|Σχ₂(x)e_n(ad)| ≤ 2√p`, `|Σχ₂(y)e_n(ad)| ≤ 4√p` from the same
  cohomology with a **Kummer** sheaf (`#R·√p`, `#R=2` for `x`, `4` for `y`). **KS does NOT bound χ₂** (its
  ψ is additive, via Artin–Schreier); do not attribute this to KS. Derived in `weil_deligne_character_bound_v1.md` §6′.
- **Reduction (P15):** concentration `C(F)=Ω(1) ⟺ F` correlates `Ω(‖F‖₂)` with a character `e_n(a₀d)`.
- **Consequence, stated at altitude:** every **bounded-degree** cheap readout (additive or χ₂) is
  spectrally flat (a `√p` floor) at the tested scales. `[GAP]` (N5): for general poly-time
  (non-bounded-degree) readouts there is **no reduction in hand**; the only `C=1` readout known is the
  discrete log itself, not bounded-degree. *"No concentration ⟺ ECDLP hard" is WITHDRAWN — the `⟹` has no
  reduction.*
> **Replicate:** `weil_deligne_bound_verify_v1.py`, `t_y_maxbound_v1.py`, `structured_pair_bilinear_v1.py`.
> Figure: `max|U|/√p ≤ 4` at all tested `p`; the best cheap readout `e_p(xy)` (deg 5) has aligned-phase
> `C/floor ≈ 1.3`; structured pairs `v=k·u` collapse to a single bounded-degree readout, `C_k` at the
> floor for `k∈{2..64}` (fixed `k`; `k` growing with `p` not covered).

## B.5 The N1 / 120° cluster — the ½ saturation resolved to relative rigidity  *(B1.1–B1.4, B2.3, M3)*

The measured anomaly (M3): `χ₂(y)`, dim 4, saturates
**0.470→½** of its Weil ceiling `4√p` while same-dimension additive `bx+cy` saturates 0.876.

- **B1.2 — one exact identity generates it.** `V₂=V₁²+2p` (SIN, `p≡3 mod4`, secp's stratum) / `V₁²−2p`
  (COS), an integer-vector identity in `ℤ[x]/Φ_n` (every non-constant component exactly 0). ⇒ `v=u²−¾`
  exactly (357/357 classes, dev `1.4×10⁻⁶⁰`) = the **Eisenstein norm form** `s₁²+s₁s₂+s₂²=¾`; solving,
  `u=cos t`, `s₁=cos(t−60°)`, `s₂=cos(t+60°)` — the two Frobenius half-angles differ by exactly 120°.
  Forced bounds nobody had stated: `v∈[−¾,+¼]`, **`max_a v ≤ ¼` unconditional**.
- **B1.1 — the 120° law is an exact identity.** `α₂/α₁=ζ₃` at every cell of **22 primes** (7 in-sample,
  **10 out-of-sample in secp's class `p≡7 mod12`**, 2464 cells; 5 cross-stratum) — upgraded from
  `[VERIFIED 9.5×10⁻⁴⁰]` to exact.
- **B2.3 — the mechanism.** `V(a)` = `A_new`'s Frobenius trace **twisted by the Lang torsor**
  (`{V(a)}` = the orbit of `H¹(A_new)` under the twist group `E(F_p)^≅ℤ/n`). Absolute rigidity is
  destroyed (each `α`'s absolute angle goes free, Sato–Tate); **relative** rigidity survives (the ratio of
  the two `±`-pairs is a root of unity — the 120° law); the `2√p` cap is the arithmetic value of the
  relative rigidity. This accounts for `½=2/4`: `bx+cy` has 4 free eigenvalues, `χ₂(y)` has 2 free
  ×`{1,ζ₃}`.
- **B1.3/B1.4 — the open inequality, retyped.** `S_y≤2` reduces to the **sign of one L-poly coefficient**
  (`v≤0 ⟺ e₂≥−2p`), equivalently `|V₁(a)|≤√3·√p` — a **sub-Weil bound** (86.6% of Weil; largest observed
  `1.932√p@p=547`). The `v≤0` route is **dead** (exact counterexamples `p=127,163,211`, `v>0` at ~4–6% of
  classes) **but the inequality is NOT refuted** (`v≤0` was sufficient, not necessary).
> **Replicate:** `n1_vsign_mechanism_v1.py` (integer-vector `V₂=V₁²±2p`, `v=u²−¾`, 8–10 primes);
> `RESULT_n1_120deg_exact_v1.md` executing `PREREG_n1_120deg_exact_ideal_v4.md` (statistic
> `g=deg gcd(L*(T),L*(ζ₃T))`, no-float multi-modular, freeze SHA `a964f246…`, 22 primes; PLANT-B/U1
> negatives → `g=0`); `n1_vsign_decide_v1.py`/`_exhibit_v1.py` (exact rational counterexamples, three
> independent count implementations + the forced identity `e₃=χ₂(−1)·p·e₁`). Figure: the m/eigenvalue
> table below.

**The `m`-law (A2.1, now scale-reachable via B1.5).** At `p≡3 mod4`, `char(t)=t⁴+m·p·t²+p²`, and the
integer `m=b₂/p ∈{−2,−1,0,1,2}` names all four eigenvalues via `z⁴+mz²+1=0`:

| `m` | eigenvalues (`√p·`) | angles (units π) | root order | `π^k` scalar |
|---|---|---|---|---|
| −2 | `{1,1,−1,−1}` | 0,0,1,1 | 1,2 | `π²=+p` |
| −1 | primitive **12th** | ±1/6,±5/6 | 12 | `π⁶=−p³` |
| 0 | primitive 8th | ±1/4,±3/4 | 8 | `π⁴=−p²` |
| **1** | `{ω,ω²,−ω,−ω²}` = prim **3rd/6th** | ±1/3,±2/3 | 3,6 | `π⁶=+p³` |
| 2 | `{i,i,−i,−i}` | ±1/2 | 4 | `π²=−p` |

**At secp: `m=1`** (`7^{(p−1)/3}≢1` ⇒ `B=7` a cubic non-residue), eigenvalues `√p·{ω,ω²,ζ₆,ζ₆⁵}`.
`[CONDITIONAL]` in A2.1; **B1.5 (below) proves the sign law it hung on**, moving `m=1` at secp toward
`[PROVED]` once the offered in-file grade moves are applied.

**B1.5 — the Jacobi sign law `[PROVED — modulo (D2); (D2) discharged]`.** `J(χ₃,χ₄)=−p` if `p≡1 mod3`
(`p≡7 mod12`, secp's class), `+p` if `p≡2 mod3`. Route: Stickelberger ⇒ `(J)=(p)` (kills the `π²`
competitor, which Frobenius could not — it constrains the field, `π²` differs in the **ideal**) →
Kronecker ⇒ `J=ζp`, `ζ∈μ₁₂` → mod the prime over 2 forces the μ₃ part trivial (rationality) → mod the
prime over 3 fixes the sign.
> **Replicate:** `RESULT_jacobi_sign_law_stickelberger_v1.md` (spec `VERIFY_SPEC_...` frozen pre-run;
> exact `ℤ[ζ₁₂]` 4-vectors, no float). Params: 28 primes × 4 char pairs (info unit = 28, the pairs are
> Galois conjugates), 4807 primes for the digit lemmas. Figure: all 5 firing controls fire (FC5 rejects a
> planted `π²`; FC4 reproduces the classical cubic `(0,1)`); at secp `J=−p`, profile `(1,1,1,1)`.
> ⚠ Novelty doubted, not claimed (semiprimitive/uniform-cyclotomy is classical); the three Katre caveats
> (§B2.1) travel with any promotion.

## B.6 Amicability  *(A1.2)*

`(p, N_ord)` is an aliquot 2-cycle for `y²=x³+7`: `#E(F_p)=N_ord` and `#E(F_{N_ord})=p`, exact at the
256-bit primes. `t_N=2−t_p=x−3y` is one of `N`'s six sextic-twist traces `{±2x,±(x+3y),±(x−3y)}` ⇒ `p`
is an admissible `#E(F_N)` a priori; the **unforced** part is the twist selection (the curve landed on the
`x−3y` twist). Enforcing group = `CM(ℤ[ω]) ×` the sextic-twist class of `b=7`. Calibrated magnitude: this
CM family's amicable density ≈ 13/50 ≈ 26% (Silverman–Stange Conj. 40). **No d-side / private-key / ECDLP
content.** The non-homomorphic correspondence `π_n=π_p−1` remains UNANALYZED (frontier §XI.3).
> **Replicate:** `RESULT_secp_amicable_pair_v1.md`. Algorithm: reduce `E` mod `N_ord`, test `p·P=O` for 3
> independent `P∈E(F_{N_ord})` (`p` prime ⇒ forces the order). Discriminating control: the alt twist
> `N+1−2x` does **not** annihilate. All exact integers, full scale.

## B.7 The d-side geometry: `(n,k,D)`, the Dirichlet reciprocal lattice, the bit-ladder  *(A1.4, A1.5, A2.8, A2.9)*

Pure d-side objects — **no leakage or ECDLP claim**; exact integers; `check_no_float` passes.
- **A1.5** — the `T=1` (one-D-term) stratum is exactly the Dirichlet reciprocal-floor set
  `{base ± ⌊lo/q⌋ : q≥1}` (`lo=2^{N−1}`); the merge/island boundary is exactly `√lo=2^{(N−1)/2}` (`[1,√lo]`
  is one solid continent, above it isolated singletons). Verified as identical sets vs direct `d_terms`
  enumeration.
- **A2.9** — exactly 3 complexity levels `T∈{0,1,2}` (to width `7·10⁵`); the `T=1` sub-surface **shatters**
  into tens of thousands of components (the non-trivial topology the full domain lacks). Clustering is
  arithmetic-structured (matched-permutation control, real/ctrl `0.46–0.68 < 1`); mechanism = the block
  `[1,√lo]` collapsing to one component; **the guessed 2-adic mechanism is refuted** — an odd prime
  `L≈1.33·lo` gives the same shape (generic in `L`).
- **A2.8** — the `(n,k,D)` validity domain is a **contractible Farey solid** (`χ=1,β₀=1,β₁=0` at `Q≤256`),
  realized at unit resolution as a **1-D coprimality net** (no unit square is fully coprime ⇒ no 2-cell).
  The net is more connected and ~3× more cyclic than a density-matched random set (matched control). The
  domain's symmetry is `k↦n−k` (`ℤ/2`) — **μ₆ is not on this object** (it lives on the `(X,Y)` image,
  across the ECDLP bijection).
- **A1.4** — the `Aut(E)`-orbit bit-ladder tops out at `log₂6≈2.585` bits (constant, n prime ⇒ no proper
  subgroups). Conversion convention: a quotient dividing the *search space* by `k` divides a
  *square-root-time* runtime by `√k` (do not apply a space factor to a runtime).
> **Replicate:** `nkd_dterms_mechanism_v1.py`, `nkd_topology_v1.py` (Farey tessellation + `β₀,β₁` via union-
> find/cycle count), `orbit_bit_ladder`/`d1_bitmap.py`. Params: `N∈{26,28,30}`, fibers `4·10⁴–7·10⁵`,
> `Q∈{32,64,128,256}`; matched permutation/density controls, 8–20 seeds. Figure: `N=28(2,1)` → 22150
> `T=1` points = 22150 reciprocal-floors; component counts 17157/8579/10565; Farey-256 vertex count
> 19949 = saturated realized-label count at `N=18`.

---

## B.8 Further carried facts  *(secondary graded rows, kept complete per the compile rule)*

- **Theorem B (two-point bilinear) `[PROVED]`.** The two-point sum over independent `(u,v)` has
  `|S|/n² = O(p^{−1/2})` (`bilinear_closure_proof_v1.md`) — the joint-SET bilinear bound of which the
  diagonal `v=k·u` slice (B.4) is the fixed-`k` special case.
- **Semaev / index-calculus (Part VIII) `[VERIFIED unless noted]`.** `S₃` irreducible over ℚ (the `2·7`
  term is correct — do not "fix" it, retraction 22); `C_t` smooth genus-1 for every `t` (P14); the `S₄`
  singular-fibre locus is the diagonal `xᵢ=xⱼ`, identically for secp/non-CM/j=1728 (zero `t`-ideal); the
  isobaric leading-form fact `[PROVED, all m]` (`S₃` wt 4, `S₄` wt 12, leading forms free of `A,B`), but
  "isobaric ⇒ first-fall curve-independent" is only `[HEURISTIC+CITED]` (retraction 8); `x·y` gives
  `w²=x⁵+B·x²` (x-degree 5, **higher** — cannot lower the degree); `Δ(t)=−86704128(t³+7)⁴` is
  `[UNREPRODUCED]` (roots reproduce, constant/exponent do not) — not relied on downstream.
- **σ×χ₂ sub-facts (Part X) `[VERIFIED]`.** Sub-law **H1**: `ORB=flap/6` even ⟺ `p≡7 mod8` (64/64, a
  Cap-Law lattice fact); the enforcing symmetry lives **outside `F_p`** — in `ℚ(√−p,√−3)` (the reflection
  `z→ζ₆ᵏz̄` does not descend to the prime field); the multiplicative sign-flip mechanism is **ruled out**
  (no `c∈F_p*` with `σχ₂(cx)=−σχ₂(x)`, exhaustive at `p=127,823,967,991`). **M13:**
  `(B2)=Σ_{P≠O}σ(x_P)=C` exactly (49/49), `C²/p ≤ ~3.7`, consistent with `|C| ≤ ‖σ‖_W·2√p`.
- **Character-sum identities (Part VI) `[PROVED]`.** `Σ_b|T(a,b)|²=p(n−2)`; Parseval
  `Σ_a|Corr_F|²=‖F‖₂²`; aligned `Corr(a₀)=√(πn)/2`; single-coordinate covariance
  `|Cov_d(F(x_d),g(d))| ≤ (max|T|/n)‖F‖_A‖g‖_A` ⇒ (given KS) `O(p^{−1/2+o(1)})`, MI `O(p^{−1+o(1)})`.

---

# PART C — THE MEASURED JOINT OBJECT AND ITS EXACT FENCES  *(with replication)*

## C.1 The joint `(x,y)` shadow — real structure, and an exact characterization  *(M14, A2.3, A2.4)*

`xy = x·y` is odd-in-`d` + μ₃-weight-1 — the symmetry type the odd half of the `d`-spectrum needs and `x`
alone cannot see. The joint aligned readout `F̂=U/|U|` reaches **`ρ_inf = 0.93–0.96`** (x-only 0.29–0.36),
reproduced by two independent implementations. **But** (M14, strengthened in A2.3) the magnitude control —
the same phase-only reconstruction applied to the leaking character and to a random target — gives the
**same fidelity in both norms** (`ρ_inf` 0.9534 vs 0.9567; `ρ₂` 0.9996 vs 0.9997). So the 0.93 is the
coordinate geometry's phase-only reconstruction quality, not a character discriminator. What is exact and
survives: the symmetry group is **exactly `{parity ℤ/2}×{GLV μ₆}`** (`U(−a,b,c)=U(a,b,−c)`,
`U(a,b,c)=U(aλ,βb,c)`, phase-rigid to std 0.000); the 6-cell budget is equipartitioned; and those two
symmetries **are** M16's barrier (μ₆-symmetric ⇒ constant on `{±d,±λd,±λ²d}`).
> **Replicate:** `joint_shadow_decompose_v1.py`, `joint_map.py`, `recon_sup.py`. Params: `p=163…823`,
> aligned `F̂=conj(U)/|U|`. Figure: the char/random fidelity table (both norms equal); planted perfect
> character pins `ρ_inf=0.997`.

## C.2 The harmonic profile is Rayleigh; the sub-Rayleigh deficit is diffuse  *(A2.4, A2.5)*

**A2.4** — is the alignment carried by a few active harmonics? No: `N_eff/|S| = 0.7805→0.7839` converging
to **`π/4=0.785398`** — the exact Rayleigh value. The profile is Rayleigh (complex-Gaussian coefficients);
the top 1% of harmonics carry 2.7% (the diffuse floor). The l² budget `Σ_{b,c}|U|²=p²(n−1)` (A1.7) is
pinned and **identical for the character and for a random target**, so *that statistic* cannot separate
them — but a pinned 2nd moment does **not** forbid unitary concentration (a unitary map redistributes a
fixed total into fewer modes), so the no-concentration evidence here is the **measured** Rayleigh profile
`[EMPIRICAL — 7 primes, p≤2089]`, not the conservation. Untested/outside: **non-unitary/oblique**
transforms, bases other than `(b,c)` Fourier, higher-degree readouts, `p>2089`.

**A2.5** — the character's harmonics are on average slightly **smaller** than random (a `0.06–0.10%`
sub-Rayleigh deficit, `Z=−13.99` pooled, sign 7/7), surviving the exact value-multiset control (MC2),
carried by the **low tail** (~8% excess of near-zero harmonics). The pre-committed fourth-moment mechanism
was **refuted by its own threshold** (`r⁴≈0` for `r<0.1` ⇒ M4 is blind to a low-tail effect). ⚠ **The
later "b=0 (pure-y) axis localization" refinement is RETRACTED** — a wrong-null artifact: the random
unit-phase null omitted the character's forced Hermitian symmetry `g(n−d)=conj(g(d))`, and the mismatch
concentrated on the ±-symmetric axis manufactured the −10..−13% locus; under a symmetry-matched null the
on-axis deficit collapses to −0.1..−3.8%. **The AGGREGATE ~−0.1% deficit survives the matched null but is
DIFFUSE — there is no locus.** (Prior memory had already flagged this; plant/floor/replication controls
all fired but shared the same wrong null.)
> **Replicate:** `RESULT_harmonic_support_pattern_v1.md`, `RESULT_subrayleigh_deficit_locus_v1.md`;
> matched-null checks `_axis_null_check_v1.py`, `_aggregate_null_check_v1.py`. **Lesson (binding): a null
> must carry the object's forced symmetries, not just its marginal.**

## C.3 N1 as an extremal-tail phenomenon  *(A2.6)*

Parity as cause is **refuted** (both `p mod4` classes ≈½ at 10 primes). The bulk 4th moment is
structurally **blind** ("dim 4" is a Weil bound on `max|V(a)|`, not a DFT-support statement — the
dimension lives in `O(1)` of `n` frequencies contributing `O(n)` against a bulk `O(n²)`; the whole class
is disqualified a priori). Max **separates** the readouts (0.470 vs 0.876), so they are not noise — and
**the entire difference lives in the extremal tail** of `|V(a)|/√p`. Candidate mechanism (B2.3): the
`[−1]`-involution 2+2 parity split; a definite-parity `y`-readout couples to only its own 2-dim half.
> **Replicate:** `n1_P1_calibrator_gate_v1.sage` (the run-blocking gate that caught the bulk-moment
> blindness before it produced a false answer; positive control gives a ~150× margin at true rank 1/2).

## C.4 `C_T` tensor structure and the substrate  *(M7, M10)*

`C_T = C₁⊗C₁` (`(¾:⅛:⅛)⊗(¾:⅛:⅛)`), with a doubly-degenerate `⅓`; at `p=100003` the degenerate block
splits into exact swap-even and swap-odd channels (block trace 7.5e-5 from `2/3`). Inter-coordinate
coupling is a **bounded magnitude `< ~1.6%`** (Frobenius-norm estimator, `n≈1.3×10⁵`; the 2–3% residual is
reproduced by a zero-coupling surrogate, pooled G² p=0.40 — an **empirical** refutation, not analytical).
Substrate: secp sits at criticality (`|π|=√p`), `|T|²`~Porter–Thomas (thermal, no scar), transfer
spectrum mixes beyond μ₆ (`|λ₂|~1/√n`).
> **Replicate:** `ct_tensor_structure_v1.py`, `_anomaly_drill_ct_split_v2.py`, `ct_coupling_universality_v3.py`.
> Params: 8 curves `p≤2¹⁷`, `b=7`. Figure: `ε̂≤0.025`, `z_G²∈[−1.17,+4.46]`. Next: `‖D_odd‖_F` at
> `n~10⁶–10⁷`.

## C.5 The twist-orbit monodromy programme  *(B1.7, B3.1, B3.2, B4.1, B4.2)*

Testing whether `a↦V(a)` is structured beyond its forced μ₃+odd symmetry. **B1.7:** Arm II dissolves to the
exact curve-independent frame identity `⟨f_a,f_b⟩=nI−J`, locating the signal in the **values** `V(a)`, not
the frame; 2nd/3rd-order objects are forced (additive autocorr `n(nδ_b−1)`; multiplicative bispectrum `≡0`
by odd parity). The one free 2nd-order object, magnitude `|V(a)|²`, is **null** (B4.2, 12 primes,
min p=0.05, PLANT fires 4.9–10.9×); the single-character spectrum is **null** (B4.1). **B3.1:**
`E[u⁴]` (`u=V/2i√p`, exact rational) is consistent with full **SU(2)** and **excludes the 3/8 torus/CM
reduction** (12 primes OOS, pooled dev +0.00008) — the twist frees the absolute angle toward Sato–Tate
while the relative 120° stays frozen. Cross-check strengthening both nulls: the signed-low prime (2251) ≠
the magnitude-low prime (2647) ⇒ independent noise. **B3.2:** μ₃-invariance is CM-specific (`j=0` 100%
μ₃-trivial energy) ⇒ these nulls sit on a real CM property, not a class-machinery artifact.
> **Replicate:** `RESULT_twist_orbit_{spectrum,forced_landscape,magnitude,monodromy}_v1.md` (preregs
> `experiment-designer`-signed, freeze SHA `7cde99fe…`). ⚠ v1 prereg carried a symmetry bug (`V` is odd
> μ₃, not μ₆) the gate caught — fixed in v2. **Scope:** through 2nd/3rd/4th order, **no curve-specific
> structure detected beyond the forced CM symmetry** — a where-it-cannot-be map, NOT "maximally generic".
> Untested (could still hold structure): joint/coupled objects, short-scalar/incomplete sums, higher
> moments, larger `p`.

---

# PART D — THE LEAKAGE FRONTIER: WHAT IS BOUNDED, WHAT IS OPEN

**Framing (counter-prior).** The security-relevant question is **computational** — is there a feasible
algorithm whose distinguishing or key-recovery advantage beats generic (`~2^{n/2}`)? — but that does **not**
retire the **statistical** (information-theoretic) channel: the ensemble the generator leaves is not the
ideal distribution, and whether a cheap statistic has advantage on it is open, and if it fires it is the
stronger (unconditional) result. Two facts fix the boundary and must be stated together:
1. **Single-instance secrecy is vacuous.** `H(k|P)=0` (bijectivity of `k↦kG`) — the key is *determined*,
   not *hidden*. This says nothing about *structure*; "determined ≠ structureless".
2. **A statistical null cannot certify computational security, and cannot certify a break** — it runs both
   ways. Every null below is scoped to its class of observable; none is a security statement.

**What the character-sum bounds actually close (a class-closure, provable).** P6a/P6b bound **every
distinguisher in the bounded-Wiener-norm / complete-character-sum class**: `|Σ_d g(d)χ(·)| ≤ #R·√p·‖g‖_A`.
That is an analytical **class-closure** (a bound over every distinguisher in that class), and the χ₂(y) case is halved by the cap
(factor 2, the `#R=4` contributing as 2): `|Σ_d g(d)χ₂(y_d)| ≤ 2√p·‖g‖_A`. The `y`-channel leakage
question **reduces to a Wiener-norm question on `ℤ/n`.**

**The specific high-correlation readout is DLP-cost.** The aligned `F̂(b)=conj(T(a₀,b))/|T(a₀,b)|` reaches
`Corr≈0.93` (joint), but building `F̂` needs `T`, hence all `x_d` — a DLP-cost object; and (M14) the
scalar-fidelity statistic does not separate that readout from a random target. The exact, control-surviving
part is the even/odd constraint. *(This is the precise content behind master v4's over-broad "leakage is
computational, not information-theoretic" header, restated.)*

**The algorithm classes the character-sum bounds do NOT cover — where computational leakage could live.** Complete character
sums say nothing about: **LLL / hidden-number-problem** (lives in the tail, not the mean), **index calculus
/ Semaev summation polynomials**, **short-scalar / incomplete sums** (`B≪√p`, no character-sum bound
applies). These are where computational leakage could live. Every statistic in the record is a
complete-orbit, mean-based object; the tail and the short-scalar corners are named and largely untouched.

**Doors with a specific checked reason** *(a list of what has been checked — not a completeness claim):*
additive-subgroup (prime order) · MOV on `E` (254-bit, verified not cited) · anomalous (`#E≠p`) ·
Weil-descent (prime field) · H² carry (control z=849) · `Hom(E,A_new)=0` (P13, unconditional). The
**Route 3** cover transfer (genus-3 index calculus `Õ(p^{4/3})` on one cover) stays OPEN — not a bound
over the cover family.

---

# PART E — LIVE FRONTIERS  *(reconciled across master §XI + Addendum-1 §A5 + Addendum-2 §B6; ranked by structural reach)*

**Top structural gap.**
- **#26 — Uniform `u=ζ₃`** (all `a`, all `p≡7 mod12` ⊇ secp) **via geometric monodromy.** The **sole
  remaining structural gap** of the cap-via-relative-rigidity programme. Per-cell is `[PROVED]` at 22
  primes (B1.1); no finite sweep gives uniformity. Target: identify the `μ₃` in the geometric monodromy
  group of `L_{χ₂(y)}⊗L_{χ_a}` on `H¹_c` forcing the between-pair ratio to a primitive cube root uniformly.
  Ingredient available: the ω-descent constrains the monodromy group. **L-Stick is retired for this**
  (B2.2, non-abelian `a≠0`); **L-mono is the primary route.**
- **#28 — the `a≠0` big-monodromy** — prove non-abelian for generic `p` (now `[VERIFIED p=43,67]`) and
  identify the group (GL(2)/big). The object #26 must analyze.
- **#27 — `S_y≤2` as an exact sign / sub-Weil bound** `|V₁(a)|≤√3·√p`. `v≤0` route dead; candidates: derive
  `v=u²−¾` from the μ₆ action (currently proved by verification, not derived); measure the exceptional
  `a`-set (located, not characterized); or tolerate `v≤¼`.

**The leakage-facing leads.**
- **#1 — a cheap *partial* of the joint `(x,y)` shadow** (the highest-value leakage lead). Bounded by M20
  (μ₆-isotype-pure, `φ≈0.1–0.5`), M14 (0.93 does not separate), M19 (bits at the matched floor), A2.4
  (Rayleigh, no active/starved split). **Still open, outside every test run:** higher-degree joint
  readouts; the `N_eff` multi-frequency channel at large `n`; **non-μ₆-covariant cheap readouts** (raw
  coordinate bits, one curve/one `n` only); multi-bit/multi-point joint; sub-floor `φ`; larger `p`.
  **Two explicit new exclusions:** non-unitary/oblique transforms; higher-degree (non-linear) readouts.
- **#29 — group-law joint difference-set objects on the real key set** (connects to the DLP through curve
  arithmetic, unlike an `x`-coordinate character sum): `P_i±P_j` via curve addition; the μ₃-graded cubic
  difference character `χ₃(x_j−x_k)` (secp's own CM/Eisenstein direction, the subspace `S_diff` is blind
  to — this is the E3 line, §B3.4, whose diffuse `β²` reject is OPEN); the σ-weighted difference sum;
  triple/multilinear objects. Each its own prereg.
- **#30 — higher-order/joint/larger-`p` twist-orbit** (short-scalar/incomplete sums, joint additive-
  multiplicative cross, higher moments).
- **#17 — the per-frequency conservation `Σ_a|U(a,b,c)|²=n(n−1)`** — the one exact constraint the random
  nulls do not satisfy; is the ~8% near-zero excess the shadow of this row-wise conservation?

**The arithmetic-completion frontiers.**
- **#16 / L1** — `(†) C′−C = Σχ₂(s)·sgn(ρs mod p−s) = 3·h(−p)` (verified 134 primes); the single open step
  of P2, which would move `|FLD|=6h` from `[EMPIRICAL]` to `[PROVED]`. Needs analytic class-number /
  generalized-Dedekind-sum machinery (elementary manipulation is provably circular).
- **§XI.3** — the non-homomorphic amicable correspondence `π_n=π_p−1` (ambient object now a verified fact,
  A1.2; correspondence UNANALYZED; protecting lift obstruction `[HEURISTIC]`).
- **§XI.9 — FLD-sign intrinsic-ness.** `sign(FLD)=−χ₂(M)` verified 54/54 but reduces to **none** of ~25
  tested intrinsic invariants; the magnitude `|FLD|=6h` is intrinsic, the **sign is unresolved**. (Only
  its *void* sub-check — the `π_p↔π̄_p` chirality probe — is `resolved-by RESULT_twist_gauge_covariance_v2`;
  **do not re-strike the frontier itself** — Master restored it via its own compile-diff: "voiding a
  decisive check is not closing the question it was meant to decide.")
- **#19 (Addendum 1)** — the **curve-side image of the `T=1` Dirichlet island lattice** beyond the tested
  families (A3.2/A3.3 are null for 4 energy statistics + 2 GLV detectors, `M=1024`): other Farey labels,
  larger `M`, higher-order joint statistics, and the d-side↔curve-side question across the now-verified
  amicable bridge (A1.2).
- **N3** (CM-type discriminator; also the M6 order-set `{1,3}`/`{3,4}` pattern needs a larger sample),
  **N4/Route 3** (cover family), **N5** (`[GAP]` growing-degree corner).
- **§XI.4 — first-fall / `S₄⁺` degree.** Open at `m≥5`, larger `p`, and non-Semaev index calculus;
  `bounded-by RESULT_semaev_cm_lever_v1` (secp = non-CM = j1728 on matched systems, `d_ff=12`, `p≤307`,
  `m≤4` — the one place a `j=0` CM lever could hide is curve-blind at the tested scale).

**Also live (lower stakes):** full-resolution `σ₁,σ₂` boundedness; is `ε` an arithmetic object?; the
`(n,k)`-net per-`n`-density null and *which* cycles carry the ~3× β₁ excess (Stern–Brocot depth?); the
ε carry-trajectory; the `T=2`/`T=3` strata past width `10⁷`; individual slow-mode eigenvector resolution
(needs `n~10⁵–10⁶`); μ₆-matched feature/target pairs at `n>5·10⁴`; a **`p mod 8` law** for `⟨σ,χ₃⟩` or
`⟨eps,χ₂⟩`; **deriving H1** (the `ORB` parity) from the Cap-Law continuum geometry; an **unconditional
Part-VI bound** (needs Weil–Deligne + KS reproved — a `[GAP]`); the **large-prime rank-10 μ₃ split**;
**cross-project** (finite-field zeta as an RH test-bench; the LRC↔μ₆/μ₂ shadow); the LBE diffuse-dependence arm
(ABSTAINED, needs more null draws not re-analysis).

---

# PART F — RETRACTION LEDGER  *(do NOT re-claim any of these; carried complete from master §XII 1–26 + Addendum-1 §A4 27–38 + Addendum-2 §B5 39–45 + post-Addendum 46)*

1. χ₂ "doubling transport law" → textbook duplication formula (CITED, not a finding).
2. Test-A cubic-moment "null" → zero statistical power (N=82).
3. G "tested the blind corner" → tested a proxy (`d mod k`, a known-null hardcore bit).
4. v11 amicable "wall" → strawman; only the group-homomorphism case was ruled out.
5. "‖F‖_A gap is the only analytic door" → wrong; Wiener norm is a red herring.
6. v17 "6–7σ soft shadow" → null-mismatch artifact (shuffle null destroyed the μ₆-invariance).
7. aligned-leak scaling `~1/√log p` → data drift over too small a `p`-range.
8. `[PROVED, general m]` first-fall curve-independence → `[HEURISTIC+CITED]`.
9. "no concentration ⟺ ECDLP hard" → withdrawn (`⟹` has no reduction in hand).
10. "KS bound covers χ₂" → withdrawn (KS's ψ is additive; χ₂ needs a Kummer argument).
11. "KS / Lange–Shparlinski pairing for the mixed sum" → KS alone carries it; do not re-pair.
12. "L1 needs analytic machinery / an honest wall" → withdrawn (difficulty verdict dressed as honesty).
13. "L1 elementary and reachable via first-moment" → withdrawn (built on two wrong formulas).
14. "± flap counts EXACTLY equal" → field-level conflation; the curve law is `(B2)=C ≠ 0` generally.
15. Bit-readout "ESCAPE" (5.8/5.3/7.9σ) → μ₂-symmetry null mismatch (`x_{−d}=x_d`); #6 recurring.
16. "`p≡7 mod12 ⇒ √p·ζ₆` = a CM fingerprint" → FALSE; the ζ₆ is geometric supersingularity (μ₄, any cubic).
17. "`√−3` in the splitting field = a CM detector" → FALSE (non-CM shows it); "splits over `Q(ζ₁₂)`" uninformative.
18. "non-CM splits over `Q(i)`" → FALSE, and the degree-2-on-dim-2 reasoning was wrong.
19. `int1_frame_operator_v1.build` β-calibration bug (single probe `x=12345=3·5·823` degenerates at p=823); secp unaffected.
20. σ×χ₂ tallies `64/64, 42/42, 20/20` → corrected to **35/35 unforced** (law survived, tally did not).
21. "`sign(FLD)·χ₂(M)` constant 792/792 ⇒ a lattice function" → 2 distinct configs = 99 forced bits.
22. "the `2·7` in `S₃` is a typo" → do NOT fix it (it is the `2B` slot, `B=7`; vanishes 1406/1406).
23. "μ₃-closing raises the solving degree" → retracted (a `p=211`-only proxy number).
24. **(standing)** residue-vs-component tautology: never correlate `r=v−w` against `w` (spurious MI z≈+5000 the shuffle control cannot expose).
25. "the `C_T` 2–3% split was refuted analytically" → overstated; the refutation is **empirical** (a fired surrogate).
26. Two dismissals-by-declaration (χ₂(y) "bound-irrelevant"; `A_new` "auxiliary"; "χ₂(y)'s 2√p is a max-artifact") — all withdrawn.
27. "`A_new` ss because `p` inert in `Q(i)`" → the **reason** withdrawn; the conclusion now has a proof (A1.1).
28. "`m=1` ⇒ `√p·{±ζ₁₂,±ζ₁₂⁵}`" → FALSE (those are `m=−1`; `m=1` = primitive 3rd/6th). Caught by root-order count, not reread.
29. "34/34 configurations confirm the Jacobi reduction" → 15 distinct (12 of 19 forced by the step under test).
30. "λ₃ eigenvector 60→85% μ₃-covariant" → gauge (drifts with K) + no covariant excess (a `16/15` null-mismatch).
31. D1 non-additivity mis-scoped both ways within one session; **M18 (3 primes, controls) stands**.
32. "the transfer map is public ⇒ any inversion is an ECDLP solver" → invalid (would "refute" MOV/Frey–Rück).
33. "DLP in `F_{p³}` at `2²⁵⁶` is not feasible" → wrong (prime-field DLP records ~795 bits).
34. "the energy is flat ⇒ no sector to target" → withdrawn (all readouts misaligned; only the differential survives).
35. "the 4th moment settles starvation vs spreading" → wrong; the statistic is blind (caught by the calibrator gate).
36. "the `T=1` clustering is 2-adic (`lo=2^{N−1}`)" → refuted by a matched odd-prime control; generic in `L`.
37. the 6000-sample 130-bit vs 256-bit flap-density gap → noise (`z=−0.85` at `N=10⁵`).
38. the prereg-frozen sub-Rayleigh mechanism (M4 excess on `Δ=0` quadruples) → refuted by its own pre-committed threshold.
39. the two `A_new`-channel within-cell mechanism sketches (μ₃/μ₄-equivariant sheaf) → WRONG (equivariant only at `a=0`); the framing B2.3 survives.
40. the ω-descent reframed as the order-pinning lever → withdrawn (a field automorphism permutes eigenvalues; it cannot manufacture `ζ₃`). Live **ingredient**, not the lever.
41. "`v>0` is generic" → WRONG; observed ~5% is a **suppressed** rate and the suppression is the content (B1.2).
42. the `E3` "unliftable ceiling / no control can move it / says nothing about the curve" → RETRACTED (null→closure failure mode); interpretation is OPEN.
43. `e₃=−p·e₁` stated unconditionally → corrected to `e₃=χ₂(−1)·p·e₁` (produced a false stratum-C null caught mid-run).
44. "9 of 12 out-of-sample" for the `G(χ₄)` sign rule → retracted (the 3 fitted primes were never named).
45. "a named crypto curve being amicable is unremarked" → narrowed (Pasta/Pallas-Vesta are a deployed 254-bit `j=0` amicable pair). **The FACT (A1.2) stands.**
46. **(post-Addendum)** the sub-Rayleigh deficit's "b=0 pure-y axis LOCALIZATION" → **wrong-null artifact** (the null omitted the forced Hermitian symmetry `g(n−d)=conj(g(d))`); the **diffuse aggregate ~−0.1% survives**, no locus. (`RESULT_harmonic_deficit_locus_v1` retracted; `RESULT_y_channel_chi2_vs_axis_v1` superseded.)

*(Process note: the recurring failure mode is reaching for "honest/genuinely" exactly when asserting
unchecked algebra or generalizing from a few primes; the fix is to run the check the word papers over.
See `feedback_self_cert_words_audit_trigger`, `feedback_negative_bias_enlarge_nulls`,
`feedback_closure_grade_2026_07_28`.)*

---

# PART G — SCOPED NULLS  *(compact; each is a magnitude at a matched floor with a firing control — a where-it-cannot-be map, NEVER "nothing there". A hidden aligned readout, another basis, or `2²⁵⁶` is consistent with every one.)*

- **LBE battery (A3.1)** — 30 local DLP-free features × 25 scalar targets, disjoint construction,
  Holm/FWER 0.01, `p=127…100003`, exhaustive over `d`. **0 rejections** at the discovery prime; floor
  `e_min=0.02`. Diffuse-dependence arm **ABSTAINED** (χ² miscalibrated 2–4×; report the integer rank).
  `lbe_harness_v1.py`.
- **Dirichlet-island curve image (A3.2), full-scale secp** — 4 energy/windowed statistics on `M=1024`
  islands, `N∈{64,128,252}`. All null; planted `±`-pair / residue-AP fire. `islands_curveimage_jointset_v1.py`.
- **GLV/μ₃ β-cross-structure (A3.3), full-scale secp** — exact GLV-orbit collision detectors `G1,G2 = 0`;
  plants fire. `islands_glv_beta_crossset_v1.py`.
- **Flap `ε` under the group law (A3.4), full-scale secp** — doubling `P(F|F)=0.24983` vs 0.25, Fisher
  null; bounds group-law flap dependence below ~`2⁻⁶–2⁻⁹` of forced-equal pairs at `n=10⁶`.
  `flap_grouplaw_transition_v1.py`.
- **Flap density 130-bit vs 256-bit (A3.5)** — `z=−0.85`, null (the earlier 6000-sample gap was noise).
- **No `d`-free selector predicts per-harmonic magnitude (A3.6)** — 6 selectors, permutation floor, 7 primes; scoped null.
- **Twist-orbit single-character spectrum (B4.1)** & **magnitude `|V(a)|²` (B4.2)** — null out-of-sample
  (12 primes), PLANT fires; the two low-`p` disagree ⇒ independent noise. `experiment-designer`-signed.
- **`S_diff` on the real 82 keys (B4.3)** — `S_diff=−35`, 30th pct, `real ≡ known-MT` on a joint object;
  rules out a frozen-orientation per-pair QR-bias above `ε≈0.034`. The orthogonal (orientation-symmetric)
  subspace — the μ₃-graded `χ₃(x_j−x_k)`, secp's Eisenstein direction — is invisible here (frontier #29).
- **`χ_k(x([d]G))` vs `d mod k` (post-Addendum, both key sets)** — NULL, `kfold_gate`-gated out-of-sample,
  `k∈{2,3,6}`, `N≤10⁴`, control fired. A per-point marginal bound, not a closure. `chik_dmodk_leakage_v1.py`.
- **Master Appendix-A nulls (carried):** single-key `(X,Y)→(n,k,D)` ~1e-5 bits; bilinear-additive joint
  sum flat `O(n)`; H² carry not leaked (z=849); difference-set μ₃/cubic/xy at the AP floor; no metastable
  soft mode (`|λ₂|~1/√n`); hybrid `χ_k`×additive ≈2√p; 3-point group-law/collinearity; index-calculus
  relation yield (β-lever ≤1.5×, bounded); GLV/CM ⊥ key-coordinate on the 82; `derr↔cap` a bit-length
  confound (dissolves at fixed bits); **finer-m difference scan** at floor (z=1050); **phase-hunt beyond
  μ₆** (9 CM/Frobenius candidates — the only *known computable* phase structure is the μ₆ group);
  **scalar-mult `ψ(d)`**; **cubic-moment / S3 tensor**; **bilinear difference-set** (powered to 1.4%);
  **joint `(x,y)` magnitude distribution** (CM = non-CM); **`S₄/S₅` decomposition** (β-lever → 1.0);
  **easy-target predictability** (no lever); **exposed-pubkey relations** (the original run had NO firing
  control — redone with plant+random it is a scoped null; *lesson: audit OLD nulls for a firing control
  before trusting them*). *Each at the matched floor for that readout/statistic/scale.*

---

# PART H — THE RECIPROCITY-BRIDGE PROGRAMME (`p ↔ n`)  *(consolidated from `BRIDGE_PROGRAMME_COMPENDIUM_v2.md`; its L/B/D/M/E labels are a SEPARATE namespace from the curve-structure P/M/L above)*

**⚠ Namespace note.** The objects below (**bridge-L1/L2/L3, bridge-B1–B5, D1–D3, M1–M2, E1–E5**) are the
reciprocity programme's own ledger and are **distinct** from the curve-structure `L1`(=P2, `Σχ₂=0`),
`L3`(=the CM layer), and `B1.x` used elsewhere in this document. Reproduction scripts:
`scripts_bridge_programme/` (exact integers; no float in any signal path; all verdicts from exact
permutation counts).

**The programme, and its mechanism.** The ledger item *"`ord_n(p)=(n−1)/6`, `ord_n(2)=(n−1)/64`,
`[VERIFIED]` and never explained"* dissolved and, pulled apart, produced an exact reciprocity law between
`p` and the group order `n`. With `n=p+1−t` ⇒ `n−p=1−t`, set **`U:=|t−1|`**; then **`n ≡ p (mod U)`**,
and for odd `ℓ`, `χ_ℓ(p mod n)=χ_ℓ(U mod n)`, `χ_ℓ(n mod p)=χ_ℓ(U mod p)`. The dichotomy: `ℓ=2` →
`ℚ(√U)/ℚ` abelian ⇒ a congruence does it; `ℓ≥3` → `ℚ(ζ_ℓ,U^{1/ℓ})/ℚ` non-abelian ⇒ **no congruence can
— the bridge requires `ζ_ℓ` to lie in the CM field.** Via Eisenstein reciprocity (`ν=1−π`, `N(ν)=n`):
**`χ₃(p mod n)=ω^{c₃}·χ₃(n mod p)`, `c₃ ≡ s·(t−1)/3 (mod 3)`**, and with quadratic reciprocity
**`c_p=6 ⟺ n` is a sextic residue mod `p`** (up to two explicit corrections). **An exact identity does
not decay — so the bridge holds at `2²⁵⁶`.**

| id | statement | grade |
|---|---|---|
| bridge-L3 | `3∣n−1` forced for prime-order `j=0` (why GLV applies). | `[PROVED]` + 4977/4977 |
| bridge-L1 | `n≡1 mod24 ⇒ sf(\|t−1\|)∣6 ⇒ (p/n)=+1` forced. | `[PROVED]` + 1546/1546 |
| bridge-L2 | density `≈2.69/√(2√p) ∝ p^{−1/4}` ⇒ `≈10⁻¹⁹` at secp. | `[PROVED asymptotic]`+`[VERIFIED 20–48 bit]` |
| bridge-B1 | the **cubic bridge** `χ₃(p mod n)=ω^{c₃}·χ₃(n mod p)`. | `[PROVED\|classical inputs]` + 12050/12050, 8→256 bit |
| bridge-B2 | `χ_λ(ω)=ω^{(a+b+1)/3}` (identity `(N(λ)−1)/3≡(a+b+1)/3`). ⚠ cite **Ireland–Rosen 2nd ed. Ch. 9 Exercises p. 135 / Z.-H. Sun Acta Arith. 84 (1998) eq (1.1)** — **NOT** IR Prop 9.3.3. | `[PROVED]` 3659/3659 |
| bridge-B3 | `t≡1 mod3 ⇒ ν,π̄` share a primarizing unit. | `[CITED — Silverman–Stange Thm 19(a); prior art, not ours]` |
| bridge-B4 | `c_p=6 ⟺ n` sextic residue mod `p` (up to the 2 corrections). | `[VERIFIED]` 150/150 at 256-bit **+ secp** |
| bridge-B5 | `\|t−1\|` a perfect cube ⇒ `χ₃=1` forced; density `∝p^{−1/3}`. | `[VERIFIED]` rate 1.0000; **density under-powered** |
| D1 | odd (prime, `N>5`) order ⇒ `D≡5 mod8` (2 inert in the **order `O_D`**, not the field). | `[CITED — Bröker–Stevenhagen]`; converse empirical 0/67477 |
| D2 | `w=4` branch empty (only `D=−4`, ramified). | `[VERIFIED]` 35907 twists, 0 odd |
| D3 | bridge at `ℓ=3` **only** for `D=−3`; bounded-away at `ℓ=5,7` (9.7σ/7.0σ), only **weakly** at `ℓ=11,13` (4.5σ/3.6σ), `ℓ≥17` untested. | `[VERIFIED — bounded, §dichotomy]` |
| M1 | the bridge is **CM-generated, not shape-generated**. | `[VERIFIED — bounded, <1.06 vs 1.645]` |
| M2 | the dichotomy is keyed to `w`, **not** the class number. | `[VERIFIED — bounded, h=2 only]` |
| E1–E5 | exact congruence laws ⇒ `c₃ ≡ s·(t−1)/3 (mod3)`. | `[VERIFIED — 0/52000, two samples]` |
| — | `P(c₃=0)=5/9`, ratio `5/3`. | `[VERIFIED]` (pooled `z=+0.08`, independent `z=+1.55`) — with the `s`-uniformity caveat |

**Controls (all fired):** K0 Eisenstein reciprocity 4000/4000 + 1500/1500(32-bit); K1 Gauss `2`-cubic-residue
1200/1200 + 400/400; K2 base rate 0.3395 vs 0.3250; K3 `ω²+ω+1≡0` both fields + 1500/1500; dichotomy
positive control reproduced its pre-committed effect (observed `0.1920` vs `0.1185`, ratio `1.69`); every
random-base negative control clean in every arm.

**Dissolutions (each with its scope):** `ord_n(2)=(n−1)/64` is a **selection effect** (`ν₂(n−1)=6`; 5 of
168 primes `q<1000` have odd order mod `n` vs 2.62 expected) — *about `2`, not `n`*. `ord_n(p)=(n−1)/6`
is a **`1/6` draw** (H-sextic "CM forces it" **falsified**: cube rate 0.3349, `z=+0.27`) — *this says the
two mechanisms examined do not force it, not that no mechanism does; the bridge determines where the draw
is made, not that it is `1/6`*. The `(p/n)` finite-size effect **decays** `z: +10.48(16b)→+0.15(256b)`,
controls clean throughout.

**The dichotomy measurement (§3, the file's declared contribution):** `D=−3,ℓ=3` (POS CTL) ratio **1.69**,
`1/20001`, `16.1σ`; `ℓ=5` 0.96 (`9.7σ`, strongly tested null); `ℓ=7` 0.96 (`7.0σ`); `ℓ=11,13` 1.03
(`4.5σ`/`3.6σ`, weakly bounded); ten `D=−11..−163` and ten `h=2` families at `ℓ=3`, ratios `0.94–1.04`,
`12.7–16.0σ`; CM `D=−3,ℓ=3` (M1) ratio **1.645** (`29.5σ`) vs matched control `n−p=Δ` **0.993** (`27.5σ`).

**Every open item, caveat and bound — carried (do not drop on any re-promotion):**
- **Novelty — no claim of any kind is supportable** until a citation-graph sweep (the ~40 papers citing
  Silverman–Stange arXiv:0912.1831; Lemmermeyer *Reciprocity Laws* Ch. 7; Cox *x²+ny²* §4; MathSciNet/
  zbMATH) — **not done.** bridge-B1 sits inside a **known `p↔q` sextic-reciprocity family** (Silverman–
  Stange Prop 23(b)/Thm 7.1(d); Babinkostova et al. *Elliptic Reciprocity* arXiv:1212.1983 Thm 2.7);
  published identities are base `2`/`4k`, the **base-`p`/base-`n`** instance was **NOT FOUND** in sources
  reached — **"not found ≠ novel".**
- **`KNOWN_FACTS` deflation:** "exactly one prime-order sextic class" is **not** a law — over `p≡1 mod6`,
  `p<600` the count is `{0:6,1:31,2:12,3:1}`; secp's "exactly one" is **typical (~62%), not distinctive.**
- **Corrections of record (kept inoculated):** bridge-B2's citation was wrong (IR Prop 9.3.3 → Ch. 9
  Exercises); "2 inert in the CM *field*" is wrong (it is the **order `O_D`**; `D=−12` has 2 inert in `K`
  yet 6028/6028 even orders); "`D≡5 mod8 ⇒ odd order`" is **FALSE pointwise** (only the converse is a
  theorem); Gauss's `2`-criterion is Euler's conjecture first proved by Gauss; "3 cubic-residue ⟺
  `p=a²+243b²`" is FALSE (it is `4p`); the H-constant model was **REJECTED, not flagged** ("a passing
  number is not a passing model"); `P(s=0)` systematic **WITHDRAWN** (`z=−1.92→+2.18`).
- **Mathematical gaps:** E1–E5 **verified, not proved** (the `μ(λ)=A+B` derivation is sketched); the
  primarizing sign is always `+1` (0/52000) **unexplained**; **`s`-uniformity NOT established**
  (`χ²=7.43`, `p≈0.024`) — `5/9` follows from E4 only if `s` and `9∣t−1` are equidistributed, so the
  verified object is the **structure**, not the value; **secp's other `n−1` factors (`149, 631,
  107361793816595537, …`) have no reciprocity law in hand**; `w=4` needs a different framework (mod the
  odd part of `#E`).
- **Bounds that are bounds, not absences:** M1 shape-association `<~1.06` at 3σ vs CM's 1.645 (30-bit,
  `N=17305`; a residual `<~6%` of baseline not excluded); ⚠ **uniform-correction blind spot**
  (pre-committed, verbatim): *"No bridge with a non-uniform correction is detectable by a generator-free
  2×2 association at this N"* — **not** "no bridge exists"; **a hypothetical `ℓ≥5` bridge with exactly
  uniform correction would read as absent — wrongly. Untouched by all subsequent work.** M2 bounded to
  ≈1.08 (h=2; `h≥3` untested); bridge-L1's free cell bounded at 0.5, **not proved**; bridge-B5's density
  order-of-magnitude only; `ℓ≥17` untested, `ℓ=11,13` weakly bounded.
- **Prereg deviations:** `ord_n` family experiment unregistered + H-sextic half not run + hypothesis (i)
  falsified and repaired post-hoc; `cubic_sextic` train/freeze/test not executed + `e_λ(ω)` supplement
  entered unregistered + a float cube-root written-then-removed; `dichotomy` D1 generalized post-hoc +
  power column post-hoc + **no multiple-comparison correction over 10 tests** (two small p-values vanished
  at higher power); `mechanism` replacement laws post-hoc on the discovery sample (discharged by the
  independent retest).
- ⚠ **Audit status:** compile-diff was run against the ten sources **on v1** (23 findings; the 22-item
  restoration is grep-verified in `AUDIT_compendium_v2_restoration_check_v1.md`); a **fresh full re-audit
  of v2 was attempted but HUNG (~9h, killed) and NOT completed** — a *new* v2-introduced loss beyond the
  named-item scan would not have been caught. That gap is open.

---

# APPENDIX A — CITED INPUTS  *(verify before relying)*

- **✅ Kohel–Shparlinski**, ANTS-IV 2000, LNCS 1838, 395–404. **VERIFIED** against the source
  (`kohel_shparlinski_ants4_2000.pdf`, SHA-256 `645d9022e029055271ae60387518b440075fad282886d8baa9df35f5b55d8d2a`).
  Thm 1 `|S| ≤ Σmᵢ deg(𝔓ᵢ)q^{1/2}`; eq (3) `|S| ≤ 2 deg(f) q^{1/2}`; `ω ∈ Hom(E(F_q),ℂ*)`, **ψ additive**.
  **Scope: additive ψ only — NOT χ₂** (retraction 10).
- **⚠ Lange–Shparlinski**, JMC 1 (2007) 1–11 (SHA-256 `f29c524a9670…c6edec`). Lemma 2.4 bounds the
  UNTWISTED sum only. **NOT load-bearing; do not cite for the mixed sum** (retraction 11).
- **Tate's isogeny theorem** — carries `Hom(E,A_new)=0` from disjoint Frobenius eigenvalues (P13).
- **✅ Stickelberger (Katre)** — **VERIFIED** for the intended use (`m=12` composite, residue degree `f=2`),
  B2.1. Three caveats travel with it: cite the proof's hypothesis `j,k,j+k≢0 mod m`; use the `F_q`
  digit-sum form; Stickelberger gives the **ideal**, not the value.
- **Silverman–Stange** arXiv:0912.1831 — Thm 19(a)–(d), Rmk 20, Prop 23 = the `p↔#E` bridge (B1);
  amicable-pair density is Conjecture 40 (`13/50≈26%` measured, `secp256k1_arithmetic_v4.md` thread B).
- **Heuristics** `[HEURISTIC]`: Diem 2011 (genus-1 ⇒ no index-calc lever); the canonical-lift (xedni)
  obstruction protecting the amicable transfer (§XI.3); isobaric ⇒ first-fall curve-independence (BFS).

---

# APPENDIX B — THE 82 SOLVED KEYS AND HOW TO CONSTRUCT MORE

*Embedded verbatim from `solved_keys_and_construction_v2.md` (2026-07-14) for self-containment — this is
the one place full code is inlined (a construction/provenance appendix, by request), not a finding's
replication block. Fields per key: `d` (private scalar), `(X,Y)` (public point `[d]G`), `(n,k)` (Farey
best rational of `band_offset/A`), `derr` (the exact residual `|n(d−A)−kA|`), `D_terms` (an invertible
"Engel-like" d-signature — **distinct** from the curve-identity scalar `D`; see the field definitions).
Integrity: all 82 reproduce their on-chain `X,Y` via exact `scalar_mul`.*





Supersedes v1 (v1 excerpted the data and referenced the script; v2 embeds the full
generator script **and** all 82 rows inline, so this file is fully self-contained).

Self-contained dataset for detector testing: every solved key with its public
(address, X, Y), private (`d`), and the exact `(n, k, derr, D)` decomposition —
plus a recipe (`construct_key`) to make **new** solved keys of **any** construction
so any detector can be validated on known answers before it is aimed at unknowns.

Regenerate / integrity-check: run the embedded `emit_solved_keys_dataset_v1.py`
(writes `solved_keys_augmented_v1.csv`; **82/82** keys reproduce their on-chain
`X,Y` via exact `scalar_mul`). Source rows: `puzzles_verified.csv`.

## Field definitions (all exact integers)

For a key of size `bits` with private scalar `d`:
- `A = 2^(bits-1)` — band base;  `band_offset = d − A`.
- `(X, Y) = [d]G` — the public point (`ecc_secp256k1.scalar_mul`, exact Jacobian).
- `(n, k) = best_nk(d, bits)` — Farey best rational of `band_offset / A` over
  denominators `n ≤ 256`: `argmin_{n≤256, 0≤k≤n} |n·(d−A) − k·A|`, then reduced by `gcd`.
- `derr = |n·(d−A) − k·A|` — the exact residual of that `(n,k)` approximation.
- `D_terms = d_recursion(2^bits, d)` — greedy nearest-unit-fraction (Engel-like)
  expansion; an **invertible** encoding of `d` (reproduces the dataset `D_terms`
  column 40260/40260, per `d_recursion_exact_v1`). `n_Dterms = len(D_terms)`.

Two distinct "D"s in the corpus: **this** `D_terms` (the invertible d-signature) and
the curve-identity scalar `D` in `n·Q−(n+k)·A=r·G, r=n·D−(2^{N−1}·k mod n)`
(`btc_puzzle_exact_leak_test`). Different objects; this file uses `D_terms`.

## How to construct MORE solved keys (any construction)

```python
from emit_solved_keys_dataset_v1 import construct_key
rec = construct_key(d, bits)   # any d, any rule -> full verified known-answer record
# rec = {bits, d, X, Y, n, k, derr, D_terms, n_Dterms, band_offset}
```
Pick `d` by whatever construction tests your detector (random-in-band,
sum-of-fractions à la Findings B/C, low-band-offset, low-D-term, …). The 100k
MT19937 reference set is exactly this pipeline driven by our MT19937 (select
bit-length → random-in-band `d` → curve), so it is a **full-power known-generator**
reference — test every detector on both it and the real 82
(`feedback_test_on_both_sets`).

## Generator / integrity script (`emit_solved_keys_dataset_v1.py`)

```python
#!/usr/bin/env python3
"""Emit the 82-solved-key dataset with all derived fields (pub, X, Y, d, n, k,
derr, D_terms), integrity-checked against on-chain X,Y via exact scalar_mul; plus
construct_key(d,bits) to make more solved keys of ANY construction."""
import csv
from math import gcd
from ecc_secp256k1 import scalar_mul


def best_nk(v, bits, NMAX=256):
    """Farey best rational of (v - 2^(bits-1)) / 2^(bits-1), denominators n<=NMAX."""
    A = 1 << (bits - 1)
    num = v - A
    best = None
    for n in range(1, NMAX + 1):
        kk = (2 * n * num + A) // (2 * A)
        kk = 0 if kk < 0 else (n if kk > n else kk)
        for c in (kk - 1, kk, kk + 1):
            if 0 <= c <= n:
                key = (abs(n * num - c * A), n, c)
                if best is None or key < best:
                    best = key
    resid, n, k = best
    g = gcd(k, n) if n else 1
    return (n // g if g > 1 else n, k // g if g > 1 else k, resid)


def d_recursion(N, error):
    """greedy nearest-unit-fraction expansion; terminates exactly (residual 0)."""
    e = abs(error)
    terms = []
    while e > 0:
        D = N // e
        if D == 0:
            break
        terms.append(D)
        e = abs(e - N // D)
    return terms


def construct_key(d, bits=None):
    """Full solved-key record for ANY chosen d (any construction). If bits is
    None, uses d.bit_length(). Verifies (X,Y)=[d]G on the curve."""
    if bits is None:
        bits = d.bit_length()
    x, y = scalar_mul(d)
    n, k, derr = best_nk(d, bits)
    D_terms = d_recursion(1 << bits, d)
    return {"bits": bits, "d": d, "X": x, "Y": y,
            "n": n, "k": k, "derr": derr,
            "D_terms": D_terms, "n_Dterms": len(D_terms),
            "band_offset": d - (1 << (bits - 1))}


def example_constructions(bits=64):
    import random
    N = 1 << bits
    A = 1 << (bits - 1)
    rng = random.Random(0)
    return {
        "random-in-band": A + rng.randrange(A),
        "sum-of-fractions (N/3+N/7)": N // 3 + N // 7,
        "sum-of-fractions+2^(b/8)": N // 3 + N // 7 + N // 13 + 2 ** (bits // 8),
        "low-band-offset": A + 12345,
        "near-top": N - 999,
    }


def main():
    print("Recomputing + integrity-checking the 82 solved keys "
          "(exact [d]G vs on-chain X,Y)...\n")
    out_rows = []
    bad = 0
    with open("puzzles_verified.csv") as fh:
        for r in csv.DictReader(fh):
            bits = int(r["bits"]); d = int(r["private_key"], 16)
            X = int(r["X"], 16); Y = int(r["Y"], 16)
            rec = construct_key(d, bits)
            ok = (rec["X"] == X and rec["Y"] == Y)
            bad += (not ok)
            out_rows.append((int(r["puzzle"]), bits, d, X, Y, r["address"],
                             rec["n"], rec["k"], rec["derr"],
                             rec["n_Dterms"], rec["D_terms"], ok))
    print(f"integrity: {len(out_rows)-bad}/{len(out_rows)} keys reproduce on-chain X,Y "
          f"via scalar_mul\n")

    with open("solved_keys_augmented_v1.csv", "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["puzzle", "bits", "d_priv", "X", "Y", "address",
                    "n", "k", "derr", "n_Dterms", "D_terms"])
        for pz, bits, d, X, Y, addr, n, k, derr, nD, Dt, ok in out_rows:
            w.writerow([pz, bits, d, f"{X:x}", f"{Y:x}", addr, n, k, derr, nD,
                        "|".join(map(str, Dt))])
    print("wrote solved_keys_augmented_v1.csv\n")

    print("example constructions (construct_key on chosen d, 64-bit):")
    for name, d in example_constructions(64).items():
        rec = construct_key(d, 64)
        print(f"  {name:32s}: n={rec['n']:>3} k={rec['k']:>3} "
              f"derr={rec['derr']} #D={rec['n_Dterms']}")


if __name__ == "__main__":
    main()
```

## The 82 solved keys — full data

Columns: `puzzle, bits, d_priv, X, Y, address, n, k, derr, n_Dterms, D_terms`
(`D_terms` `|`-separated). Machine copy: `solved_keys_augmented_v1.csv`.

```csv
puzzle,bits,d_priv,X,Y,address,n,k,derr,n_Dterms,D_terms
1,1,1,79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8,1BgGZ9tcN4rm9KBzDn7KprQz87SZ26SAMH,1,0,0,1,2
2,2,3,f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9,388f7b0f632de8140fe337e62a37f3566500a99934c2231b6cb9fd7584b8e672,1CUNEBjYrCn2y1SdiUMohaKUi4wpP326Lb,2,1,0,2,1|4
3,3,7,5cbdf0646e5db4eaa398f365f2ea7a0e3d419b7e0330e39ce92bddedcac4f9bc,6aebca40ba255960a3178d6d861a54dba813d0b813fde7b5a5082628087264da,19ZewH8Kk1PDbSNdJ97FP4EiCjTRaZMZQA,4,3,0,2,1|8
4,4,8,2f01e5e15cca351daff3843fb70f3c2f0a1bdd05e5af888a67784ef3e10a2a01,5c4da8a741539949293d082a132d13b4c2e213d6ba5b7617b5da2cb76cbde904,1EhqbyUMvvs7BfL8goY6qcPbD6YKfPqb7e,1,0,0,1,2
5,5,21,352bbf4a4cdd12564f93fa332ce333301d9ad40271f8107181340aef25be59d5,321eb4075348f534d59c18259dda3e1f4a1b3b2e71b1039c67bd3d8bcf81998c,1E6NuFjCi27W5zoXg8TRdcSRq84zJeBW3k,16,5,0,3,1|2|6
6,6,49,f2dac991cc4ce4b9ea44887e5c7c0bce58c80074ab9d4dbaeb28531b7739f530,e0dedc9b3b2f8dad4da1f32dec2531df9eb5fbeb0598e4fd1a117dba703a3c37,1PitScNLyp2HCygzadCh7FveTnfmpPbfp8,32,17,0,3,1|4|64
7,7,76,96516a8f65774275278d0d7420a88df0ac44bd64c7bae07c3fe397c5b3300b23,bdacd9a05fb9fb73108c0a99d567fba9b2f75ab36207e1557f6bf255f1337ff0,1McVt1vMtCC7yn5b9wgX1833yCcLXzueeC,16,3,0,3,1|2|10
8,8,224,8bc89c2f919ed158885c35600844d49890905c79b357322609c45706ce6b514,d313f3cdd7cdcc16de776fec3b5892c1172d3056112776f06f63f4cea8c95157,1M92tSqNmQLYw33fuBvjmeadirh1ysMBxK,4,3,0,2,1|8
9,9,467,43601d61c836387485e9514ab5c8924dd2cfd466af34ac95002727e1659d60f7,8791c0007c09c94db328034b88c5bbbc113335366679eb099a5e75b583bc2c2a,1CQFwcjw1dwhtkVWBttNLDtqL7ivBonGPV,256,211,0,3,1|11|512
10,10,514,a7a4c30291ac1db24b4ab00c442aa832f7794b5a0959bec6e8d7fee802289dcd,d580b4242cf68189ac1309e79c5a2132d2cbf0e18be6d0b37d05a32256ca0c8b,1LeBZP5QCwwgXRtmVUvTVrraqPUokyLHqe,256,1,0,3,1|2|512
11,11,1155,8b05b0603abd75b0c57489e451f811e1afe54a8715045cdf4888333f3ebc6e8b,1d10f88145db40fb889e2ddce81bda7c27f5b615acd6179dbb30f4fe7f40fb39,1PgQVLmst3Z314JrQn5TNiys8Hc38TcXJu,86,11,2,4,1|2|15|409
12,12,2683,8b00fcbfc1a203f44bf123fc7f4c91c10a85c8eae9187f9d22242b4600ce781c,61e9e58a3e81e690ec0264280ee5442a0a8de699dadfbcac478985cc89d35bc9,1DBaumZxUkM4qMQRt2LVWyFJq5kDtSZQot,129,40,5,4,1|2|6|87
13,13,5216,aadaaab1db8d5d450b511789c37e7cfeb0eb8b3e61a57a34166c5edc9a4b869d,2ed7caaf2a261616f564190b4bc9f496f3df86353ff76d7f704e48e654bacdf1,1Pie8JkxBT6MGPz9Nvi3fsPkr2D8q3GBc1,128,35,0,4,1|2|7|163
14,14,10544,b4f1de58b8b41afe9fd4e5ffbdafaeab86c5db4769c15d6e6011ae7351e54759,7875ee3c7e4d1b5c753d3747c7d5774b583da4d075fb8caf8cab311b0f350483,1ErZWg5cFCe4Vw5BzgfzB74VNLaXEiEkhk,101,29,16,5,1|2|6|43|5461
15,15,26867,fea58ffcf49566f6e9e9350cf5bca2861312f422966e8db16094beb14dc3df2c,c71136e9f21ec86870c3a999f045d712f848c6fd6ed9582521c3f7444c8f182e,1QCbW9HWnwQWiQqVo5exhAnmfqKRrCRsvW,236,151,4,4,1|5|50|10922
16,16,51510,9d8c5d35231d75eb87fd2c5f05f65281ed9573dc41853288c62ee94eb2590b7a,83c227263dece3d7e8afe4005eff667bb90dd33ce17c663b1e83b303b12c0348,1BDyrQ6WoF8VN3g9SAS1iKZcPzFfnDVieY,7,4,122,4,1|4|27|949
17,17,95823,3f688bae8321b8e02b7e6c0a55c2515fb25ab97d85fda842449f7bfa04e128c3,393e3b1c529624e56840acbb10243ec9e0cfe99c3cffe1c87537b735bbba2d2f,1HduPEXZRdG26SUT5Yk83mLkPyjnZuJ7Bm,251,116,139,4,1|3|15|441
18,18,198669,ce4a3291b19d2e1a7bf73ee87d30a6bdbc72b20771e7dfff40d0db755cd4af1,889098969cd1f2642a070ace8aacd681b6c97281ed46d6354f8094614865fba8,1GnNTmTVLZiqQfLbAdp9DVdicEnB5GoERE,159,82,19,4,1|4|127|87381
19,19,357535,85663c8b2f90659e1ccab201694f4f8ec24b3749cfe5030c7c3646a709408e19,457e3dd2f2a02ea1dd219233e317782fcc39a3594ca5ef4228f9af3b49bdc671,1NWmZRpHH4XSPwsW6dsS3nrNWfL1yrJj4w,11,4,725,4,1|3|65|9362
20,20,863317,3c4a45cbd643ff97d77f41ea37e843648d50fd894b864b0d52febc62f6454f7c,88020b66e0e1970a0009fa411e77166bca00b1ada6163854362ca33d1ee35ab1,1HsMJxNiV7TLxmoF6uJNkydxPFDog4NQum,150,97,1586,4,1|5|42|2056
21,21,1811764,1a746c78f72754e0be046186df8a20cdce5c79b2eda76013c647af08d306e49e,2d5736900aa6d87c26325ccc3d707065de2fb7dd6602f71ffadb33dcdf26c239,14oFNXucftsHiUMY8uctg6N487riuyXs4h,158,115,2536,4,1|7|147|34379
22,22,3007503,3ed96b524db5ff4fe007ce730366052b7c511dc566227d929070b9ce917abb43,700d7526050cc27c80c39aac7e5a930a79914bc74c8808177d58335f69ab72f4,1CfZWK1QTQE3eS9qn61dQjV89KDjZzfNcv,129,56,5233,5,1|3|19|443|279620
23,23,5598802,f82710361b8b81bdedb16994f30c80db522450a93e8e87eeb07f7903cf28d04b,97336f10faad1355ee425ca4f3a989bbd929704bfb9ae2371178ae3adef7ab3f,1L2GM8eE7mJWLdo3HZS6su1832NX2txaac,218,73,3628,4,1|3|1311|4194304
24,24,14428676,6ea839d22847ee1dce3bfc5b11f6cf785b0682db58c35b63d1342eb221c3490c,d4313e400ac025a18f72b7e4487a3a47676c1e97ba6f8119e9736d4b8c4ce2a9,1rSnXMr63jdCuegJFuidJqWxUPV7AtUf7,25,18,6756,4,1|7|348|3355443
25,25,33185509,57fbea3a2623382628dde556b2a0698e32428d3cd225f3bd034dca82dd7455a,b7deb4729bedde33c9edc651ecb0c034adc49678ad67414e3e90b01f2d085655,15JhYXn6Mx3oF4Y7PcTAv2wVVAuCFFQNiP,91,89,17561,3,1|90|8594
26,26,54538862,4e4f50a2a3eccdb368988ae37cd4b611697b26b29696e42e06d71368b4f3840f,76d012b98c9e265dda1a9028ae37f1a4548505fac40524d507b5675c74714ca,1JVnST957hGztonaWK6FougdtjxzHzRMMg,8,5,103280,4,1|5|78|7803
27,27,111949941,1a864bae3922f351f1b57cfdd827c25b7e093cb9c88a72c1cd893d9f90f44ece,340864e1e4a939cf2eb8511e833c1c2bdd51a55bd204368332ae70d68a65c61,128z5d7nN7PkCuX5qoA4Ys6pmxUYnEy86k,220,147,33932,3,1|6|1318
28,28,227634408,e9e661838a96a65331637e2a3e948dc0756e5009e7cb5c36664d9b72dd18c0a7,9f531540a4ca59f50f93b8bf7b0c060045754aaae7ce1bea5a136c0d5874b97,12jbtzBb54r97TCwW3G1gCFoumpckRAPdY,125,87,142664,4,1|6|68|28599
29,29,400708894,6caad634382d34691e3bef43ed4a124d8909a8a3362f91f1d20abaaf7e917b36,f5c907aad14e4457181ce6be0f0206a1a22d2730d14edf5d50630ad30d63baf4,19EEC52krRUK1RkUAEZmQdjTyHT7Gp1TYT,69,34,61718,5,1|3|12|276|600526
30,30,1033162084,d282cf2ff536d2c42f105d0b8588821a915dc3f9a05bd98bb23af67a2e92a5b,b0ca8ab2bfb595a48a19d4faecd863697762a74e1e889de825accfee9895790d,1LHtnpd8nU5VHEMkG2TMYYNUjjLc992bps,172,159,393424,4,1|26|1495|5395687
31,31,2102388551,87dc70db1806cd9a9a76637412ec11dd998be666584849b3185f7f9313c8fd28,446b6eef4da5141b139a7d9a8f684d20536cd9383a747885791a11af1aef6c91,1LhE6sCTuGae42Axu1L1ZB7L96yi9irEBE,119,114,2392577,4,1|47|3602|14510024
32,32,3093472814,9c58240e50e3ba3f833c82655e8725c037a2294e14cf5d73a5df8d56159de69,4fd08050375c910eecb46adeb9ffde4614adbf875f0493ad8d0a117d23b219e0,1FRoHA9xewq7DjrZ1psWJVeTer8gHRqEvR,84,37,6194968,5,1|3|18|508|645956
33,33,7137437912,a355aa5e2e09dd44bb46a4722e9336e9e3ee4ee4e7b7a0cf5785b283bf2ab579,4162d6719ade112c0440936eaa0666052fd1fffb8562ad3629b0718c298495f,187swFMjz1G54ycVU56B7jZFHFTNVQFDiu,68,45,14473568,5,1|5|32|2916|14939016
34,34,14133072157,3cdd9d6d97cbfe7c26f902faf6a435780fe652e159ec953650ec7b1004082790,c7fd4dd8b1c621129b2277c44a3fd706e17783cafc47894cfe5fbc912e7b67bb,1PWABE7oUahG2AFFQhhvViQovnCr4rEv7Q,234,151,14066818,5,1|5|44|13476|199765920
35,35,20112871792,f6a8148a62320e149cb15c544fe8a25ab483a0095d2280d03b8a00a7feada13d,8fde318a70a6dbed63953f4bb93087820e5ccb071faa514204ad19650e5a86ee,1PWCx5fovoEaoBowAvF5k91m2Xat9bMgwb,41,7,5977360,6,1|2|11|180|123834|34359738368
36,36,42387769980,b3e772216695845fa9dda419fb5daca28154d8aa59ea302f05e916635e47b9f6,6e1ad5a30b9c99a0ce54247314bd60f6a8c4af66c2672b1a9d7bfebbd8f9340c,1Be2UF9NLfyLFbtm3TCbmuocc9N1Kduci1,107,25,5923284,6,1|2|8|122|50108|8589934592
37,37,100251560595,7d2c03c3ef0aec70f2c7e1e75454a5dfdd0e1adea670c1b3a4643c48ad0f1255,6144da0f5d8070b5cbfc25541705394c22b83d0c90f3f6fb1fe5b20dac02a940,14iXhn8bGajVWegZHJ18vJLHhntcpL4dex,85,39,167535311,6,1|3|15|255|69730|10572227190
38,38,146971536592,c060e1e3771cbeccb38e119c2414702f3f5181a89652538851d2e3886bdd70c6,37bbfdac1b7ca715972daa71db7e26d673a9793c6b499406676154c12d566d3f,1HBtApAFA9B2YZw3G2YKSMCtb3dVnjuNe2,173,12,130561904,5,1|2|28|966|4059455
39,39,323724968937,2d77cd1467019a6bf28f7375d0949ce30e6b5815c2758b98a74c2700bc006543,35c003eaea2e33c7ced258f506f57f8dbd90636cbf24e91c9729e5833050d06e,122AJhKLEfkFBaGAd84pLp1kfE7xK3GdT8,45,8,905465867,5,1|2|11|486|1233928
40,40,1003651412950,a2efa402fd5268400c77c20e574ba86409ededee7c4020e4b9f0edbee53de0d4,7ba1a987013e78aef5295bf842749bdf97e25336a82458bbaba8c00d16a79ea7,1EeAxcprB2PpCnr34VfZdFrkUWuxyiNEFv,195,161,1044218878,5,1|11|268|151288|24988900631
41,41,1458252205147,b357e68437da273dcf995a474a524439faad86fc9effc300183f714b0903468b,9a6435e99428f3ef51a405550940fc39ce67823cb8b35f7f4d829902974d0c65,1L5sU9qvJeuwQUdt4y1eiLmquFxKjtHr3E,236,77,380920804,6,1|2|6|283|309649|99955602525
42,42,2895374552463,eec88385be9da803a0d6579798d977a5d0c7f80917dab49cb73c9e3927142cb6,28afea598588ea50a6b11e552f8574e0b93abd5595f5aa17ea3be5304103d255,1E32GPWgDyeyQac4aJxm9HVoLrrEYPnM4N,60,19,364040828,6,1|2|6|119|14566|218753867
43,43,7409811047825,a631f9ba0f28511614904df80d7f97a4f43f02249c8909dac92276ccf0bcdaed,c69d75bbc4ec87b7d7616b7a197fa0ab25814fb551d292aa70b54979e21cbc64,1PiFuqGpG8yGM5v6rNHWS3TjsG6awgEGA1,92,63,5407178780,5,1|6|110|38086|11791009413
44,44,15404761757071,5e466e97ed0e7910d3d90ceb0332df48ddf67d456b9e7303b50a3d89de357336,7715eb01dc2b29c9400694be91f9dda229d7f7eac9da41441f112daeb4dbf54c,1CkR2uS7LmFwc3T2jV8C1BhWb5mQaoxedF,189,142,6818264429,4,1|8|1516|3272265
45,45,19996463086597,6ecabd2d22fdb737be21975ce9a694e108eb94f3649c586cc7461c8abf5da71a,aa9a8c19d3626939f8f87d0c00c130d76a332fa99fda533bdf449a67407d11b6,1NtiLNGegHWE3Mp9g2JPkgx6wUg4TW7bbk,139,19,57025980745,6,1|2|14|323|936955|2345624805922
46,46,51408670348612,fd5487722d2576cb6d7081426b66a3e2986c1ce8358d479063fb5f2bb6dd5849,a004626dffa0fb7b934118ea84bacc3b030332eee083010efa60025e4fde7297,1F3JRMWudBaj48EhwcHDdpeuy2jwACNxjP,180,83,70803387344,6,1|3|15|360|178895|1134979744801
47,47,119666659114170,3a12bd3caf0b0f77bf4eea8e7a40dbe27932bf80b19ac72f5f5a64925a594196,c058e0f0f399f3c35b24b1de2374abe4355f932126eeb97919e73d5d2e56ce3a,1Pd8VvT49sHKsmqrQiP61RsVwmXCZ6ay7Z,177,124,6665731226,5,1|6|58|3425|86045345
48,48,191206974700443,91bee5cf4b14c291c650732faa166040e4c18a14731f9a930c1e87d3ec12debb,5c9103bbf879a6d6544a5df287116caf287ac27c934508ea1a2f422fbc7b5156,1DFYhaB2J9q1LLZJWKTnscPWos9VBqDHzv,145,52,273874435381,5,1|3|79|47036|3369182427
49,49,409118905032525,591d682c3da4a2a698633bf5751738b67c343285ebdc3492645cb44658911484,baca0af074d601c29f5acd658d0cb8568a38f48f3d3c2de066805f3247cecbb4,12CiUhYVTTH33w3SPUBqcpMoqnApAV4WCF,86,39,146256034850,6,1|3|16|412|594218|446431366710
50,50,611140496167764,f46f41027bbf44fafd6b059091b900dad41e6845b2241dc3254c7cdd3c5a16c6,eb3dfcc04c320b55c529291478550be6072977c0c86603fb2e4f5283631064fb,1MEzite4ReNuWaL5Ds17ePKt2dCxWEofwk,35,3,2180864138116,6,1|2|23|1478|7738863|102354536985693
51,51,2058769515153876,8c6c67bef9e9eebe6a513272e50c230f0f91ed560c37bc9b033241ff6c3be78f,810ddadcaeae69d8aae00ec0760b089bc312134b87d14bbb69ffcdefa5b38bfc,1NpnQyZ7x24ud82b7WiRNvPm6N8bqGQnaS,35,29,661007542276,5,1|11|192|45630|4340852389
52,52,4216495639600700,74c33bd548ef02667d61341892134fcf216640bc2201ae61928cd0874f6314a7,d8b0b0699fb814528ef174a644b4fae2cc77dd91f167b19577b2c0d24b1e15ed,15z9c9sVpu6fwNiK7dMAFgMYSK4GqsGZim,251,219,5506892290860,5,1|15|342|138860|50901359984
53,53,6763683971478124,faaf5f3afe58300a335874c80681cf66933e2a7aeb28387c0d28bb048bc6349,65455ef6afc625e4aeef1229f052dfd9ab299b02aaa7e659c0e010a795e49e38,15K1YKJMiJ4fpesTVUcByoz334rHmknxmT,2,1,16569060844760,5,1|4|1087|5113542|176611750092960
54,54,9974455244496707,4af4b81f8c450c2c870ce1df184aff1297e5fcd54944d98d81e1a545ffb22596,5f8151d32bd6771ea637e2c8328097d49d2498c3ddd4c76a81f2bad58944cd,1KYUv7nSvXx4642TKeuC2SNdTk326uUpFy,149,16,5954397745663,6,1|2|18|537|7387486|109843893350499
55,55,30045390491869460,85a30d8413af4f8f9e6312400f2d194fe14f02e719b24c3f83bf1fd233a8f963,eb400323654cec63999b56f4ba44e8b21ab92d9d697fabe4666df3678585669,1LzhS3k3e9Ub8i2W1V8xQFdB8n2MYCHPCa,3,2,64178928198460,5,1|6|1684|20054877|537743239089014
56,56,44218742292676575,3f2db2074e3217b3e5ee305301eeebb1160c4fa1e993ee280112f6348637999a,e00baccca7595a1af869923463f7f5928452d888fbeb495f827bc28f829ab38f,17aPYR1m6pVAacXg1PTDDU7XafvK1dxvhi,22,5,34810926857514,6,1|2|8|88|45539|5883254408
57,57,138245758910846492,a521a07e98f78b03fc1e039bc3a51408cd73119b5eb116e583fe57dc8db07aea,6fb15c871dd7cf7d287390acd4e09d41f705081a98d5fe3a930ca032525dbcdc,15c9mPGLku1HuW9LRtBf4jcHVpBUt8txKz,221,203,107152784370132,5,1|24|1064|1889609|8417451555157
58,58,199976667976342049,11569442e870326ceec0de24eb5478c19e146ecd9d15e4666440f2f638875f42,524c08d882f868347f8b69d3330dc1913a159d8fb2b27864f197693a0eb39a23,1Dn8NF8qDyyfHMktmuoQLGyjWmZXgvosXf,129,50,371503369923233,6,1|3|36|1572|7749328|96656732445242
59,59,525070384258266191,41267d2d7ee1a8e76f8d1546d0d30aefb2892d231cee0dde7776daf9f8021485,cf8b796676a624addecf7aaa9151eb7aafee708d2b1762adfc0bf2974836ebc,1HAX2n9Uruu9YDt4cqRgYcvtGvZj1rbUyt,129,106,58826335921201,5,1|11|567|376589|153323000894
60,60,1135041350219496382,48e843dc5b1bd246e6309b4924b81543d02b16c8083df973a89ce2c7eb89a10d,d094fcabf8995e2a25c73298a9f7419720db622daff89c67fd5535f6ac29720f,1Kn5h2qpgw9mWE5jKpk8PP4qvvJ1QVy8su,129,125,696906754532674,5,1|64|8588|300186975|576460752303423488
61,61,1425787542618654982,49a43860d115143c35c09454863d6f82a95e47c1162fb9b2ebe0186eb26f453f,d3a2cb3be02da3fe0286ef4a5fe755045bcc2067424e33243e0506c1ce631e5c,1AVJKwzs9AskraJLGHAZPiaZcrpDr1U6AB,169,40,2499760278326026,6,1|2|8|150|290094|126987572556
62,62,3908372542507822062,231a67e424caf7d01a00d5cd49b0464942255b8e48766f96602bdfa4ea14fea8,3d3011be9c3eac0a86a1d3a6a1fa7f5d97a48329985209ebf0eb0152f4d362c5,1Me6EfpwZK5kQziBwBfvLiHjaPGxCKLoJi,200,139,6271621877837328,6,1|6|70|7946|463197877|288230376151711744
63,63,8993229949524469768,65ec2994b8cc0a20d40dd69edfe55ca32a54bcbbaa6b0ddcff36049301a54579,5a1b76ab01e9edd0de24157ceff77bcb0f615560b250b365a5d435873eaa4625,1NpYjtLira16LfGbGwZJ5JbDPh3ai9bjf4,20,19,8844271821267104,5,1|40|20857|1561865079|3074457345618258602
64,64,17799667357578236628,100611c54dfef604163b8358f7b7fac13ce478e02cb224ae16d45526b25d9d4d,5127c2d0b1c4a4d5b4996bbdf37633b86901d0303b61e2f6f0772282ae08ff95,16jY7qLJnxb7CHZyqBP8qca9d51gAjyXQN,57,53,10115327934148916,5,1|28|1571|2852311|22407329126056
65,65,30568377312064202855,30210c23b1a047bc9bdbb13448e67deddc108946de6de639bcc75d47c0216b1b,e383c4a8ed4fac77c0d2ad737d8499a362f483f8fe39d1e86aaed578a9455dfc,18ZMbwUFLMHoZBbfpCjUJQTCMCbktshgpe,35,23,17950352906893803,5,1|5|35|71935|6906760590
66,66,46346217550346335726,4ee2be2d4e9f92d2f5a4a03058617dc45befe22938feed5b7a6b7282dd74cbdd,7b4c61e962f21c90418e516459c297472a3d1902259b9babf4cf8e72e2eb2238,13zb1hQbWVsc2S7ZTZnP2G4undNNpdh5so,121,31,82125184202931582,7,1|2|7|67|5662|72320127|10528963512391296
67,67,132656943602386256302,12209f5ec514a1580a2937bd833979d933199fc230e204c6cdc58872b7d46f75,f0473484a9d3f348a15f196fa805e0cd4c87d668f10f0b0a29835c50ba6826f2,1BY8GQbnueYofwSuFAT3USAhGjPrkxDdW9,94,75,246295203348800028,6,1|9|99|13989|948475665|1219619442889887710
68,68,219898266213316039825,1fe02f1d740637a7127cdfe8a77a8a0cfc6435f85e7ec3282cb6243c0a93ba1b,f939fb5729f35b2f7464cfacd80481da04c1cc35e3f2769aec334f41766836b,1MVDYgVaSN6iKKEsbzRUAYFrYJadLYZvvZ,202,99,309954402760246678,7,1|3|12|201|51465|5106401061|49191317529892137642
69,69,297274491920375905804,4babadccc6cfd5f0e5e7fd2a50aa7d677ce0aa16fdce26a0d0882eed03e7ba53,d2cadbc2264032203cec6a0d89859e3d0880b39649fc81654aa4e077fb4d0f3e,19vkiEajfhuZ8bs8Zu2jgmC6oqZbWqhxhG,139,1,447651822855286916,5,1|2|277|132798|3111765403119
70,70,970436974005023690481,90e6900a58d33393bc1097b5aed31f2e4e7cbd3e5466af958665bc0121248483,d7319f127105f492fd15e009b103b4a83295722f28f07c95f9a5443ef8e77ce0,19YZECXj3SxEZMoUeJ1yiPsw8xANe7M7QR,191,123,577582325950244303,6,1|5|45|4345|56847134|3376427815594743
75,75,22538323240989823823367,726b574f193e374686d8e12bc6e4142adeb06770e0a2856f5e4ad89f66044755,9b15322e6707090a4db3f09c7e6632a26db57f03eb07b40979fc01c827e1b0a3,1J36UjUByGroXcCvmj13U6uwaVv9caEeAt,88,17,21477598146493296024,7,1|2|10|292|109813|13350426017|686889670235584758355
80,80,1105520030589234487939456,7e1238f7b1ce757df94faa9a2eb261bf0aeb9f84dbf81212104e78931c2a19dc,625c7118f1c29cb92d28ce0dfd0dc58144fe5572effebc7fee54c4fce3333a6b,1BCf6rHUW6m3iH2ptsvnjgLruAiPQQepLe,76,63,822138434906558680576,5,1|11|186|397285|4409830235019
85,85,21090315766411506144426920,29c4574a4fd8c810b7e42a4b398882b381bcd85e40c6883712912d167c83e73a,e02c3afd79913ab0961c95f12498f36a72ffa35c93af27cee30010fa6b51c53,1Kh22PvXERd2xpTQk3ur6pPEqFeckCJfAr,166,15,56756379656069974216976,6,1|2|22|3537|15420158|872663496651264
90,90,868012190417726402719548863,5c38bd9ae4b10e8a250857006f3cfd98ab15a6196d9f4dfd25bc7ecc77d788d5,a84963ebff4abefe121a0d3c6bf9203faaef25898cda62686efbf64d1c6fb433,1L12FHH2FHjvTviyanuiFVfmzCy46RRATU,256,103,883695212199751811710720,7,1|3|28|828|694185|8455115513415|88424288520384305349937444
95,95,25525831956644113617013748212,967a5905d6f3b420959a02789f96ab4c3223a2c4d2762f817b7895c5bc88a045,9da9709f8e830ba5cea1d0426a261f0b9b5dda057478d8e6009ad7c4a8af6916,19eVSDuizydXxhohGh8Ki9WY9KsHdSwoQC,142,41,20297184129311288683481768,8,1|2|6|44|2362|5712914|34127756371721|3601280114284742617888361378
100,100,868221233689326498340379183142,d2063d40402f030d4cc71331468827aa41a8a09bd6fd801ba77fb64f8e67e617,875561c0bd6298fbf187053d33ffde9672edf2830e2cb961582431369fd53765,1KCgMv8fo2TPBpddVi9jqmMmcne9uSNJ5F,73,27,2379952090635695987479899434,6,1|3|54|3579|92499661|8655422842435108
105,105,29083230144918045706788529192435,bcf7ce887ffca5e62c9cabbdb7ffa71dc183c52c04ff4ee5ee82e0c55c39d77b,506c02f3b5c15c12deb94ba16d02bd9710eeaf3b25adf89cc5012ed9c44c31f,1CMjscKB3QW7SDyQ4c3C3DEUHiHRhiZVib,53,23,51932196870529760199050538161,7,1|3|19|427|1534682|2534139426972|25144672676023312372358838
110,110,1090246098153987172547740458951748,9976ba5570966bf889196b7fdf5a0f9a1e9ab340556ec29f8bb60599616167d,2ef58f7eef3ebbc285602744ad51753bad939c214ff6a465c384377abdea7b9,12JzYkkN76xkwvcPT6AWKZtGX6w2LAgsJg,203,138,1695669787631638921092865801748,6,1|6|152|58011|3537281290|12807611373238384618
115,115,31464123230573852164273674364426950,48d313b0398d4923cdca73b8cfa6532b91b96703902fc8b32fd438a3b7cd7f55,66f0742c24f5ff80c799d691d756ad8e5aa7f6d8f986abd9eeef45514637c0d4,1NLbHuJebVwUZ1XqDjsAyfTRUPwDQbemfv,134,69,47463766616155645909345506493348,6,1|4|133|21015|537211736|2444170042218326431
120,120,919343500840980333540511050618764323,ceb6cbbcdbdf5ef7150682150f4ce2c6f4807b349827dcdbdd1f2efa885a2630,2b195386bea3f5f002dc033b92cfc2c9e71b586302b09cfe535e1ff290b1b5ac,17s2b9ksz5y7abUm92cHwG8jEPCzK3dLnT,227,87,2179352670743667798300026445402889,6,1|3|40|33912|9045603996|133391003134953761827
125,125,37650549717742544505774009877315221420,33709eb11e0d4439a729f21c2c443dedb727528229713f0065721ba8fa46f00e,2a1c304a39a77775d3579d077b6ee5e4d26fd3ec36f52ad674a9b47fdd999c48,1PXAyUB8ZoH3WD8n5zoAthYjN15yN5CVq5,209,161,64844038510165883769732500758613140,7,1|8|98|22772|521750219|707776751114737680|733367170088229447119341826361569421
130,130,1103873984953507439627945351144005829577,633cbe3ec02b9401c5effa144c5b4d22f87940259634858fc7e59b1c09937852,b078a17cc1558a9a4fa0b406f194c9a2b71d9a61424b533ceefe27408b3191e3,1Fo65aKq8s8iquMt6weF1rku1moWVEd5Ua,209,130,1781917113223345927405449641628985575,7,1|5|90|8881|103582255|12971283389441456|1244355421832707119626398331138081
```

Row count = 82 (puzzles 1–70 then 75,80,85,…,130). All reproduce their on-chain
`X,Y` under exact scalar multiplication.
