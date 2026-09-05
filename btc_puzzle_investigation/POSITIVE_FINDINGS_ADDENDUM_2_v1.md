> **⛔ FROZEN — NOT CURRENT.** This file is a historical snapshot. The single current-state
> document is **`CLAIMS.md`**. Do not read status, grades, or open items from here; do not
> write a successor version of this file. (Frozen 2026-09-01.)

# secp256k1 — Positive-Findings ADDENDUM 2 (v1, 2026-07-27)

**This document is ADDITIVE. It supersedes nothing.** It records only what was found **after**
`POSITIVE_FINDINGS_ADDENDUM_1_v1.md` (2026-07-23) — i.e. the 2026-07-25 → 2026-07-27 sessions — and is
read **alongside** `POSITIVE_FINDINGS_MASTER_v4.md` (2026-07-20) and Addendum 1, not in place of either.
Every Part, ledger row, frontier and retraction of v4 and of Addendum 1 stands unless a numbered entry
below names the artifact that changes it.

**Why an addendum and not a v5.** Same reason as Addendum 1: the consolidation step is the measured
lossy step on this project (`DEGRADATION_AUDIT_H3_TO_MASTER_v1.md`: live frontiers 5→0 across one
master rebuild, invisible to tag counts; and `SYNTHESIS_..._ADDENDUM_1_v1` reproduced it at small
scale — ~10 of ~30 generated items died at the compression step). An additive document cannot lose a
predecessor item, because it does not restate one.

**Reading order:** `POSITIVE_FINDINGS_MASTER_v4.md` → `POSITIVE_FINDINGS_ADDENDUM_1_v1.md` → this file
→ the named `RESULT_*` / `ANALYSIS_*` artifact.

---

> ## ⚠ ALL FOUR v4 BANNERS APPLY VERBATIM AND ARE NOT RESTATED
> The **SCALE BANNER** (nothing measured at `p ≈ 2²⁵⁶`; ~239 binary orders of gap; a `[VERIFIED]` or
> `[EMPIRICAL]` row has **no power** against structure at cryptographic scale), the **LANGUAGE RULES**
> (`secure` / `closure` / `proven hard` / `unbreakable` forbidden; `flat` / `generic` is a statement
> about one statistic in one basis, never a verdict of absence), the **COMPILE RULE**, and the
> **ANOMALY-DRILL RULE** (output = characterization, never a verdict; every bound carries power and
> scope; a drill ends in a sharper law / bounded magnitude / next probe — never a closure) govern every
> line below.
>
> **The two proved-at-scale results of Addendum 1 (§A1.1 `A_new` supersingular, §A1.2 the amicable
> pair) are unaffected.** Nothing new here is measured at secp scale except the `S_diff` and `E3`
> difference-set nulls on the real 82 keys (§B4.3, §B3.4), which are scoped to their statistic families,
> not to curve size.

---

## 0. Source artifacts (2026-07-25 → 2026-07-27)

| artifact | object |
|---|---|
| `RESULT_n1_120deg_exact_v1.md` (+ PREREG `..._ideal_v4` + DEVIATIONS) | the 120° law `α₂/α₁=ζ₃` upgraded to an exact identity, 22 primes |
| `ANALYSIS_n1_cap_anew_channel_kronecker_route_v1…v3.md` | `V(a)` = the `A_new` channel; the route from ideal-equality to uniformity |
| `RESULT_stickelberger_citation_verified_v1.md` | the Stickelberger citation discharged (Katre), three caveats |
| `RESULT_anew_twisted_eigenvalues_nonabelian_v1.md` | the `a≠0` eigenvalues are non-abelian ⇒ the `ζ₃` is geometric |
| `RESULT_n1_v_sign_mechanism_v1.md` | the exact identity `V₂=V₁²±2p`, `v=u²−3/4`, the sub-Weil restatement |
| `RESULT_n1_v_sign_route_refuted_v1.md` | `v≤0` is false — exact counterexamples; route closed, inequality not refuted |
| `RESULT_n1_phase_inequality_reduction_v1.md` | `S_y≤2` reduces to the sign of one L-polynomial coefficient |
| `RESULT_jacobi_sign_law_stickelberger_v1.md` (+ `_semiprimitive_v1`, spec `VERIFY_SPEC_...`) | the `J(χ₃,χ₄)=∓p` sign law, both halves |
| `RESULT_ideal_level_symbol_collapse_v2.md` | the `ℓ≥5` CM ideal-level route collapses to a rational symbol |
| `RESULT_twist_orbit_spectrum_v1.md`, `_forced_landscape_v1.md`, `_magnitude_v1.md`, `_monodromy_v1.md` (+ PREREGs + DEVIATIONS) | the twist-orbit spectrum drill: forced landscape, magnitude null, `E[u⁴]` monodromy |
| `RESULT_diffset_cubic_v1.md`, `_secondcontrol_v1.md`, `_beta2_characterization_v1.md` (+ PREREGs) | cubic difference-set energy `E3` on the real 82 |
| `RESULT_diffset_sdiff_v1.md` (+ PREREG) | `S_diff` on the real 82 |
| `RESULT_literature_sweep_v1.md` | Silverman–Stange bridge published; Cap Law Thm A steps classical; amicable framing narrowed |
| `SYNTHESIS_curve_structure_and_new_directions_v1.md`, `SYNTHESIS_brainstorm_seven_cycles_v1.md` (+ `ADDENDUM_1_v1`) | structure maps and directions — nothing run, nothing promoted (their load-bearing items became the proofs above) |

---

# PART B1 — NEW PROVED / EXACT RESULTS

## B1.1 The 120° law is an EXACT identity — `α₂/α₁ = ζ₃` at every cell of 22 primes `[PROVED — exact, at the stated cells]`

`RESULT_n1_120deg_exact_v1.md` (executes `PREREG_n1_120deg_exact_ideal_v4.md`, gate-signed-off; freeze
SHA-256 `a964f246…`, written by point-counting **before the first `V₁`**; no-float multi-modular path).

- **Statistic:** `g(p,a) = deg gcd(L*(T), L*(ζ₃T))`, with `g = 2 ⟺` two of the four Frobenius
  eigenvalues of `H¹_c(E, L_{χ₂(y)} ⊗ L_{χ_a})` differ by exactly a primitive cube root of unity.
- **Result:** `g = 2` at **every census-surviving cell** of **22 primes** — 7 in-sample (`p≡7 mod12`,
  `≤547`), **10 out-of-sample stratum-S (`p≡7 mod12`, `>547`, secp's class)** totalling 2464 cells, and
  5 cross-stratum C (`p≡1 mod12`). No census exclusions, no repeated roots, no cell with `g≠2`. This
  **upgrades the law from `[VERIFIED-numeric, 9.5×10⁻⁴⁰]` to an exact identity** at those cells.
- **Controls all fired:** PLANT-A/PLANT-Z (planted positives) → `g=2`; **PLANT-B/PLANT-U1 (planted
  negatives) → `g=0`** (statistic not vacuous); C-NOFLOAT (AST) pass; an independent Sage `O(p⁴)` route
  confirms all four eigenvalues weight-1 `|α|=√p` to `2.2e-16` `[CONFIRMED-independent]`.
- **Scope (carried verbatim):** this establishes the **premise** of the cap route (that `α₂/α₁` is
  exactly `ζ₃`). It does **not** establish the cap `|V|≤2√p` (that additionally needs purity at every
  embedding + order-pinning + uniformity), does **not** establish uniformity (per-cell at 22 primes; no
  finite sweep gives all `a`, all `p`), and every cell is `p≈10³` (banner #5).

## B1.2 The N1 mechanism: one exact identity generates the ½-saturation and the 120° law `[PROVED — exact]`

`RESULT_n1_v_sign_mechanism_v1.md` (`n1_vsign_mechanism_v1.py`; integer-vector, no float).

- **`V₂ = V₁² + 2p` (SIN, `p≡3 mod4`, secp's stratum) / `V₂ = V₁² − 2p` (COS)** — exact integer-vector
  identity in `ℤ[x]/Φ_n`, every non-constant component exactly zero, verified at 10 primes. **⇒ `V₂` is
  completely determined by `V₁`; the whole `k=2` field enumeration the pipeline is built around is
  redundant.**
- **`v = u² − 3/4` exactly** (357/357 classes over 8 primes, max dev `1.4×10⁻⁶⁰`), i.e.
  `s₁²+s₁s₂+s₂² = 3/4` = the **Eisenstein norm form** of the `j=0` curve; solving gives `u = cos t`,
  `s₁ = cos(t−60°)`, `s₂ = cos(t+60°)` — **the two Frobenius half-angles differ by exactly 120°.** One
  fact generates the rest.
- **Positive residue — forced bounds nobody had stated:** `v ∈ [−3/4, +1/4]`, both endpoints forced;
  **`max_a v ≤ 1/4` is UNCONDITIONAL.**
- **The rate is a suppression, and the suppression is the content:** `v>0` occurs at ~4.8% of classes vs
  ~9.1% for a Gaussian at the same threshold — lighter-tailed, as Sato–Tate should be. (Correcting the
  earlier "generic" label; see R-B5.41.)

## B1.3 `S_y ≤ 2` reduces to the SIGN of one L-polynomial coefficient — it was a sub-Weil bound `[PROVED — algebra]`

`RESULT_n1_phase_inequality_reduction_v1.md`.

- The `α↦−ᾱ` pairing factors `L(t)=(1−At−pt²)(1−Bt−pt²)`; with `u,v` the sum/product of the two
  half-sines, `e₂ = −2p − 4p·v`, and weight-1 gives `|u|≤1+v` for free. **Hence `v ≤ 0 ⟹ S_y ≤ 2`, and
  `v ≤ 0 ⟺ e₂ ≥ −2p`** ⇒ the whole open inequality follows from the **sign of the `t²`-coefficient** of
  the twisted L-polynomial — the record's named "middle coefficient" attack made exact, and a **sign**
  target reachable by integrality, not a magnitude over millions of cells.
- Combined with B1.2: **`v ≤ 0` at every class ⟺ `|V₁(a)| ≤ √3·√p` for every `a≠0`** — a **sub-Weil
  bound** (Weil allows `2√p`; this demands never exceeding 86.6% of the Weil bound). Largest observed
  `1.932√p` at `p=547`. It was never a statement about signs of sines.
- ⚠ **Attribution correction carried from `SYNTHESIS_..._v1`:** `RESULT_n1_v_sign_mechanism_v1.md §3`
  sourced `v ≤ +1/4` to "Weil `|u|≤1`". Weil/purity gives `|u|≤2` (`|V₁|≤4√p`); the `1/4` endpoint comes
  from the pairing + weight-1, not from Weil. Labelling it "Weil" made the open cap look already-had.

## B1.4 The `v ≤ 0` route to `S_y≤2` is FALSE — exact counterexamples; the route is closed, the inequality is NOT refuted `[PROVED — exact]`

`RESULT_n1_v_sign_route_refuted_v1.md` (three independent count implementations agree).

- **Exact rational counterexamples, no float:** `p=127` gives `v ∈ [21/127, 85/508] > 0`; `p=163`,
  `p=211` likewise. Adjudicated four ways (2nd count implementation; exact Descartes/Sturm; μ₆-coset
  product; and the forced identity `e₃=∓p·e₁` holding exactly at 13/43/127/163/211 via a third
  implementation).
- **`v>0` is generic-rate (~4–6% of μ₆ classes) in BOTH strata** — the two frozen references `p=13`
  (`d=1`) and `p=43` (`d=5`) were simply too small to exhibit one (`P(none at d=5)≈0.79`); the
  conjecture had never been tested where it could fail.
- ⚠ **`S_y ≤ 2` is NOT refuted** — `v≤0` was **sufficient, not necessary**. The exceptional classes were
  **located, not characterized**; the inequality stays open (see frontier #27).

## B1.5 The Jacobi sign law `J(χ₃,χ₄) = ∓p` — PROVED, both halves `[PROVED — modulo (D2); (D2) now discharged, see B2.1]`

`RESULT_jacobi_sign_law_stickelberger_v1.md` (spec `VERIFY_SPEC_jacobi_stickelberger_v1.md` frozen
pre-run; exact `ℤ[ζ₁₂]` 4-vectors, no float).

- **Theorem.** For `p≡3 mod4`, any order-3 `χ₃` and order-4 `χ₄` of `F_{p²}^×`:
  `J(χ₃,χ₄) = −p` if `p≡1 mod3` (`p≡7 mod12`, **secp's class**); `J(χ₃,χ₄) = +p` if `p≡2 mod3`.
- **Route:** Stickelberger gives `(J)=(p)` (kills the `π²` competitor — Frobenius could not, because it
  constrains the field and `π²` differs in the **ideal**) → Kronecker ⇒ `J=ζp`, `ζ∈μ₁₂` → reduction mod
  the prime above 2 forces the `μ₃` part trivial (the rationality) → mod the prime above 3 fixes the
  sign. Uses neither (S) nor Frobenius ⇒ discharges the earlier unverified-(S) dependency on the
  `p≡11` half as well.
- **Verified** at 28 primes × 4 char pairs (info unit = 28, the 4 pairs are Galois conjugates), 4807
  primes for the digit lemmas, **all 5 firing controls fire** (FC5 rejects a planted `π²`; FC4 pins the
  normalization by reproducing the classical cubic `(0,1)`). At secp's own `p`: profile `(1,1,1,1)`,
  `J=−p`.
- **Consequence:** **`m=1` at secp moves from `[CONDITIONAL]` toward `[PROVED]`** — the one open input
  (D2) was Stickelberger's citation, now **discharged** (§B2.1). ⚠ **The in-file grade move is offered,
  not yet applied**, and the three Katre caveats of §B2.1 travel with it. ⚠ **Novelty is DOUBTED, not
  claimed** — semiprimitive / uniform-cyclotomy is classical.

## B1.6 The `ℓ ≥ 5` ideal-level CM route COLLAPSES to a rational symbol — forced algebra, not a null `[PROVED — forced, derived before running]`

`RESULT_ideal_level_symbol_collapse_v2.md` (scripts `ideal_symbol_{build,structure,units,reduction}_v1.py`).

- With `3∣n−1` (L3), `n` splits in the CM ring, `ℤ[ω]/(ν)≅F_n`, `p=ππ̄`. Three forced degeneracies
  (each derived before running ⇒ the counts are instrument checks): `π≡1 mod ν` ⇒ `χ_ℓ(π mod ν)=1`
  identically (250/250); the full-orbit ideal symbol `=1` forced; and **`π̄ ≡ t−1 (mod ν)` element-wise
  (250/250)** ⇒ **both bridge sides are symbols of the SAME rational `U=|t−1|`.** No ideal-level content
  in the CM route — because the elements reduce to rationals, not because a test came back null.
- **Why `ℓ=3` escapes** (and stays a live control on the same code, 63/200): its correction is carried
  by the primarizing units `μ₆` + the ω-supplement; `gcd(6,ℓ)=1` at `ℓ≥5` forces `χ_ℓ(u)=1` (200/200).

## B1.7 The twist-orbit "Arm II" dissolves to an exact, curve-independent frame identity; the forced 2nd/3rd-order landscape `[PROVED — forced, exact]`

`RESULT_twist_orbit_forced_landscape_v1.md`, `RESULT_twist_orbit_spectrum_v1.md §Arm II`.

- **Arm II (spectral-dilution) DISSOLVED:** the frame Gram `⟨f_a,f_b⟩ = nI − J` **exactly**,
  curve-independent (`|f_a(P)|=1` annihilates the `χ₂` sign; verified `p=43,67`). **The dissolution is
  positive — it LOCATES the object:** the curve signal lives in the **values `V(a)`**, not the
  unit-modulus frame. Also forced: Parseval `Σ_{a}|V(a)|² = n(n−1)` (6 primes).
- **Forced 2nd/3rd-order objects** (`[PROVED — exact]`, curve-independent): the 2-pt **additive**
  autocorrelation `Σ_a V(a)V̄(a+b) = n(nδ_b − 1)` (5 primes); the 3-pt **multiplicative** bispectrum
  `≡ 0` forced by odd parity (odd·odd = even ⇒ vanishes); the multiplicative autocorrelation is the
  Wiener–Khinchin dual of the (null) signed spectrum. **The one free 2nd-order object is the magnitude
  `|V(a)|²`** (even, `μ₃`-trivial chars) — tested in §B4.2.

---

# PART B2 — CITATIONS DISCHARGED AND MECHANISM IDENTIFICATIONS

## B2.1 The Stickelberger citation is VERIFIED (Katre) — a three-times-failed debt discharged `[CITED — verified, three caveats]`

`RESULT_stickelberger_citation_verified_v1.md` (`citation-verifier` run, isolated context, Katre's text
verbatim in hand; corroborated against Michigan L9 and Wikipedia).

- **Classical Stickelberger supports the intended use** — prime-ideal factorization of Gauss/Jacobi
  sums over `ℚ(ζ_m)` for **`m=12` (composite, not a prime power)** and **residue degree `f=2`**
  (`q=p²`, forced when `p≡3 mod4`). The `[UNVERIFIED CITATION]` on (D2) — which had killed **three**
  prior citation-verifier runs — moves to `[CITED — verified]`.
- **Three load-bearing caveats travel with the promotion:** (1) cite the **proof's** hypothesis
  `j,k,j+k ≢ 0 (mod m)`, not the printed `jk(j+k)≢0` (which our `(4,3),m=12` violates precisely because
  12 is composite); (2) use the `F_q` digit-sum form, **not** the `ℓ≡1 mod m` (`f=1`) packaging; (3)
  **Stickelberger gives the IDEAL, not the value** — the residual root of unity is pinned separately by
  Kronecker + reductions mod the primes over 2 and 3.
- **Moves (offered, not yet applied in-file):** `RESULT_jacobi_sign_law_stickelberger_v1.md` (D2)
  `[UNVERIFIED] → [CITED — verified]`, hence B1.5's `m=1` at secp toward `[PROVED]`.
- **Honesty note carried from the verifier:** verified against Katre + Michigan L9 + Wikipedia; did
  **not** open Ireland–Rosen Ch. 14, Washington §6, or Lang — the natural next textbook if a canonical
  citation is wanted.

## B2.2 The `a≠0` twisted eigenvalues are NON-ABELIAN ⇒ the `ζ₃` is GEOMETRIC — the route is redirected, not closed `[VERIFIED — p=43,67; plant-validated]`

`RESULT_anew_twisted_eigenvalues_nonabelian_v1.md` (exact number-field computation, Sage; plants
correctly classified in each field used).

- **Question (fork 1):** are the `a≠0` Frobenius eigenvalues Jacobi-sum / Hecke-character values (so
  Stickelberger would govern the uniformity)? **Answer: NO, generically.** Their splitting field is not
  even Galois over `ℚ` (Kronecker–Weber criterion: `σ(D)/D ∉ (K*)²` at a generator, `p=43` and `p=67`,
  both quadratics). So they are **not cyclotomic, not Jacobi/Gauss sums**; classical Stickelberger does
  not factorize them. `p=13` (`n=7`) is a small-case exception.
- **The coherent picture:** the individual `a≠0` eigenvalues are **GL(2)/big-monodromy type, not
  GL(1)/Hecke** — the signature of a genuine 4-dim deformation whose `a=0` fiber is the CM/abelian
  degenerate case (`√p·μ₁₂`). **The `α₂/α₁ = ζ₃` ratio is cyclotomic even though the eigenvalues are
  not** ⇒ the 120° law's cube-root ratio is **not an arithmetic fact about the eigenvalues but a
  relation within the GL(2) structure — a monodromy / geometric fact.** This is exactly why every
  eigenvalue-arithmetic (Stickelberger) attempt was aimed at the wrong object.
- **Route consequence (updates `ANALYSIS_..._v3 §4`):** **L-Stick (Stickelberger on the `a≠0`
  eigenvalues) is retired for the uniformity problem** — its premise is false — but **not wasted**: the
  verified citation (B2.1) stands for what it governs (the `a=0` supersingular anchor and the separate
  Jacobi sign law). **L-mono (geometric monodromy) is now the primary route** to uniform `u=ζ₃`, with
  the ω-descent (§4b) a live **ingredient** (it constrains the monodromy group to contain/commute with a
  genuine `μ₃`), not the lever. **Refuting the mechanism did not touch the proved per-cell fact (B1.1);
  it identified the mechanism behind it.**

## B2.3 The `A_new` channel: `V(a)` is `A_new`'s Frobenius trace twisted by the Lang torsor — the cap is the arithmetic value of a *relative* rigidity `[structural analysis; the framing is exact, the mechanism is B2.2]`

`ANALYSIS_n1_cap_anew_channel_kronecker_route_v1…v3.md`.

- **The framing is exact and the record already contained its `a=0` consistency check.** `C→E` is the
  double cover `w²=y`, so `H¹(C) = H¹(E) ⊕ H¹(E, L_{χ₂(y)})` with `6 = 2+4` and
  `H¹_c(E, L_{χ₂(y)}) = H¹(A_new)` exactly. Lefschetz + the proved (L1) sum-`=0` at `p≡3 mod4` = a
  supersingular surface's zero trace — two independent parts of the record agreeing at `a=0`. `L_{χ_a}`
  is totally unramified ⇒ `dim H¹_c` stays 4 ⇒ **`{V(a)}` is the orbit of `H¹(A_new)` under the twist
  group `E(F_p)^ ≅ ℤ/n`.**
- **Rigidity budget — what survives the twist:** purity `|α|=√p` **yes** `[PROVED all p]`; `α↦−ᾱ`
  closure **yes** `[PROVED-forced]`; each `α` = `√p`×root-of-unity **no** (the absolute angle goes free,
  equidistributing Sato–Tate); **the RATIO of the two pairs is a root of unity — yes** (the 120° law,
  now B1.1). ⇒ **absolute rigidity is destroyed, relative rigidity survives, and the `2√p` cap is the
  arithmetic value of the relative rigidity.** This accounts for the `½` saturation the master flagged
  as "one measured anomaly with no account": additive `bx+cy` has 4 free eigenvalues; `χ₂(y)` has 2 free
  × `{1,ζ₃}` ⇒ **`½ = 2/4`.**
- **Downstream of B1.1:** since `ζ₃` is a unit, `α₂=ζ₃α₁` gives the ideal equality `(α₁)=(α₂)`
  immediately at every tested cell (the hypothesis that carried the whole Kronecker chain now *follows*
  from the run), and the order is pinned `=3` there. **The sole remaining structural gap is uniformity**
  (frontier #26).

## B2.4 Literature: the `p ↔ #E(F_p)` bridge is published, the Cap Law's steps are classical, and the amicable framing narrows `[CITED — classical]`

`RESULT_literature_sweep_v1.md` (3 of 5 targets discharged; items 3–4 not reached ⇒ that ledger item
stays open).

- **Silverman–Stange arXiv:0912.1831 Thm 19(a)–(d), Rmk 20, Prop 23** is the correct citation for the
  `p↔#E` bridge (B1); Prop 23's proof contains the record's own primarize-then-cubic-reciprocity
  manoeuvre verbatim. The record's `[VERIFIED — classical]` + "no originality claimed" both stand; the
  pointer improves.
- **Cap Law Thm A steps 1+3 are classical** (Gauss automorphs ↔ Pell; disc `−3` has exactly six) ⇒
  regrade to `[PROVED — classical input]`. ⚠ **Lemma C** (flap `= {|u−v|>½}` for the half-open
  parallelogram) **NOT located** — the Eisenstein-lattice literature concerns the Voronoi hexagon, a
  different domain; Lemma C keeps its standing.
- ⚠ **Amicable framing narrowed (bears on Addendum 1 §A1.2 — the FACT stands):** the Pallas/Vesta
  "Pasta" curves are a published, deliberately-constructed, deployed 254-bit `j=0` amicable pair
  (`y²=x³+5`). Any phrasing that "a named crypto curve being amicable is unremarked" is wrong; defensible
  residue is "secp's own instance not located in a bounded search". (See R-B5.45.)

---

# PART B3 — NEW MEASURED LAWS AND CHARACTERIZATIONS

## B3.1 4th-moment monodromy: `E[u⁴]` is consistent with full SU(2) and EXCLUDES the 3/8 (torus/CM) reduction `[EMPIRICAL — scoped, 12 primes out-of-sample]`

`RESULT_twist_orbit_monodromy_v1.md`.

- `u = V/(2i√p)`; `E[u⁴] = n·Σ_j R(j)²/(16p²(n−1))` is an **exact rational** (`R` = autocorrelation of
  the `y`-Legendre sequence; no signal-path float). Full SU(2) predicts `1/8`, torus/CM predicts `3/8`.
- **Out-of-sample:** 12/12 primes in the iid-SU(2) band, pooled deviation `+0.00008`, 6/6 above/below ⇒
  **consistent with full SU(2), excludes the `3/8` reduction.** The finite-`p` concern (in-sample 7/7
  below `1/8`) **resolved by the data** — the deficit vanishes out-of-sample (large-`L` half `−0.0004`,
  `1/√L` intercept `≈0`) ⇒ finite-size, not a reduction.
- ⚠ **NOT a proof of SU(2)** — matches two moments (one forced); a reduction too small to move `E[u⁴]`,
  or higher-moment / larger-`p` structure, is not excluded. Direction is consistent with the `A_new`
  channel picture (the twist frees the absolute angle toward Sato–Tate; the relative 120° stays frozen).
  ⚠ **Discipline gap logged:** the `experiment-designer` sign-off did not complete (session cap) — the
  prereg + controls were validated but no independent verdict was issued; retroactive sign-off advisable.

## B3.2 `μ₃`-invariance is CM-specific — the twist-orbit null is structure beyond a class-machinery artifact `[VERIFIED]` (C-JZERO)

`RESULT_twist_orbit_spectrum_v1.md`. `j=0` (our `x³+7`) = 100% `μ₃`-trivial spectral energy; `j≠0`
≈ ⅓. So the `μ₃`+odd symmetry that the nulls of §B4.1/§B4.2 sit "subject to" is a real CM property of
this curve, not an artifact of the class machinery.

## B3.3 §XI.17 row-budget: a `char − MN − μ₆` layer EXISTS; and a reproducible instrument over-dispersion `[EMPIRICAL — seen-data, control-repaired]`

`RESULT_row_budget_lowtail_v3.md` (first verdict in three specs; `PREREG_..._v3.md` + DEVIATIONS).

- **Gate passes; Arm A pooled `Z=+70.50` (raw `+66.87`), sign 10/10** ⇒ a `char−MN−μ6` layer **exists**.
  **A3′ passes including its unseen `{211,349,577}` subset** (`Ĉ=−0.746±0.128` vs F11's `−0.4950`),
  superseding v2's "A3 FAILED" — the log-log slope was underpowered by construction; the right instrument
  is the constant `C=(n−1)·layer`, inverse-variance weighted.
- ⚠ **New instrument finding:** carrier-vs-replicate `z` scale is **over-dispersed across primes by
  ≈1.55×, reproducibly in two independent draws** — a global mild mis-scaling, not one prime
  (`p=19231`'s `sd=1.37` was a draw; 1.106 fresh). Next probe: raise `R`.
- ⚠ **§XI.17 still OPEN** — Arm A shows a layer exists, it does **not** decompose it.

## B3.4 The cubic difference-set energy `E3` on the real 82 keys: a pre-registered, non-artifact reject whose interpretation is OPEN `[EMPIRICAL — pre-registered reject, p≈0.03–0.04, NOT MC-corrected]`

`RESULT_diffset_cubic_v1.md`, `_secondcontrol_v1.md`, `_beta2_characterization_v1.md`.

- **Fired cell (pre-committed):** `E3(real)=13125` at the **98.4th percentile** of the matched known-MT
  null (two-sided `p≈0.033`), driven by a **+75 excess in cubic class `β²`**. **Reproduced against a
  second, generator-agnostic control** (uniform random valid curve points, no `d`, no PRNG): still a
  reject (98.1st pct, `p≈0.038`), the validity gate confirming bit-length is irrelevant to the null ⇒
  **not a null-estimation artifact.**
- **Characterization sharpened it, did not upgrade it:** the `+75` `β²` excess is **DIFFUSE** — a
  ~uniform `+2.3%` tilt across all pairs, **no band/bucket/key localizes it** (MC-corrected max|z|
  `p=0.21`, hottest key `p=0.47`, per-key dispersion at the 20th percentile = if anything *more* uniform
  than random).
- **Why this is not (yet) a finding, stated symmetrically:** it is **1 of ~7 statistics** this session
  (Bonferroni ×7 ≈ 0.23, non-significant); **no independent real replication exists** (n=82 fixed; the
  two nulls are the same distribution, so `p≈0.033` and `0.038` are one result expressed twice); and
  under the standard uniform-key assumption `E3(real)` is a null draw. **Interpretation is OPEN** — a
  real-vs-construction difference *could* be generation-side (off-limits per
  `feedback_no_prng_generation_side`) or curve-relevant; neither is demonstrated. No break, no leak, no
  closure, no impossibility claim. (The earlier "unliftable ceiling / generator-descriptive by
  construction" phrasing is retracted — R-B5.42.)
- **The one decidable firm-up (named, not yet run):** additional independent controls / additional
  solved keys; or a **group-law** joint object (`P_i ± P_j` via curve addition), which connects to the
  discrete log through curve arithmetic rather than describing `x`-coordinates. Its own prereg.

---

# PART B4 — NEW SCOPED NULLS  *(each with a fired firing-control; each a where-it-cannot-be map, not a closure)*

## B4.1 Twist-orbit single-character spectrum — no concentration beyond `μ₃`+odd `[EMPIRICAL — scoped, out-of-sample]`

`RESULT_twist_orbit_spectrum_v1.md` (prereg `_v2`, `experiment-designer` signed off; freeze SHA
`7cde99fe…`). **Is `a↦V(a)` multiplicatively concentrated beyond its forced symmetry?**

- **NULL:** 12 primes `p∈[823,2731]`, permutation p-values ~Uniform (min 0.029 at `p=2251` ≫ Bonferroni
  0.004; max-χ order inconsistent across primes = noise). No single-character concentration beyond the
  forced `μ₃` + odd (`V(−a)=−V(a)`, forced by `χ₂(−1)=−1`).
- **POWER + SCOPE:** PLANT-POS fires 4–6× (≈6% energy detectable) ⇒ scoped-real, not a power failure.
  This is a **magnitude bound, not a closure** — higher-order shape (2-pt/autocorr, additive/short-scalar,
  multiplicativity `V(a)V(b)/V(ab)`) is untested, each named as a next probe with its own prereg.
- ⚠ v1's prereg carried a load-bearing bug the gate caught (claimed `μ₆`-invariance; `V` is odd `μ₃`, not
  `μ₆`), fixed in v2 — **check a new symmetry claim against the record's own instrument before building on
  it.** Minor erratum logged: the signed run's in-sample reference set mixed `p≡1 mod12` primes; stratum S
  (all `p≡7 mod12`) unaffected.

## B4.2 Twist-orbit magnitude `|V(a)|²` — the one free 2nd-order object `[EMPIRICAL — scoped, out-of-sample]`

`RESULT_twist_orbit_magnitude_v1.md`. Everything else at 2nd/3rd order is forced (B1.7); the magnitude on
`(ℤ/n)^×/μ₆` (even `μ₃`-trivial chars, DC excluded) is the lone free object.

- **NULL out-of-sample:** 12 primes, min `p=0.050 @ 2647` ≫ Bonferroni; `experiment-designer` signed off;
  PLANT fires 4.9–10.9×.
- **★ Cross-check that strengthens both this and B4.1:** the signed-low prime (2251) `≠` the
  magnitude-low prime (2647) ⇒ **independent noise, not persistent structure.**
- **SCOPE:** through 2nd/3rd order the twist orbit is structureless *subject to* `μ₃`+odd+purity;
  combined with B3.1 (`E[u⁴]~SU(2)`), across the tested axes **no curve-specific structure is DETECTED
  beyond the forced CM symmetry** — a where-it-cannot-be map, not a "maximally generic" verdict. Untested
  (could still hold structure): **joint / coupled objects** (additive-multiplicative cross, short-scalar),
  **higher moments**, **larger `p`**.

## B4.3 `S_diff` on the real 82 keys — real ≡ known-MT on a joint object `[MEASURED — scoped null, n=82, secp P]`

`RESULT_diffset_sdiff_v1.md` (frozen before data).

- **NO REJECT:** `S_diff(real) = −35`, 30th percentile of the matched known-MT null, `p=0.59` — the
  recurring `real ≡ known-MT` pattern, now on a **joint** (pairwise) object rather than a marginal.
- **POWER + SCOPE:** rules out a frozen-orientation per-pair QR-bias above `ε≈0.034` (50% power) / `0.048`
  (80%); the planted control fired (`0.046→0.83` at `ε=0.05`). Scope: these 82 keys, secp P,
  ascending-bit ordering.
- **What stays open (the orthogonal subspace, invisible not bounded):** by `χ₂(−1)=−1`,
  orientation-**symmetric** difference-set structure is identically 0 in `S_diff`. The **`μ₃`-graded /
  cubic difference character** `χ₃(x_j−x_k)` (verified `χ₃(−1)=1` at secp ⇒ orientation-symmetric) probes
  exactly this blind subspace and is secp's own CM/Eisenstein direction — its own prereg (this is the E3
  line, §B3.4).

---

# PART B5 — RETRACTION LEDGER, CONTINUED  *(numbering continues Addendum 1 §A4; 1–38 are unchanged and not restated. Do not re-claim any of these.)*

39. **The two `A_new`-channel mechanism sketches** (the `μ₃`-equivariant-sheaf mechanism and the `μ₄`
    version) → **WRONG.** `[λ]*(L_{χ₂(y)}⊗L_{χ_a}) = L_{χ₂(y)}⊗L_{χ_{aλ}}`, equal iff `a(λ−1)≡0 mod n`;
    `n` prime, `λ≠1` ⇒ `a=0` only. The sheaf is `μ₃`-equivariant only at `a=0`; the same computation
    kills the `μ₄` version. **The framing (B2.3) survives; only the within-cell mechanism was wrong.**
    Withdraws `SYNTHESIS_brainstorm_seven_cycles_v1 §1.3` and `ADDENDUM_1_v1 §2.4`.
40. **`[REV §4b]` (the ω-descent) reframed as "the most likely source of the second input" / the
    order-pinning lever** → **WITHDRAWN.** `σ_λ` preserves the ratio `α₂/α₁` (a field automorphism
    permutes eigenvalues; a permutation cannot manufacture the value `ζ₃`). It is a symmetry the answer
    *has*, not a constraint that *produces* it — confirmed but insufficient. It is a live **ingredient**
    of L-mono (B2.2), not the lever. *Same category error as #39 — a group action relating cells,
    mistaken for a within-cell forcing; logged so it is not reached for a third time.*
41. **"`v>0` is generic" (`RESULT_n1_v_sign_route_refuted_v1 §4`)** → **WRONG.** Independent angles give
    ~50%, equidistributed `t` gives ⅓; the observed ~5% is a **suppressed** rate and the suppression is
    the content (B1.2). Naming the frequency and burying the mechanism is exactly
    `[[methodology_understand_exceptions_2026_05_28]]`, committed in the file reporting the exception;
    corrected in `RESULT_n1_v_sign_mechanism_v1`.
42. **The `E3` "unliftable ceiling"** — that `E3` is "generator-descriptive **by construction**", that
    "**no control** can move it", that a reject "says **nothing** about the curve" → **RETRACTED.**
    Unconditional impossibility claims, never proved = the null→closure / negative-bias failure mode this
    project tracks (`feedback_negative_bias_enlarge_nulls_2026_07_17`,
    `feedback_conditional_negatives_phrasing`). Supported instead (scoped): `E3` is a function of the
    pubkey-x set; the two controls tested give the same null; interpretation is **open**.
43. **The forced relation `e₃ = −p·e₁` stated unconditionally (prereg A6)** → **corrected to
    `e₃ = χ₂(−1)·p·e₁`** (sign is `p mod 4`-dependent; `−p·e₁` holds only for `p≡3 mod4`). This produced
    a **false stratum-C null caught mid-run** (first `g=0` sweep, would have fired "law is
    stratum-specific"); the independent Sage `V₁..V₄` route exposed it (B1.1 §5). Discrimination intact
    (PLANT-B still `g=0`).
44. **"9 of 12 out-of-sample" for the `G(χ₄)` sign rule** → **RETRACTED** — the record never names which
    three primes the rule was fitted to, so the count is unsupported. Supportable: 12 primes computed
    exactly, all agreeing (the bar the ledger demanded lifted is lifted; the OOS *count* is not claimed).
45. **"a named crypto curve being amicable is unremarked" (framing on Addendum 1 §A1.2)** → **NARROWED.**
    The Pasta (Pallas/Vesta) curves are a published, deliberately-constructed 254-bit `j=0` amicable
    pair. **The FACT (secp is an amicable pair, §A1.2) stands unchanged**; only the "unremarked /
    unremarkable" framing was wrong. Defensible residue: secp's own instance not located in a bounded
    search (weak evidence).

---

# PART B6 — FRONTIER LEDGER DELTA  *(v4 §XI and Addendum 1 frontiers stand unless named here; new items continue the numbering from #26)*

**Status changes to existing frontiers:**

- **Frontier 15 (the Jacobi sign law `J(χ₃,χ₄)=∓p`, was `[EMPIRICAL 12/12]`)** → **PROVED, both halves**
  (B1.5), and its single external input — **Stickelberger's citation — is now VERIFIED** (B2.1). ⇒ **the
  whole "remaining gap between the measured `m`-law and a scale-free one" is discharged in substance**;
  `m=1` at secp moves `[CONDITIONAL] → [PROVED]` **once the offered in-file grade moves are applied and
  the three Katre caveats are attached.** The sub-items frontier 15 listed (the `G(χ₄)` fitted rule, the
  norm-lift step) are resolved (B1.5, R-B5.44). ⚠ Novelty is doubted, not claimed.
- **§XI.10 (the mechanism of the `½` saturation, N1)** → **major advance, still open on one axis.** The
  `½` now has an account: `½ = 2/4` from the rigidity budget (B2.3); `v = u² − 3/4` and the 120° law are
  exact (B1.2, B1.1); the anomaly's home is the `A_new` channel's *relative* rigidity. The candidate
  mechanism is now precise — a **geometric monodromy `μ₃`** (B2.2), the eigenvalue-arithmetic reading
  having been ruled out (non-abelian `a≠0`). Remaining: **uniformity** (→ #26).
- **The N1 inequality `S_y ≤ 2`** (Addendum 1 §XI.10 sub-thread) → **retyped, still open.** Reduced to a
  **sign** of one L-coefficient / a sub-Weil bound `|V₁|≤√3√p` (B1.3); the `v≤0` route is **dead** (exact
  counterexamples, B1.4) but the inequality is **not refuted** (`v≤0` was sufficient, not necessary).
  `max_a v ≤ 1/4` is unconditional. (→ #27.)

**New frontiers:**

26. **Uniform `u = ζ₃` (all `a`, all `p ≡ 7 mod12`, ⊇ secp) via geometric monodromy (L-mono)** — the
    **sole remaining structural gap** of the cap-via-relative-rigidity programme. Per-cell is `[PROVED]`
    at 22 primes (B1.1); no finite sweep gives uniformity. Target: identify the `μ₃` in the
    geometric/arithmetic monodromy group of `L_{χ₂(y)}⊗L_{χ_a}` on `H¹_c` that forces the between-pair
    ratio to a primitive cube root uniformly in `a`. **Ingredient available:** the ω-descent (`L*(a)`
    over the index-3 subfield `ℚ(ζ_n)^{⟨σ_λ⟩}`, confirmed exactly) constrains the monodromy group.
    L-Stick is retired for this (B2.2); this is the primary route.
27. **`S_y ≤ 2` as an exact sign / a sub-Weil bound.** Prove `|V₁(a)| ≤ √3·√p` for every `a≠0` (Weil
    gives `2√p`; largest observed `1.932√p @ p=547`). Candidate next objects: derive `v=u²−3/4` from the
    `μ₆` action (currently `[PROVED-exact]` by verification, **not derived**); a measure of the
    exceptional `a`-set (located, not characterized, B1.4); or tolerate `v ≤ 1/4`. None tested.
28. **The `a≠0` big-monodromy itself** — prove non-abelian for generic `p` (currently `[VERIFIED
    p=43,67]`; `p=13/n=7` is an exception) and identify the monodromy group (GL(2)/big). This is the
    object L-mono (#26) must analyze; a wider sweep + a "why big monodromy for `a≠0`" proof are owed.
29. **Group-law joint difference-set objects on the real key set.** `P_i ± P_j` via curve addition
    (connects to the DLP through curve arithmetic, unlike an `x`-coordinate character sum); the
    `μ₃`-graded / cubic difference character `χ₃(x_j−x_k)` (secp's CM/Eisenstein direction, the subspace
    `S_diff` is blind to); the `σ`-weighted difference sum (the on-curve analogue of the v34
    `C=Σσ(x)χ₂(x³+7)` object); triple / multilinear difference-set objects. Each its own prereg.
30. **Higher-order / joint / larger-`p` extensions of the twist-orbit programme.** The 2 arrangement
    channels null (B4.1, B4.2) + the others forced (B1.7) + `E[u⁴]~SU(2)` (B3.1) map **where** structure
    cannot be through 2nd/3rd/4th order — **not** a closure. Untested and named: joint
    additive-multiplicative cross objects, short-scalar / incomplete sums (no character-sum bound
    constrains `B ≪ √p` scalars), higher moments, larger `p`.

---

# PART B7 — METHOD NOTES THAT BIND FUTURE RUNS  *(each established by an artifact in this window)*

1. **A "false null" can be a bug — check the forced-relation sign before reading a stratum split.** The
   first 120° sweep returned `g=0` on all of stratum C and would have fired "the law is
   stratum-specific"; it was `e₃`'s `p mod 4`-dependent sign mis-stated in the prereg (R-B5.43), caught
   by the independent `V₁..V₄` route, not by the primary pipeline. Keep a second, independent instrument
   for any sign the conclusion turns on.
2. **Refuting a mechanism ≠ refuting the claim — redirect, don't close.** L-Stick's premise is false for
   `a≠0` (B2.2); the proved per-cell `u=ζ₃` (B1.1) is untouched, and the route moves to L-mono. A wrong
   mechanism relocates the object; it does not retract the fact
   (`[[feedback_verify_external_critiques_2026_07_17]]`).
3. **A group action relating cells is not a within-cell forcing.** The same category error was made
   twice (R-B5.39, R-B5.40): the `μ₃`-equivariant sheaf and the ω-descent both relate *different* `a` to
   each other; neither produces the `ζ₃` *within* a fixed cell. Before proposing a symmetry as the
   forcing lever, check it is not merely permuting the objects whose value is in question.
4. **Verify a citation before use, even a "classical" one — and the verification can succeed on the
   fourth try.** Stickelberger failed three citation-verifier runs, then verified cleanly against Katre
   with three load-bearing caveats (B2.1). "Classical" is not "verified"; and a discharged citation
   carries its caveats forward on every promotion.
5. **A pre-registered fired cell goes to §1 with its pre-committed conclusion; a robustness re-test of
   the same statistic is not an independent replication.** `E3` (B3.4): the two nulls are the same
   distribution, so the two p-values are one result twice, not a reduced p — and multiple-comparison
   correction (1 of ~7 statistics) is applied before the cell is named anything
   (`[[feedback_prereg_abstention_is_the_finding_2026_07_19]]`).
6. **A dissolution is positive when it locates the object.** Arm II dissolving to `nI−J` (B1.7) *found*
   the signal (the values `V(a)`, not the frame); forced 2nd/3rd-order objects *isolate* the one free
   object (magnitude). Report the located object, not the dissolved arm.

---

*Every claim above is traceable to a named artifact in `btc_puzzle_investigation/`. Grades are carried
verbatim from those artifacts; where an artifact grades its own work `[VERIFIED — p=43,67]`,
`[PROVED — modulo (D2)]`, `[EMPIRICAL — scoped]`, etc., that qualifier is reproduced here and must not
be dropped on promotion. Nothing in this document is promoted into `POSITIVE_FINDINGS_MASTER_*` — that
promotion is gated by `compile-diff` (CLAUDE.md §2).*

*No ECDLP, key-recovery, or security claim is made or implied anywhere in this addendum. Empirical and
verified rows are scoped facts about a statistic, a sample, and a floor; only a rigorous analytical
proof closes an avenue, and none is claimed closed here.*
