> **⛔ FROZEN — NOT CURRENT.** This file is a historical snapshot. The single current-state
> document is **`CLAIMS.md`**. Do not read status, grades, or open items from here; do not
> write a successor version of this file. (Frozen 2026-09-01.)

# secp256k1 — Master Positive-Findings & Structure Map (v7, 2026-08-09)

**Supersedes `POSITIVE_FINDINGS_MASTER_v6.md`** (2026-08-06), retained for diff; v6→v5 (2026-08-05)→v4
(2026-07-20)→v3 (2026-07-19)→v2 (the non-lossy restoration after `DEGRADATION_AUDIT_H3_TO_MASTER_v1.md`),
all retained. Predecessor handovers in `archive_handovers/`.

**What is new in v7** (2026-08-09): folds in two structural layers that post-date v6 and were in no
master — the `~/ZCodeProject` research tree is now in scope. **(A) The cohomological tensor /
splitting-field layer** (Part XIII): the ZCode `tensor-decomp` twist-discriminator (the census identity
`e₂=e₁²−χ₂(−1)p` at **1171/1171 cells, 11 primes `43≤p≤1303`**; twist character `ξ=ζ₃` constant) *plus*
the on-disk **algebraic-number layer** (`RESULT_algebraic_number_layer_v1.md`, 2026-07-31 — tower
`Q⊂Q(ω)⊂L`, multiplicity 3, `G⊆A₄₀`), which had sat in this folder **uncarried by v4/v5/v6**. **(B) The
universal phase channel** (Part XIV): the ZCode `secp256k1-structure` Threads #2/#5/#6 (`k=3`,
`χ₂(b)`-coupled, real-weight `μ₂` mechanism — NOT CM, NOT a leak). New ledger rows **P16, M21–M24,
N8–N10**; new live frontiers **§XI.16–18**; Appendix A / C additions. **The load-bearing honest framing
(anti-overclaim):** the discriminator's headline 1171/1171 is, by an exact symbolic reduction (P16,
`twist_identity_reduction_v1`), **equivalent to the single scalar census identity per cell** —
necessary-not-sufficient for the tensor decomposition, *not* an independent 4-dimensional confirmation;
the reframed question is *why the identity holds* (N8). The **global** field layer (M23) is genuinely
independent of that per-cell identity and is not reduced away — both holding is real evidence the
structure is not a one-methodology artifact. No new security claim; every new row is under the scale
banner (`p≤1303` tensor/field, `p∈[5000,65000]` phase channel). *(The `kangaroo-pool-lab` Pollard
sandbox is applied tooling — "will not find the key at any realistic compute" per its own charter —
deliberately **excluded** from this structure map.)*

**Compile-diff record (v7 vs v6).** Compiled against v6 with the `compile-diff` agent: **PRESERVED — no
losses, no unjustified upgrades.** The v6→v7 `diff` is strictly additive (zero delete hunks; the only
non-additive edits are the title and the version-lineage line, both non-lossy). Part A ledger (15 P / 20 M
/ 7 N), Part XI frontiers 1–15 + the "Also live" tail, the Part XII retraction ledger (26/26 + both
notes), Appendices A/B/C, and all six structural guards (scale banner, language rules, compile rule,
anomaly-drill rule, stance, grades legend) carried forward intact. No existing grade moved; the only new
tags sit on new additive rows — P16 `[PROVED — exact symbolic]`, M24 `[EMPIRICAL]`, and the tensor
decomposition itself graded `[HYPOTHESIS]` (a **down-grade** of the ZCode source, backed by the named
reduction script). All nine spot-checked new-cited artifacts exist on disk. **Owed (outside loss scope):**
the `[CITED — TO VERIFY]` Katz / Kummer citation (§XIII.6, Appendix C) needs `citation-verifier` before
any grade moves up on its strength.

**What is new in v6** (2026-08-06): a **correction pass** executing the ledger action of
`RETROSPECTIVE_FINDING_01_subrayleigh_demotion_v1.md` (2026-08-04), which v5 did not carry. Three fixes,
each a restoration of something established on disk and lost at consolidation: (1) the **sub-Rayleigh
deficit** — a real, universal, mechanism-open **−13.99σ** anomaly, the one live residue of the #1 lead —
is restored to A.3 (N7) and Part XI (§XI.15), absent from v4/v5; (2) the **M14 caveat is re-worded**: the
scalar-fidelity control is *forced* non-separating (pinned `l²`), a property of the statistic, not a bound
on the lead; (3) **§XI.1's "NOT YET RUN" is corrected** — the frequency-support map ran
(`harmonic_support_pattern_v1`, 2026-07-20): Rayleigh across ~`p²` harmonics, no active/starved split,
`l²` basis-invariant. No new measurement and no security claim; the arithmetic-scatter follow-up to N7 is
under active investigation and a later version will fold its result.

**What is new in v5** (2026-08-05): (1) **N4 / Route 3** upgraded from "one cover" to a source-verified
characterization of the whole cover family (`ANALYSIS_n4_cover_family_indexcalculus_v2.md`,
citation-verifier-cleared) — N4 row, §VII.3 Route 3, §XI.13; (2) **R1 / Semaev** (§XI.4) re-scoped: the
prior matched solving-degree null rested on a provably curve-blind statistic
(`RESULT_semaev_dsolv_statistic_power_v1.md`) — the CM solving-degree lever question is REOPENED, plus a
generic-CM decomposition-count effect surfaced. Both corrections run toward MORE open, not less; no new
security claim.

**Compile-diff record (v5 vs v4).** Compiled against v4 with the `compile-diff` agent: the Part XII
retraction ledger is byte-identical (26/26 preserved), both cited artifacts exist and are on-point, and
the +26-line diff is exactly the 6 intended regions with nothing changed outside them (N5/N6/banner
untouched). One substantive finding — §XI.4 had re-claimed first-fall-DEGREE curve-independence as
`[PROVED]`, contradicting preserved retraction #8 / §VIII (which hold it at `[HEURISTIC+CITED]`; isobaric
sub-fact `[PROVED]`) — **fixed in this edit** (§XI.4 now mirrors §VIII); two minor items (this record; the
N4 `R3` gloss) also fixed.

**What is new in v4:** (1) the programme pivot to **Localized Bit Extraction** (Part 0); (2) a
**standing ledger** in status-tag form with no interpretation attached (Part A); (3) the
**χ₂(y)-cover / `A_new`** thread, which post-dates v3 and was not in any master; (4) restoration of
**Claim S / Claim F** and the **frame-operator core isotropy**, both present in earlier sources and
absent from v3; (5) five post-v3 `RESULT_*` threads folded in; (6) thirteen additions to the
retraction ledger (§XII.14–26); (7) five new live frontiers (§XI.10–14).

**Compile-diff record.** v4 was compiled against v3 with the `compile-diff` agent, which found and
sent back for repair: a struck frontier (§XI.9) whose citing artifact explicitly declines to resolve
it; a deleted Part IX; a scale-banner carve-out that had exempted two claims that are not scale-free;
two grade-ups with no artifact named (the χ₂ bounds — the artifact existed on disk and was simply not
cited, now `[PROVED|WD]` P6b; and `ord_n(p)`, reverted to `[VERIFIED]`); one dropped open sub-item;
two dropped scope qualifiers; and nine dropped file references. All are repaired above. **The audit
that catches this is not optional — three of those defects were introduced by the same edit that was
writing the compile rule forbidding them.**

---

> ## ⚠ SCALE BANNER — GOVERNS EVERY MEASURED CLAIM BELOW
> **Every empirical result here was measured at small-to-moderate `p`** (`p = 13 → 10⁵`; the
> class-number thread at `p < 2500`; the `C_T` drill at `p ≈ 2¹⁷`; the Semaev thread at `p ≤ 307`;
> the cover thread at `p ≤ 160`). **Nothing here was measured at secp's `p ≈ 2²⁵⁶`** — a gap of
> ~239 binary orders of magnitude. A structure that only switches on near `2²⁵⁶` would not show in
> any test cited here, and **no test here has any power against that hypothesis.** **This caveat is
> total and governs every Part below.**
> *(The only claims that reach secp are those whose proof is algebraic and contains no measured input:
> P1, P2, P8 (Claim S), P9–P10 (Claim F), P15, and the congruence facts of Part I. Every
> `[VERIFIED]`/`[EMPIRICAL]` row does not. **Two claims that look scale-free are not:** the Cap Law
> and the CM spine are `[PROVED — continuum]`, i.e. exact in the continuum with a finite-`p`
> discretization error; and **`Hom(E,A_new)=0` (P13) inherits N2** — its proof runs through "`A_new`
> supersingular at secp", which is an unproved dimension-2 extrapolation. Do not quote P13 at secp
> without N2 attached.)*

> ## ⚠ LANGUAGE RULES (binding on this document and all successors)
> This document **maps structural boundaries; it does not assess cryptographic security.** The words
> **`secure`, `closure`, `proven hard`, `unbreakable` are forbidden.** Every conclusion states
> (a) exactly what was measured, (b) the bound it achieved **with its power and scope**, and (c) that
> unmeasured / higher-degree / other-basis structures remain **outside the scope of the statement.**
> **"Bounded by KS" is not "ECDLP is hard"** — never equate them.
> **No dismissal by declaration.** A measurement reported as `flat` or `generic` is *a statement about
> one statistic in one basis*, never a verdict that structure is absent. Restate it as: "flat in
> basis/statistic B at scale S; interference in another basis or at higher degree is UNTESTED."
> In this problem `flat`/`generic` most often means *the right basis to see the interference has not
> been found yet.*

**Compile rule (binding on all successors).** A successor may **not** delete a predecessor's open item
or retraction. It may only (a) carry it forward verbatim, or (b) mark it `resolved-by <artifact>` /
`bounded-by <artifact>` naming the script/proof. Losing an open item with no artifact cited is a defect
regardless of whether any claim is wrong. Grades move **down** freely; a grade moving **up** requires a
named artifact in the same edit. *(v4 was compiled against v3 with the `compile-diff` agent.)*

**Anomaly-Drill rule (binding on all frontier work).** Output = the mathematical **characterization**
of the object (symmetry type / eigenvector / subspace), never a verdict. Report magnitudes, never
convert a magnitude to a verdict; every bound carries its **power** and its **scope** (orbit, generator,
prime, estimator, `n`); the control must fire; a drill ends in a sharper law, a bounded magnitude with
its power, or a named next probe — **never in a "door shut".** Dissolution is a positive result: an
anomaly dissolves *into a sharper law* — state the law and its precision. **Count only UNFORCED hits**
(a forced-nonzero cell carries zero information); **reproduce the tally** — the law survives audit, the
count often does not; **retest out-of-sample before naming a zero.**

**Grades:** `[PROVED]` rigorous · `[PROVED|KS]` given the cited Kohel–Shparlinski bound ·
`[PROVED|WD]` given Grothendieck–Lefschetz + Ogg–Shafarevich + Deligne, derived on disk in
`weil_deligne_character_bound_v1.md` (verification `weil_deligne_bound_verify_v1.py`) ·
`[VERIFIED]` exact/numeric **at tested scale — see banner** · `[CITED]` literature ·
`[EMPIRICAL]` measured, not proved · `[HEURISTIC]` · `[OPEN]` · `[GAP]` no reduction in hand ·
`[UNREPRODUCED]` stated in a source, not reproducible here.

**Stance.** ECDLP is **assumed-not-proven**; it is the *object of study*, currently the residual. An
EMPIRICAL null is **not** a closed avenue — only a rigorous analytical proof closes one, and leakage
may be subtle or sub-noise. Positive exact structure leads. **Out of scope: the PRNG / generation
side** (a curve question only). Signal-path arithmetic is exact (`int`/`Fraction`); float appears only
as an analytic-size character-sum magnitude or a monotone statistic ranked against a matched
permutation null.

---

# PART 0 — PROGRAMME PIVOT: LOCALIZED BIT EXTRACTION  *(new in v4)*

**We are pivoting away from global group properties and global character sums.**

Those two families are where the last several arcs lived: `Σ_P` over the whole group, `max_a |U(a,b,c)|`,
frame-operator spectra, isotype energy budgets, class-number conservations. They produced real exact
structure (Parts II–IV, VIII) and real magnitude bounds (Part V). What they cannot do, by construction,
is say anything **point-specific**: a global sum over `E(F_p)` is invariant under the very symmetries
that make individual scalars indistinguishable, and a `√p` bound on a global sum is a statement about
an average, not about any one point.

**The new object.** Let `d ∈ ℤ/n` be the secret scalar and `P = [d]G = (x_d, y_d)`.

> **Localized Bit Extraction (LBE).** Does there exist a map `B : E(F_p) → {0,1}^k`, computable in
> polynomial time **from the single point `(x_d, y_d)` alone** (no `T`, no `U`, no group-wide sum, no
> discrete log), whose output carries information about a *specific local function of `d`* — a named
> bit, `d mod m`, `d`'s position within its μ₆ orbit, or `d`'s residue against a lattice/lift
> coordinate — at a rate above a **symmetry-matched** null?

**The question v4 asks of every structure in this document.** The lift geometry (`eis`, the flap, `σ`,
`ε`), the CM spine, the `x₂(y)` / χ₂(y)-cover behaviour and the cover lifts are **anomalies with exact
laws**. The pivot asks whether any of them **leverages itself into local, point-specific information
about `d`** — not whether it produces another global identity.

**Operational form (what a run must fix before data).**
1. **Readout** `B` — explicit, poly-time, single-point, no DLP-cost object in its definition.
2. **Target** `τ(d)` — a *local* function of `d`, constructed **disjointly** from `B` (never a residue
   of the same decomposition — see the residue-vs-component tautology, §XII.24).
3. **Null** — symmetry-matched to `B`'s own invariances. A value-permutation null against a readout
   that is even in `d` (because `x_{−d}=x_d`) is a **guaranteed false positive**: this has now fired
   twice (§XII.15, §XII.6).
4. **Power** — the plant that fires, and the mixing fraction at which it stops firing.
5. **Falsification** — the pre-committed cell that says the arm did not fire.
Pre-registration via the `experiment-designer` agent is **mandatory** before any LBE run.

**What is already bounded inside the LBE frame** (each a magnitude with a fired control, none a
closure): the six μ₆-isotype-pure cheap readouts (M20 / §X.3, no concentration above `φ ≈ 0.1–0.5`); six
coordinate-bit readouts at `n=50497` (M19 / §X.3, `z_matched ∈ [−1.05, 2.34]`); the D1 affine lift into
`A_new` (§VII.4, `0/666` additivity). **What is untouched:** the effective-support / multi-frequency
channel (`N_eff`) that single-peak concentration cannot see; multi-bit and multi-point joint readouts;
**non-unitary / non-Fourier bases** of the 0.93 joint shadow (its `(b,c)`-Fourier support IS mapped —
Rayleigh, no active/starved split, `l²` basis-invariant — §XI.1) and the **sub-Rayleigh deficit** that
map left (N7 / §XI.15); every scale above `2¹⁷`.

**Standing caution.** LBE is a research direction, not a result, and it is the direction in which a
positive finding would be **most consequential** — which is exactly the direction in which a
symmetry-mismatched null manufactures one. Every §XII retraction in this document that came from a
"5–9σ escape" was an LBE-shaped test with an unmatched null.

---

# PART A — THE STANDING LEDGER  *(status tags only; no interpretation, no ECDLP consequence)*

*This is the compressed record. Each line is independently verifiable from the named artifact. No line
here carries a "this means X for ECDLP" clause; the structure map is Parts I–X plus X-bis, the open items
are Part XI, and the things not to re-claim are Part XII.*

## A.1 Proved  *(rigorous; verifiable independently; scale-free unless noted)*

| # | statement | grade |
|---|---|---|
| P1 | `p_secp = 2²⁵⁶−2³²−977 ≡ 3 mod 4`, `≡ 1 mod 3`, `≡ 7 mod 12`. | `[PROVED]` |
| P2 | For any elliptic curve over `F_p` with `p ≡ 3 mod 4`: `Σ_{P∈E(F_p)} χ₂(y_P) = 0` **exactly**. *Proof:* `χ₂(−1)=−1 ⇒ χ₂(y_{−P}) = −χ₂(y_P)`; pair `P↔−P`; 2-torsion gives `χ₂(0)=0`. **Applies at secp.** Converse FALSE (non-CM `p=97 ≡ 1 mod 4` vanishes accidentally). | `[PROVED]` |
| P3 | `C : w⁴ = x³ + B` has genus 3; `E = C/⟨w↦−w⟩`; `H¹(C) = H¹(E) ⊕ H¹_new`, `dim 2 + 4`. | `[PROVED]` |
| P4 | `ζ₄:(x,w)↦(x,iw) ∈ Aut(C)` for **any** cubic; `ζ₄² = (w↦−w)` ⇒ `ζ₄ = ±i` on `H¹_new` ⇒ `Q(i) ⊆ End⁰(A_new)`. | `[PROVED]` |
| P5 | For cubic `= x³+B` **only**: `ζ₃:(x,w)↦(ωx,w) ∈ Aut(C)` ⇒ `Q(ζ₁₂) ⊆ End⁰(A_new)`, degree `4 = 2·dim`. | `[PROVED]` |
| P6a | **Additive** character-sum bound from Grothendieck–Lefschetz + Ogg–Shafarevich + Deligne (Weil II): `\|U(a,b,c)\| ≤ (1+ord_O(f))√p + 1` — `= 4√p+1` for `c≠0`, `3√p+1` for `c=0`. Holds for all `p`, bounded degree. Independently carried by Kohel–Shparlinski for the additive case (Appendix C). | `[PROVED\|WD]` = `[PROVED\|KS]` |
| P6b | **Multiplicative (χ₂) rows — a DIFFERENT theorem, and it is named.** `\|Σχ₂(x_P)e_n(ad)\| ≤ 2√p`, `\|Σχ₂(y_P)e_n(ad)\| ≤ 4√p`. **KS does NOT give these** (§XII.10 — KS's ψ is additive, via Artin–Schreier). They come from the same cohomological machinery with a **Kummer** sheaf `L_χ(g)` (rank 1, tame, Swan 0, ramified exactly where `ord(g) ≢ 0 mod ord(χ)`) in place of Artin–Schreier: `\|V(a;χ₂,g)\| ≤ #R·√p` with `#R = 2` for `x` (the pole has even order 2) and `#R = 4` for `y`. **Derived on disk: `weil_deligne_character_bound_v1.md` §6′, script `weil_deligne_bound_verify_v1.py`.** This is what closes the §XII.10 scope gap; **do not attribute it to KS.** | `[PROVED\|WD]` |
| P7 | `a_p = t`, `0 < t < p` ⇒ `t ≢ 0 mod p` ⇒ **`E` is ORDINARY**. | `[PROVED]` |
| P7′ | `ord_n(p) = (n−1)/6` exactly, 254-bit (MOV embedding degree). Computed, not proved here. | `[VERIFIED — 254-bit]` |
| P8 | **Claim S — the μ₆ selection rule on the curve.** With bidegree `(j,k) ∈ ℤ/2 × ℤ/3` defined by `F([−1]P)=(−1)^j F(P)`, `F([λ]P)=ω^k F(P)`: `Σ_{P≠O} F(P)\overline{G(P)} = 0` whenever `bidegree(F) ≠ bidegree(G)`. *Proof:* reindex `P→uP`, `u∈μ₆`; the sum picks up `χ_F(u)\overline{χ_G(u)}`; differing characters give a factor `≠1` for some `u`. Three lines. **Verified p=547: 54 cross-bidegree pairs, 0 violations**, by a *direct* sum (an orbit-decomposed sum would assume the mechanism). Controls fired (`T(s_y,s_y)=91`; `T(s_y,s_y·h)=45` — a known nonzero at matching bidegree). | `[PROVED]`+`[VERIFIED]` |
| P9 | **Claim F — the FIELD-level rule, strictly stronger.** For `F,G` functions of `x` alone, `#{y:y²=x³+B} = 1+χ₂(x³+B)` splits every `j=0` pairing into a **FIELD** part (pure `F_p` lattice/character geometry, zero curve content) and a **CURVE** part (a Weil-scale sum). With field bidegree `(i,k)` from `F(−x)=(−1)^i F(x)`, `F(βx)=ω^k F(x)`: **(F1)** FIELD `= 0` unless `(i,k)_F=(i,k)_G` — **6 sectors**; **(F2)** CURVE `= 0` unless `k_F=k_G` — **3 sectors**. **Verified p=127→1249, 16 primes: (F1) 336/336, (F2) 180/180, zero violations.** | `[PROVED]`+`[VERIFIED]` |
| P10 | **The missing `ℤ/2` is the sextic twist.** `Aut(E)` reaches `x` only through μ₃ (`[−1]` moves `y`, not `x`); the field group is strictly larger. `βx: (βx)³+B = x³+B` (invariant, μ₃ survives on the curve); `−x: (−x)³+B = −(x³−B)` ⇒ **the sextic twist `y²=x³−B`**. Field negation exchanges `E` with its sextic twist. | `[PROVED]` |
| P11 | **Cap Law.** The flap is geometrically forced, not a statistical region: `ε(x) ≠ 0 ⟺ \|u−v\| > ½` in the reduced basis. Core/flap densities `¾ : ⅛ : ⅛` (continuum area). | `[PROVED — continuum]` |
| P12 | **CM spine law.** For every `X`, `eis(βX) = ζ·eis(X) + c` with `c ∈ {0, +R, −R}` in exact densities **`¾ : ⅛ : ⅛`** (θ-independent, continuum). The pure-rotation ¾ preserves norm; the `±R` flap (¼) is the sole norm-change / parity flip. The correction is a **μ₃-orbit invariant** `ε ∈ {0,+,−}` per orbit `{X,βX,β²X}`, ⊥ χ₆. | `[PROVED — continuum]`+`[VERIFIED]` |
| P13 | `Hom(E, A_new) = 0` at secp — **⚠ inherits N2: the proof runs through "`A_new` supersingular at secp", an unproved dimension-2 extrapolation. Quote it with N2 attached.** `E` ordinary (`π,π̄`, `\|π\|=√p`, `π+π̄=a_p ≢ 0`) vs `A_new` supersingular (eigenvalues `√p·ζ`): no shared Frobenius eigenvalue ⇒ by **Tate's isogeny theorem** `Hom ⊗ ℚ_ℓ = 0`. Equivalently incompatible Newton slopes `{0,1}` vs `{½,½}`. **Secp-valid, not a small-`p` artifact.** | `[PROVED]` |
| P14 | **Prime-order rigidity.** `E` of prime order ⇒ the only coarse readout that **chains** (`f(P+Q)=φ(f(P),f(Q))`) is `d`; `σ ⊥ s_y` exact; the Semaev `C_t` is smooth genus-1 for every `t` (`disc_{x₂}S₃ = 16(t³+B)(x₁³+B)`, `n` odd prime ⇒ `−B` not a cube ⇒ `t³+B ≠ 0`). | `[PROVED]` |
| P15 | **Reduction (exact).** `Corr_F(a) = ⟨F, χ_a⟩_d`; concentration `C(F) = max_a\|Corr_F\|/‖F‖₂ = Ω(1)` ⟺ `F` correlates `Ω(‖F‖₂)` with `χ_{a₀} = e_n(a₀ d)`. | `[PROVED]` |
| P16 | **Twist-factorization reduction.** For the monic Frobenius `L*(T)=T⁴+c₃T³+c₂T²+c₁T+c₀`, the `ζ₃`-twist factorization `L*=(T²+AT+B)(T²+ζ₃AT+ζ₃²B)` (the ZCode `tensor-decomp` "discriminator") forces, on eliminating `A,B`, residuals `R₀=c₁²−c₀c₃²` and `R₂=c₂c₃−c₃³+c₁`. Under the census-forced `e₃=χ₂(−1)p·e₁`, `e₄=p²` (Part I `L*` construction): `R₀≡0` **identically**, `R₂=(e₁/p³)[χ₂(−1)(e₁²−e₂)−p]`, so off `e₁=0`, **`R₂=0 ⟺ e₂=e₁²−χ₂(−1)p`** (and the `e₁=0` branch adds no independent condition). **⇒ the discriminator PASS is algebraically EQUIVALENT to the single scalar census identity `e₂=e₁²−χ₂(−1)p` per cell — necessary-not-sufficient for `H¹≅W⊕W⊗ξ`, NOT an independent 4-dim confirmation.** `twist_identity_reduction_v1.py` (ZCode); lineage `RESULT_e2_identity_extended_verification_v1.md`. §XIII.2. | `[PROVED — exact symbolic]` |

## A.2 Measured  *(sample size stated; scale banner governs every row)*

| # | statement | sample |
|---|---|---|
| M1 | `A_new` ordinary ⟺ `p ≡ 1 mod 4`. | 24/24 (12 CM + 12 non-CM), both covers |
| M2 | `gcd(L_E, L_new) = 1`. | 18/18, both covers |
| M3 | **Saturation** (measured max ÷ its own ceiling `dim·√p`): additive `bx+cy` (dim 4) **0.876** [0.807–0.917]; additive `bx` (dim 3) **0.909** [0.809–0.964]; `χ₂(x)` (dim 2) **0.947** [0.822–0.998]; **`χ₂(y)` (dim 4) 0.470** [0.432–0.500], converging to ½ (0.432, 0.455, 0.477, 0.459, 0.500, 0.499). Decisive control: `bx+cy` has the **same dim, ceiling, frequency count and estimator** — a **1.86× systematic gap at identical dimension**, which a max-over-frequencies artifact cannot produce. | 6 primes |
| M4 | `V(a) = Σ_P χ₂(y_P) e_n(a·d)` is **purely real** at every `p ≡ 1 mod 4`, **purely imaginary** at every `p ≡ 3 mod 4`. Parity does **not** cause the ½ (both classes ≈ 0.47) — two distinct real structures. | every row |
| M5 | No measured max `/√p` exceeds its derived constant (bound verification). | all rows |
| M6 | Supersingular `ord(α²/p)`: CM `{1,3}`, non-CM `{3,4}` (order 4 only non-CM, order 1 only CM, order 3 shared). **Sample too small to call a law — recorded as an open pattern.** | 6 primes each |
| M7 | `C_T` inter-coordinate coupling `< ~1.6%` at `n ≈ 1.3×10⁵`, `b=7`, `p ≤ 2¹⁷`; **control fired** (plant at ε̂=1.6% → z=8.1, ε̂=2.4% → z=17.1, silent at n=5000). No power below ~1.6%; **zero power at 2²⁵⁶**. | 8 prime-order curves |
| M8 | Structured-pair `C_k` at the degree-matched floor, `k`-independent. | `p ≤ 10⁵`, `k ≤ 64` |
| M9 | Semaev **first-fall and solving degree identical** for secp (j=0 CM) / non-CM / j=1728 on **matched** systems (identical `V` and target): `d_ff=12`, `d_solv=15/17/18`, `d_gb=3`, and an identical singular-fibre locus (the diagonal `xᵢ=xⱼ`, zero `t`-ideal). | `p ≤ 307`, `m ≤ 4` |
| M10 | **Frame operator** `C = Σ_x eis(x)eis(x)ᵀ`: `λ_max/Tr` is **exactly ½ on the μ₃-core** (exact-integer isotropy test: a 120°-symmetric point set has `C ∝ I`) and **¾ on the full lift**; `¾ − ½ = ¼ =` the flap fraction. Every bit of anisotropy in the lift is a **flap phenomenon, weighted exactly ¼**. | exact at tested `p` |
| M11 | **`\|FLD(p)\| = 6·h(−p)`.** `FLD(p) = Σ_x σ(x)χ₂(x) = 0` unless `p ≡ 19 mod 24`; `\|FLD\| = 6·h(−p)` there. **Not `[PROVED]` — the chain closes modulo lemma L1 alone (§X.2, §XI.8).** | 34/34 nonzero (h ≤ 11) + 103/103 zero, `p ∈ [100,2000)` |
| M12 | **`⟨σ,χ₂⟩_FIELD = 0 ⟺ p ≢ 3 mod 8`**, counted correctly: `p≡1 mod 4` forced-zero 19/19; `p≡3 mod 8` **forced-nonzero by the ORB parity obstruction — zero information, not evidence**; `p≡7 mod 8` **not forced: 35/35** (22/22 in-sample + 13/13 out-of-sample on fresh primes `[8000,14000)`). Generic expectation would give ≈1.86 zeros. The natural mechanism (a multiplicative `c` with `σχ₂(cx) = −σχ₂(x)`) is **exhaustively ruled out** at `p=127,823,967,991`. | 35/35 unforced |
| M13 | **`(B2) = C`.** On the **curve**, `Σ_{P≠O} σ(x_P) = C := Σ_x σ(x)χ₂(x³+B)`, verified exactly 49/49; `C²/p ≤ ~3.7` over `p=127→6000`, consistent with `\|C\| ≤ ‖σ‖_W · 2√p`. | 49/49 |
| M14 | **Joint `(x,y)` aligned readout reaches `ρ_inf = 0.93–0.96`** (x-only 0.29–0.36), stable at `p ∈ {163,349,433,577}`; planted perfect character reads 1.0000. **But** the magnitude control (same phase-only reconstruction applied to the leaking character and to a random function of `d`) gives the **same scalar fidelity** (joint 0.999 vs 0.999; x-only 0.66 vs 0.67). **The scalar-fidelity statistic does not separate the character from random.** What is exact and real: `U(−a,b,c) = U(a,b,−c)` ⇒ x-only readouts are **even in `d`** and see only the even half of the `d`-spectrum; cross-orthogonality `⟨F_even, c_odd⟩ = 0` to 1e-15; even-subspace ceiling `1/√2`. **⚠ (v6) the non-separation is FORCED, not a bound on the lead:** `Σ_{b,c}\|U\|² = p²(n−1)` is machine-identical for the character and every random unit-phase target (`harmonic_support_pattern_v1` Arm B), so **any** `l²`-normalized fidelity statistic is forced equal across targets — the control validates nothing about the lead (see N7 / §XI.15; `RETROSPECTIVE_FINDING_01` §D1). | 4 primes |
| M15 | **Character equipartition.** `e_n(a₀d)` energy per μ₆-isotype `= 1/6` exactly in five isotypes; the trivial isotype carries `1/6 − (5/6)/(n−1)`, the deficit being **exactly** the excluded `d=0=O`, the unique μ₆-fixed point. Cross-isotype orthogonality ≤1.6e-15. | exact |
| M16 | The aligned readout built from `U` is **forced μ₆-symmetric** (`U(a,b,c) = U(λa,βb,c)`), so it is constant on `{±d,±λd,±λ²d}` and cannot separate `d` — and does not (w0≈w1≈w2). | exact |
| M17 | **`A_new`'s internal DLP is easy**: MOV embedding degree `k = ord_ℓ(p) = 3` at every tested supersingular prime (`p = 31,43,67,79,103,127,139`). Supersingular ⇒ `H¹_new` Frobenius eigenvalues are **exactly** `√p·ζ`, not merely `≤ 4√p`. | 7 primes |
| M18 | **D1 (the non-homomorphic lift `Q(P)=[P⁺−P⁻]`) carries no affine structure**: `0/666` additivity, `0/339` affine triples, at `p ∈ {43,67,79}`. Controls fired (`div(f)` principal True; `Q(d₀)` principal False). Positive structure recorded: exactly half of `E∖O` lifts (forced by `χ₂(−1)=−1`), and `Q(d)` lands on **high-order** elements (`2Q,3Q ≠ 0` at every tested `d`), not collapsed torsion. | 3 primes |
| M19 | **Six coordinate-bit readouts** (`x&1`, `hi(x)`, `x mod 4`, `x&15`, `y&1`, `hi(y)`) at `n=50497`: `z_matched ∈ [−1.05, 2.34]` against a `{d, n−d}`-orbit-matched null; plant fires at z=755, detection floor ~1% mixing. | 1 curve |
| M20 | Six μ₆-isotype-pure cheap readouts × 9 curves (`p=211→6397`): no single-orbit `d`-character concentration above **`φ ≈ 0.1–0.5`** (the power floor, smaller at larger `n`). The χ₃ weight-1/2 sub-threshold tilt at small `n` (combined `p≈0.08`) **washed out at larger `n`** (pR 0.31–0.55) — resolved, not a signal. | 54 cells |
| M21 | **The census identity `e₂=e₁²−χ₂(−1)p` holds uniformly** — via the twist-discriminator (equivalent by P16) at **1171/1171 μ₆-orbit cells across 11 primes `43≤p≤1303`**, zero failures: PATH A (exact cyclotomic factoring over `Q(ζ_{3n})`) 42/42 at `p=43,67,127`; PATH B (modular, coefficient-level twist test mod `l≡1 mod 3n`) reproduces PATH A exactly and extends to 8 more primes. Control `a=0` recovers the known eigenvalue structure. This is the exact-arithmetic content behind the "120° law" `g=deg gcd(L*(T),L*(ζ₃T))≥2`. | 1171 cells / 11 primes |
| M22 | **The twist character is constant: `ξ(Frob_p)=ζ₃`** (order-3, geometric — NOT a Legendre or cubic-residue character). Twist exponent `k(a)∈{1,2}` extracted cell-by-cell (6 primes `p=43..823`, 10 modular primes/cell): the **canonical `[2,2]` coefficient test** (`A₂=ζ₃ᵏA₁`, `B₂=ζ₃²ᵏB₁`) gives `k=1` in **1560/1560 = 100%**; the `[1,1,1,1]` 54:46 split is partition ambiguity (`{r,ζ₃r,s,ζ₃s}` indistinguishable a priori) — noise, not a varying character. So IF `H¹≅W⊕W⊗ξ`, the twist is a fixed automorphism. | 6 primes, canonical arm 1560/1560 |
| M23 | **The algebraic-number (splitting-field) layer — exact, independent of the per-cell identity.** `Q`-minpoly of `N_{Q(ζ_n)/Q}(L_a)` has degree **`4(n−1)/3`, multiplicity exactly 3** (`p=43,67,127`): the `4(n−1)` eigenvalues split into 3 equal `Q`-Galois orbits (the `μ₃` signature at the field level). Tower pinned at `p=43`: **`Q⊂Q(ω)⊂L`**, `[L:Q]=40`, `Q(ω)` the **unique** quadratic subfield (deg-20 factors `ω↔ω²`-conjugate, **even in `T`** = the forced involution `α↦−ᾱ`). Galois group (mod-`ℓ` cycle types, 100 primes): **`G⊆A₄₀`** (square discriminant), generic cycle type **`(10,10,10,10)`**, all cycle lengths `∣10`; `L/Q(ω)` **non-abelian** ⇒ commutative-CM ruled out at the field level. `RESULT_algebraic_number_layer_v1.md`. | `[VERIFIED — exact]` 3 primes; tower `p=43` |
| M24 | **Universal phase channel (conditional, not marginal).** For any Weierstrass `E/F_p`, `χ₂(−1)·sin(3·arg T(a₀,b)+φ_p) ≈ A(E,a₀,p)·χ₂(b)` (`T=Σ_d e_p(bx_d)e_n(a₀d)`), `φ_p=0` (`p≡3 mod 4`)/`π/2` (`p≡1`), **exclusively at `k=3`** (`A(k=1,5,7)` 10–100× weaker), `A∈[0.2,0.6]` (strongest `j=0`). Mechanism = real-weight `μ₂` symmetry (`T(−b)=conj T(b)`) + cubic `x`-degree — **NOT CM** (holds on non-CM curves). Decisive complex-weight control: `A:0.560→0.008`, `R²:0.18→0.00`. **NOT a leakage channel** — structure lives in the free parameter `b`; conditional MI of every contorted keyed readout given `d` is at the null (§XIV). `[EMPIRICAL]` ZCode `secp256k1-structure` Thread #6. | 14/14 primes, `p∈[5000,65000]` |

## A.3 Not established  *(open — not closed)*

| # | item | why it is open |
|---|---|---|
| N1 | **The mechanism for the ½ saturation.** `χ₂(y)` reaches half its ceiling while a **same-dimension** additive readout reaches 0.876. Effectively only **2 of 4** eigenvalues carry weight-1 mass at the maximizing frequency — the 2+2 splitting. **This is the one measured anomaly in the set with no account.** Twice attempted, twice not closed; no explanation is offered here. | unexplained |
| N2 | **Whether `A_new` is supersingular at secp.** The automorphism input is `[PROVED]` (P4: `Q(i) ⊆ End⁰(A_new)`). The step `Q(i) ⊆ End⁰ + p` inert `⟹` supersingular is **verified 24/24 at small `p`, not proved for dimension 2**. Extrapolation to `2²⁵⁶` is an **assumption**, and it is load-bearing for §VII. | proof gap at dim 2 |
| N3 | **No numerical discriminator for the CM layer (L3).** Two designed tests failed: `Q(ζ₁₂)`-splitting **passes trivially** when the roots already lie in `Q(i) ⊂ Q(ζ₁₂)` (non-CM passed 5/6); the `Q(i)` reasoning was **wrong** (degree 2 acting on a dim-2 surface is not `2·dim`). CM sits higher in both tests but not cleanly and not significantly (Fisher ≈ 0.6). L3 rests on the automorphism proof alone. | tests failed |
| N4 | **Cover transfer into `Jac(C)` — the cover FAMILY.** For any genus-`g` cover of `E/F_p`, known index calculus costs `Õ(p^{2−2/g}) ≥ Õ(p) > O(√p)` (`g≥2`; GTTD/Nagao exponent, Diem for plane curves) and genus 1 is slower than `√p` ⇒ **no cover beats Pollard by known index calculus**; subfield-exploiting descent (GHS/Gaudry/Joux–Vitse) has no input over a prime field; our cover `w⁴=x³+7` is a bielliptic plane quartic ⇒ heuristic `Õ(p)`. `[CITED — verified; ANALYSIS_n4_cover_family_indexcalculus_v2.md]` | family bounded vs KNOWN cover/index-calculus; residual R1 (prime-field Semaev)/R3 (sub-GTTD algorithm) open |
| N5 | **The unbounded / growing-degree corner of the character-sum bounds.** The constant grows with readout degree; for general poly-time (non-bounded-degree) readouts there is **NO reduction in hand**. | `[GAP]` |
| N6 | **Everything in A.2 is at `p ≤ 2¹⁷` or smaller; none of it has power at `2²⁵⁶`.** | the banner |
| N7 | **The sub-Rayleigh deficit** — the DLP character's harmonics run **0.06–0.10% *smaller*** than a random unit-phase target's (in `mean\|U\|`), one-directional **7/7 primes**, pooled **Z=−13.99**; survives the **exact value-multiset matched null**, holds for all **24** orbit-rep characters, and is **persistent** across a 79× `p`-range (decay excluded ≫8σ, `RESULT_subrayleigh_deficit_scaling_v1`). The one live residue of the #1 lead (§XI.1 / §XI.15). `[EMPIRICAL — enumerable model `p`; no transfer to secp]` | **mechanism unexplained** — two candidates ((0,0)-exclusion, Weil ceiling) refuted without refuting the effect; whether the scatter compresses to the Frobenius is under investigation |
| N8 | **Why does `e₂=e₁²−χ₂(−1)p` hold?** P16/M21 make the 1171-cell uniformity an exact structural law, but the geometric / representation-theoretic force behind the identity is unidentified. This is the question the twist-discriminator PASS actually poses — it does not answer it. | mechanism unidentified |
| N9 | **The explicit 2-dimensional piece `W`.** With `ξ=ζ₃` pinned (M22) the candidate is `H¹≅W⊕W⊗ζ₃`, but `W` (as an abelian subvariety / motive) is unidentified; and the per-cell discriminator is necessary-not-sufficient (P16), so it does **not** by itself establish the module splitting — only the scalar identity. | not identified |
| N10 | **The degree-20 non-abelian extension `L/Q(ω)`.** Is it generated by the predicted `SL₂`-monodromy action (the `W`-piece)? The concrete field-arithmetic target. The *exact* Galois group is unpinned — degree 40 is beyond PARI (cap 11) / KASH (cap 21); needs Magma or a custom resolvent. A `χ₂(−1)=+1`-branch confirmation of the mult-3 law (large enough to avoid the `n=7` degeneracy) is also owed. | group unpinned |

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
p ≡ 3 mod 4,  p ≡ 1 mod 3,  p ≡ 7 mod 12          ← secp's own class (Part A P1)
n ≡ 1 mod 4,  n ≡ 1 mod 3
```

- **Curve/scalar.** `d ↔ [d]G=(x_d,y_d)` bijection `ℤ/n ↔ E(F_p)` (full order n). Imports:
  `ecc_secp256k1` (`P=p`,`N_ORDER=n`,`scalar_mul`); `int1_frame_operator_v1.build(p)→(eis,eps)`
  **(⚠ see §XII.19 — the β-calibration bug at p=823)**; `lift_sextant_rhombus_law_proof_v2.reduced_basis(p)`;
  `_sigma_chi2_scan_v1.{chi2_table,build,sigma_fn}`.
- **Characters.** `e_p(t)=exp(2πi t/p)`, `e_n(t)=exp(2πi t/n)`; `χ_k(a)=a^{(p-1)/k}`; `χ₂`=Legendre.
  Curve character `χ_a(P):=e_n(a·d(P))` — the DLP frequency.
- **Eisenstein lift.** `eis(x)` = representative of `x∈F_p≅ℤ[ω]/(π_p)` in the 60° rhombus
  `P={uR₁+vR₂:u,v∈[−½,½)}`. `DET=R₁[0]R₂[1]−R₁[1]R₂[0]`; `u=(z₀R₂[1]−z₁R₂[0])/DET`,
  `v=(z₁R₁[0]−z₀R₁[1])/DET`; norm `N(z)=u²−uv+v²`, `s=N(eis x)/p∈[0,¾]`.
- **GLV/CM.** `β=g^{(p-1)/3} mod p` (β≡ω² mod π_p), `λ∈ℤ/n`, `λ³=1`, `x_{λd}=β·x_d`; μ₃=⟨β⟩ on x;
  μ₆=Aut=⟨β,−1⟩; `[−1]` fixes x, negates y. `eis(βx)=ω·eis(x)` reduced.
- **Cap/flap (σ).** `flap ⟺ |u−v|>½` (**Cap Law, P11**). `σ(x)=sign(u−v)` on the flap, else 0
  (orientation fixed by 100%-agreement pre-flight with `eps` — **not** a data-dependent majority vote,
  §XII.19). σ is μ₃-invariant and μ₂-odd ⇒ σ = the μ₂-isotypic part of μ₆.
- **Twisted sums.** `T(a,b)=Σ_d e_p(b x_d)e_n(a d)`; `U(a,b,c)=Σ_d e_p(b x_d+c y_d)e_n(a d)`,
  `T=U(·,·,0)`; `V(a)=Σ_P χ₂(y_P)e_n(a·d)`. `Corr_F(a)=(1/n)Σ_d F(P_d)e_n(-a d)`. `xy:=x·y` — ODD in
  d, μ₃-weight 1.
- **Bidegree (Claim S) / field bidegree (Claim F).** curve `(j,k) ∈ ℤ/2×ℤ/3` from `F([−1]P)`,
  `F([λ]P)`; field `(i,k)` from `F(−x)`, `F(βx)`. Measured field bidegrees: `sigma = (1,0)` at every
  prime; `eps = (0,0)` at every prime; `chi2 = (1,0)` at `p≡3 mod 4`, `(0,0)` at `p≡1 mod 4`.
- **Class-number thread.** `FLD(p)=Σ_{x∈F_p}σ(x)χ₂(x)`; `T+ = {x : σ(x)=+1}`; `S+ = Σ_{T+}χ₂`;
  `D = Σ_{a=1}^{(p−1)/2}χ₂(a)`; `F4 = Σ_{p/4<a<p/2}χ₂(a)`; `h(−p)` by reduced-form count (checked
  against `h(−163)=1`); `t(X)=p(u−v)`, `M ≡ t(1) mod p`; `T1 = Σ_X χ₂(X)t(X)`; `ORB = flap/6`.
- **Cover.** `C : w⁴=x³+B` (`w²=y`), genus 3; `Jac(C) ~ E × A_new`, `A_new = H¹_new` an abelian
  surface; `L_C = L_E · L_new`.
- **Semaev.** `S₃(a,b,c)=(a−b)²c²−2((a+b)(ab)+2·7)c+((ab)²−28(a+b))`. **`[VERIFIED]` — the `2·7` term
  is CORRECT** (the `2B` slot of the general `S₃`, `B=7`; survives `A=0`). Vanishes on **1406/1406**
  collinear secp triples; deleting `2·7` gives 0/1406. **Do not "fix" it** (§XII.22).
- **Key coordinate.** `A=2^{bits−1}`, `(n,k)=argmin_{n≤256}|n(d−A)−kA|`, `derr=|n(d−A)−kA|`;
  curve-identity `r=nD−(2^{N−1}k mod n)`. Datasets: `solved_keys_augmented_v1.csv` (82),
  `constructed_keys_fullrange_v1.csv` (36k), `..._100k_exact.csv`.
- **Transfer operator.** label `l(d)`; `M[i,j]=#{d:l(d)=i,l(d+1)=j}/#{d:l(d)=i}`; `|λ₂|~1/√n`=thermal.
  **Valid null = ABSOLUTE `|λ₂|` decay + multi-shuffle z (NOT shuffle-ratio on a 2-state, NOT `np.roll`).**

---

# PART II — THE EISENSTEIN LIFT LAWS  `[PROVED — continuum; VERIFIED at small p — banner]`

Shape constants are **exact statements about the continuum rhombus geometry**; at finite `p` they hold
up to a discretization error →0 as `p→∞` (measured: mean `s` deviates from `1/6` by 7.7e-3 at p=211,
1.2e-4 at p=1009, 4e-7 at p=10⁶).

- **Rhombus theorem `[VERIFIED, exact at every p]`.** Both reduced basis vectors have norm **exactly
  `p`** (re-verified p=13…331 and secp). `P` a 60° rhombus, edge `√p`; `eis` bijects `F_p→ℤ[ω]∩P`.
- **Angle law `[PROVED — continuum]`.** Sextant histogram = function of `θ=arg(π_p) mod 60°`; pinned
  pair `=1/8` (θ-indep); free `p₀(θ)=(¾)|cos2θ|/(2cos2θ+1)`. secp exact (`cos2θ=t²/2p−1`, rational):
  `p₀=0.2349002681…`, `3/8−p₀=0.1400997318…`, pinned `0.125`, θ=50.55°.
- **Norm-band law `[PROVED — continuum]`.** `s∈[0,¾]`, mean `1/6`, density `2π/√3` on `[0,3/16]`,
  breakpoints `3/16, ¼, ¾`.
- **All nontrivial `χ_k` uniform `[PROVED]`** (fibers `(p−1)/k`, exact at finite p); `Σζ₆^{χ₆}=0`.
- **GLV = lift × cube-root `[VERIFIED]`.** `χ₆(βx)=χ₆(x)+4`, `χ₃(βx)=χ₃(x)+1`, χ₂ fixed.
- **Summation-poly [ω]-covariance `[VERIFIED]`.** `S₃(βx)=β·S₃` (wt 1); `S₄(βx)=S₄` (wt 0).
- **Cap Law `[PROVED — continuum]`** — **Part A P11.** The flap is geometrically forced:
  `ε(x)≠0 ⟺ |u−v|>½`; core/flap densities ¾:⅛:⅛.
- **`x` has no μ₃ grading, only an energy profile `[VERIFIED]`.** `x → βx` is an action on a **field
  element**; `β∈F_p` is **not** `ω∈ℂ`. Measured: `x`, `eisx`, `nrm`, `sxt_z6` all come back
  **ungraded**. `eisx`'s grading defect set is **exactly the flap** (`eis(βx)=ω²eis(x)` iff `eps(x)=0`)
  — the grading defect and the flap are the same object. *An ungraded readout is not "structureless" —
  report which isotypic components carry its energy.* Derived and confirmed at every prime:
  `χ₂(β)=1` always ⇒ `chi2x` is `(0,0)` for every `p`; `chi2y`'s `j` tracks `p mod 4` via `χ₂(−1)`.

*(`lift_sextant_rhombus_law_proof_v2.py`, `norm_band_law_proof_v1.py`, `glv_orbit_structure_proof_v1.py`,
`cap_law_proofs_v1.md`, `isotypic_selection_rule_v1.py`; re-checks `_master_v2_math_verify.py`.)*

---

# PART III — THE SELECTION RULES  *(restored in v4; absent from v3)*

**One rule, not five walls.** The arc had accumulated a set of exact zeros — `σ⊥s_y`, the `Σψχ₃s_y=0`
GLV zero, the `eis_p`/`eis_n` cross-energy zeros, "± flap counts exactly equal", the linear
x-lift→scalar-lift channel — each recorded separately and each used as a *wall*. **They are one μ₆
selection rule** (Claim S, Part A P8), plus a **strictly stronger field-level rule** (Claim F, P9)
whose failure mode is the sextic twist (P10).

A selection rule is **two-sided**: it says which channels must vanish and therefore **which are allowed
to be nonzero**. That is its value here — it converts a list of "walls" into a table of *permitted*
channels, and the permitted-but-vanishing entries are the live objects.

- **The FIELD/CURVE split is mandatory on every `j=0` entry.** Reporting the total as one number
  **attributes a lattice fact to curve arithmetic**. This is the drill's central proxy guard.
- **Two recorded facts collapse into one.** `B1 = Σ_{x∈F_p*}σ(x) = 0` (σ is `(1,0)`, the constant is
  `(0,0)` ⇒ mismatch; confirmed 49/49) and `⟨σ,χ₂⟩_FIELD = 0` at `p≡1 mod 4` (χ₂ is then `(0,0)` ⇒
  mismatch) are **the same selection rule**. `B1=0` had a bespoke argument on record; it is a special
  case.
- **Non-forced FIELD zeros are accounted for.** Of 240 non-forced FIELD pairs, 72 are zero anyway:
  **56 are ordinary `F_p*` character orthogonality** (a *larger* group than μ₆), and the remaining
  **16 are the class-L × class-M cross-class pairs** — `(chi2,sigma)×8`, `(chi2,eps)×4`,
  `(chi3,eps)×2`, `(chi6,sigma)×2` — i.e. **exactly one live object**, which is the σ×χ₂ programme
  (Part VIII).

*(`isotypic_selection_rule_v1.py`, `_field_bigrading_v1.py`; `masked_structure_findings_v33–v35.md`.)*

---

# PART IV — CM / ENDOMORPHISM / L-FUNCTION / TWIST / AMICABILITY

- **`End(E)=ℤ[ω]`, maximal `[PROVED]`.** μ₆ acts **FREELY** on `E∖{O}`: `(n−1)/6` free orbits. MOV
  embedding degree `ord_n(p)=(n−1)/6` `[VERIFIED — 254-bit]`
  (`=19298681539552699237261830834781317975472927379845817397100860523586360249056`);
  `ord_n(2)=(n−1)/64` ✓, `ord_p(t)=(p−1)/6` ✓. Not anomalous (`#E=n≠p`) ✓. `E` **ORDINARY** (P7).
  Isogeny class all order n `[CITED — Tate]`.
- **Sextic identities `[VERIFIED]`.** `π_n=π−1` ✓; `[7/π_p]₆=ζ₆⁵`, `[7/π_n]₆=ζ₆`; ε=ζ₆^{3−[28/π]₆}.
- **L-function & its RH `[CITED — Hasse/Weil]`.** `L(T)=1−tT+pT²`, `|π|=√p` ⇒ zeros on `Re(s)=½`.
  Supersingular `a_ℓ=0 ⟺ ℓ≡2 mod 3` **for good reduction only (`ℓ∤42`)** `[VERIFIED]`.
- **Formal-group log `[VERIFIED]`.** `L(T)=Σ 7^k C(3k,k)/(6k+1) T^{6k+1}` — μ₆-sparse (exponents
  `≡1 mod 6`). `L(T[d]P)=d·L(T P)` linearizes the reduction kernel `E₁(ℚ_p)`, **not** `E(F_p)`;
  mapping `[d]G` into it = the DLP. **Order-2 shadow `[PROVED]`:** with `T=−x/y`, `(x³+7)³=y⁶` ⇒
  `R^(2) = T + 3T⁷` exactly (deviation 0 on real secp points and all 12 model curves); every
  truncation `R^(k)` is a polynomial in `R^(1)` alone, exponents all `≡1 mod 6`.
- **ASD/Honda `[VERIFIED]`.** `7^k C(3k,k) ≡ a_ℓ (mod ℓ)` at split ℓ — 58/58 primes < 700.
- **Twist `[VERIFIED]`.** Six sextic twists; `b=7 ↔ u=1+ω` unique prime-order; `n_t=2(p+1)−n`.
  **Field negation exchanges `E` with its sextic twist (P10)** — this is the mechanism behind M13.
- **Amicability `[VERIFIED — arithmetic] / [OPEN — transfer]`.** `#E(F_n)=p` exactly, via
  `#E(F_n)=N((1−π)−1)=N(−π)=N(π)=p` (**subtraction, not an inverse**; the spaces are load-bearing).
  **Scope: only the group-homomorphism case is ruled out (Hom=0, coprime orders). The
  non-homomorphic correspondence `π_n = π_p − 1` is UNANALYZED — §XI.3, a live frontier.** The
  protecting lift obstruction is `[HEURISTIC]` (xedni). Amicable geometry `[VERIFIED]`: `P_n=(π−1)`
  overlaps `P_p` by `1−4.1e−39`, `C_n⊆C_p`, slippage `R1_p−R1_n=(0,1)`, `R2_p−R2_n=(1,1)`.

*(`sextic_identities_verify.py`, `secp256k1_formal_group_finding.md`, `cm_amicable_correspondence_v1.py`,
`RESULT_formal_group_shadow_order2_v2.md`.)*

---

# PART V — THE LIFT-GEOMETRY PROGRAMME  `[PROVED continuum / VERIFIED small p — banner]`

- **The CM spine (P12).** `eis(βX)=ζ·eis(X)+c`, `c∈{0,+R,−R}`, densities **¾:⅛:⅛**.
- **Three bridges `[VERIFIED]`.** pinned↔angle-law; correction↔norm-band; **pinned pair↔Frobenius
  angle** (`{1,4}` if θ<30° else `{0,3}`; 0 violations / 69 primes).
- **Frame operator `C=Σ_x eis(x)eis(x)ᵀ` (M10).** `λ_max/Tr` is **exactly ½ on the μ₃-core** — a
  120°-symmetric point set has an exactly isotropic second moment (`C ∝ I`), checked by exact integer
  sums `S_uu, S_uv, S_vv` — and **¾ on the full lift** (uniform 60° rhombus, diagonal ratio `√3:1`,
  θ-independent). **`¾ − ½ = ¼ = the flap fraction`: all anisotropy of the frame operator is a flap
  phenomenon, weighted exactly ¼.**
- **`C_T` = a tensor square `[VERIFIED — precision stated]`.** `(¾:⅛:⅛)⊗(¾:⅛:⅛)`; tensor spectrum with
  a doubly-degenerate `⅓`. `ANOMALY_DRILL_01` (p=100003): block trace `λ₂+λ₃ = 0.666742` vs `2/3`
  (7.5e-5); **the degenerate block splits into one swap-EVEN and one swap-ODD channel, exactly as the
  tensor law requires.** The ~2–3% `λ₂≠λ₃` residual: a zero-coupling surrogate reproduces it
  (z=+1.6/+0.1); pooled G² p=0.40. Universality sweep (8 curves, `p ≤ 2¹⁷`, M7): `z_G²` spans
  `−1.17…+4.46`, `ε̂ ≤ 0.025`. **Language: this bounds a MAGNITUDE — any inter-coordinate coupling is
  `< ~1.6%` in the Frobenius-norm estimator, at `n≈1.3×10⁵`, this orbit/generator. It is NOT "no
  coupling", and the refutation of the 2–3% split is EMPIRICAL (a fired surrogate), not analytical
  (§XII.25). A coupling visible in another statistic, another basis, or near `2²⁵⁶` is untested.** §XI.6.
- **Addition in the lift.** `σ₁=x_{P+Q}+x_{P−Q}=−B/A`, `σ₂=x_{P+Q}x_{P−Q}=C/A` — rational in
  `x_P,x_Q`, β-covariant (400/400). Directional law `|V|²≈|U₁|²+|U₂|²+|U_sum|²` — **measured for random
  pairs at `k≤16` only** (§XI.7).

*(`glv_fundamental_domain_law_v1.py`, `glv_cm_orbit_invariant_v1.py`, `int1_frame_operator_v1.py`,
`ct_tensor_structure_v1.py`, `_anomaly_drill_ct_split_v2.py`, `ct_coupling_universality_v3.py`,
`glv_s3_addition_covariant_v1.py`.)*

---

# PART VI — THE LEAKAGE FRONTIER AND WHAT IS BOUNDED

- **Leakage is COMPUTATIONAL, not information-theoretic `[VERIFIED — with the M14 caveat attached]`.**
  The aligned readout `F̂(b)=conj(T(a₀,b))/|T(a₀,b)|` has no cancellation: `Corr(a₀)≈0.37` (x-only) /
  **0.93 (joint x,y)**. Building `F̂` needs `T`, hence all `x_d` — a DLP-cost object. **Attach M14
  whenever this line is quoted:** the scalar-fidelity control does **not** separate the leaking
  character from a random target in that statistic, so the 0.93 is the coordinate geometry's phase-only
  reconstruction quality in the tested basis. **The exact, control-surviving part is the even/odd
  constraint** (`U(−a,b,c)=U(a,b,−c)`; x-only readouts even in `d`; cross-orthogonality 1e-15).
- **★ Prime-order rigidity `[PROVED]` — P14.**
- **The bounded region.**
  1. *Reduction (exact) `[PROVED]` — P15.*
  2. *Bound `[PROVED|KS]`:* for **ψ a nontrivial ADDITIVE character** and `f` nonconstant, `deg(f)≤D`,
     `F=ψ∘f` has **`|Corr_F(a)| ≤ 2D√p/n`** — explicit constant, **no polylog** (Kohel–Shparlinski
     ANTS-IV 2000, Thm 1 + eq (3), SHA-256 `645d9022e029…5d8d2a`). Covers `e_p(xy)` (`deg=5`).
     **⚠ Does NOT cover `χ₂`** — KS's Ψ is **additive**, proof via Artin–Schreier; **χ₂ is
     multiplicative** (§XII.10). Empirically the best cheap readout `e_p(xy)` has `C/floor ≈ 1.3` in the
     aligned-phase statistic over p=211→6007, while the planted aligned control grows 6→27.
  3. *What is outside the bound:* the only `C=1` readout known is `e_n(a₀d)` = the discrete log, not
     bounded-degree. **`[GAP]` For general poly-time (non-bounded-degree) readouts there is NO
     reduction.** *"No concentration ⟺ ECDLP hard" is WITHDRAWN (§XII.9): `⟸` trivial, `⟹` unproved —
     there is no reduction in hand from a lack of concentration to hardness.*
- **`T_y/U` bound `[PROVED|KS]` — verified against the source.** `max_{a,(b,c)≠(0,0)}|U(a,b,c)| ≤
  4√p+1` — **uniform in (b,c), no polylog.** KS's `ω∈Hom(E(F_p),ℂ*)` is `e_n(a·d)` on a prime-order
  curve, so KS covers the mixed sum over the full group; `deg(bx+cy)=3` ⇒ `4√p`, `+1` for the `d=0`
  pole. **No exceptional `(b,c)` escapes.** *(This bounds `|U|`; it is not a statement about ECDLP.)*
- **Saturation of the bound (M3) — a live asymmetry.** `bx+cy` (dim 4) saturates 0.876 of `4√p`;
  `χ₂(y)` (dim 4, same ceiling, same estimator) saturates **0.470**, converging to ½. **N1.**
- **Structured pairs do not escape KS `[PROVED|KS + VERIFIED]`.** Setting `v=k·u` collapses the
  two-point sum to a **single** bounded-degree readout `F_k(P_u)=A(P_u)B(P_{ku})C(P_{(1+k)u})` with pole
  order `D_k ≈ 2(1+k)²`, so `C_k = O(k²p^{−1/2}) → 0` at fixed `k`. Making `Q=[k]P` *structured* turns
  the object into the shape KS bounds. Witness confirms (M8): `C_k` at the floor for `k ∈ {2,…,64}` and
  the μ₆ cases. **Scope: fixed `k`; `k` growing with `p` is not covered.**
- **Doors with a specific checked reason** *(a list of what has been checked — NOT a claim of
  completeness)*: additive-subgroup (prime order) · MOV on `E` (254-bit, verified not cited) ·
  anomalous (`#E≠p`) · Weil-descent (prime field; GHS proper needs `F_{q^m}`, `m>1`) · H² carry
  (control z=849) · `Hom(E,A_new)=0` (P13).
- **Covariance bound (single-coordinate, given KS) `[PROVED|KS]`.** `|Cov_d(F(x_d),g(d))| ≤
  (max|T|/n)‖F‖_A‖g‖_A`; with KS ⇒ `O(p^{−1/2+o(1)})`, MI `O(p^{−1+o(1)})`. Extends to `(x,y)` readouts
  via the `U` bound. *(A magnitude bound on one-coordinate covariance/MI at the tested scale — not a
  statement about ECDLP.)*
- **Character-sum identities `[PROVED]`.** `Σ_b|T(a,b)|² = p(n−2)`; Parseval `Σ_a|Corr_F|² = ‖F‖₂²`;
  for the aligned readout `Corr(a₀) = √(πn)/2`.

*(`phase_structure_T_v1.py`, `xy_interference_U_v1.py`, `t_y_maxbound_v1.py`, `cheap_partial_shadow_v1.py`,
`bilinear_closure_proof_v1.md`, `structured_pair_bilinear_v1.py`.)*

## The `xy` / joint-(x,y) shadow — real structure `[VERIFIED]`, and the #1 OPEN lead
`xy=x·y` is **odd-in-d + μ₃-weight-1** — the symmetry type the odd half of the spectrum needs and x
cannot see. Odd/even d-spectra carry **equal mass** (`avg|U|²=n` ∀(b,c)). The joint aligned readout
reaches **0.93** — and its `(b,c)`-Fourier support is now **mapped** (`harmonic_support_pattern_v1`,
2026-07-20): **Rayleigh across ~`p²` harmonics, no active/starved split**, and the `l²` budget is
**basis-invariant** (`Σ\|U\|²=p²(n−1)`), so **no unitary basis change can concentrate it**. The M14
scalar-fidelity control does not separate character from random because that statistic is **forced**
equal (M14 note). **What the map left is the one live residue — the sub-Rayleigh deficit (N7 / §XI.15):**
the character's mean harmonic magnitude runs 0.06–0.10% below random, `Z=−13.99`, mechanism-open. Cheap
isotype-pure readouts show no concentration above `φ≈0.1–0.5` (M20), coordinate bits none above the
matched floor (M19); **still open** at larger `n`, in **non-unitary/non-Fourier** bases, and for
multi-bit / multi-point readouts.

---

# PART VII — THE χ₂(y) COVER AND THE SUPERSINGULAR SURFACE `A_new`  *(new in v4; post-dates v3)*

The DLP-relevant sum `V(a)=Σ_P χ₂(y_P)e_n(a·d)` does not live on `E`. It lives on the cover
**`C : w⁴ = x³ + 7`** (`w²=y`), genus 3, with `Jac(C) ~ E × A_new`. This part is the characterization
of that object. **Nothing here is a statement about ECDLP.**

## VII.1 Three separate laws, three separate scopes
- **L1 `[PROVED, elementary; curve-independent; scale-free]` — Part A P2.** `Σχ₂(y_P)=0` at every
  `p≡3 mod 4`. **Applies at secp.** `[VERIFIED 12/12]`. The converse is **FALSE** (non-CM `p=97`
  vanishes accidentally) — stated as ⟺ in the pre-registration and corrected.
- **L2 `[PROVED from automorphisms; VERIFIED 24/24]` — P3, P4, M1.** `A_new` supersingular ⟺ `p` inert
  in `Q(i)` ⟺ `p ≡ 3 mod 4`. **Curve-independent — that is its correct scope, not a defect.**
  ⚠ **N2:** the implication `Q(i)⊆End⁰ + p` inert `⟹` supersingular is verified 24/24 at small `p`,
  **not proved for dimension 2**; applying it at `2²⁵⁶` is an assumption.
- **L3 `[PROVED from automorphisms; NO numerical discriminator]` — P5, N3.** `μ₁₂ ⊆ Aut(C)` ⇒
  `Q(ζ₁₂) ⊆ End⁰(A_new)`, degree `4 = 2·dim` ⇒ `A_new` is a CM abelian surface (applies at secp,
  `p≡1 mod 3`). The numerics are **consistent and non-discriminating**: at the per-prime level the
  Frobenius lands in a `p`-dependent subfield of `Q(ζ₁₂)` (sometimes just `Q(i)`, degree 2), so
  neither the eigenvalue angle, the splitting field, nor `√−3`-membership is a decidable per-prime CM
  invariant. The CM structure surfaces only as a **Frobenius-field density**.

**Why `p ≡ 7 mod 12` is secp's own class:** it is exactly the conjunction of `3 mod 4` (exact vanishing
+ supersingular cover) and `1 mod 3` (`ζ₃ ∈ F_p`, so the μ₃/CM automorphism is defined).

## VII.2 The object at secp
`p_secp ≡ 3 mod 4` ⇒ **`E` is ORDINARY and `A_new` is SUPERSINGULAR at secp itself** (subject to N2).
Supersingular ⇒ `H¹_new` Frobenius eigenvalues are **exactly `√p·ζ`** (roots of unity), not merely
`≤ 4√p` — maximal rigidity. `A_new`'s internal DLP is easy: embedding degree `k = ord_ℓ(p) = 3` at
every tested supersingular prime (M17), so it reduces via pairing to `F_{p³}` — subexponential.
**A supersingular, easy-DLP surface sits in the Jacobian of a degree-4 cover of `E`.**

## VII.3 Three routes checked, with their exact scopes
1. **MOV on `E` directly.** `ord_n(p)=(n−1)/6`, 254-bit; `E` ordinary. Not small. **Blocked —
   verified here, not cited.**
2. **Push `E`'s DLP into `A_new`.** Requires `Hom(E,A_new)≠0`; by Tate that needs a shared `L`-root.
   Measured `gcd(L_E,L_new)=1` **18/18** (M2), and structurally the Newton slopes are disjoint ⇒
   **`Hom(E,A_new)=0` `[PROVED]`, secp-valid (P13).** **Scope: this kills exactly the *homomorphic*
   cover attack, nothing more.**
3. **Cover transfer into `Jac(C)` (genus 3).** The transfer **does exist** — the cover embeds `E` into
   `Jac(C)` up to isogeny, so a DLP instance genuinely moves. Does it help? Genus-`g` index calculus
   costs `Õ(q^{2−2/g})` `[CITED — GTTD/Nagao; Diem for plane curves]`; `g=3` ⇒ `Õ(p^{4/3})` vs `O(p^{1/2})` for Pollard — worse by
   `p^{5/6}`. And `Hom(E,A_new)=0` means the transfer carries the DLP into the `E`-component while
   `A_new` receives nothing. **STATUS (UPDATED v5, gate-cleared — `ANALYSIS_n4_cover_family_indexcalculus_v2.md`): the FAMILY, not
   one cover.** For every genus-`g` cover of `E/F_p`, known index calculus is `Õ(p^{2−2/g}) ≥ Õ(p) > √p`
   (`g≥2`) and genus-1 is slower than `√p`; the subfield-exploiting descent lever needs a proper subfield,
   absent over a prime field. Our cover is a bielliptic plane quartic ⇒ heuristic `Õ(p)` (sharper than the
   `Õ(p^{4/3})` provable figure). **Still OPEN (not a security claim):** prime-field-native Semaev index
   calculus (R1), quasi-subfield constructions (no speedup found), any sub-GTTD algorithm — none
   secp-specific. Route 3 stays OPEN (N4, §XI.13).**

## VII.4 D1 — the non-homomorphic lift, tested
`Hom(E,A_new)=0` kills the homomorphic route, leaving the non-homomorphic lift `Q(P)=[P⁺−P⁻]`,
`P^± = (x_P, ±√{y_P})`. A usable transfer needs `ℓ(d)=dlog_{A_new}(Q([d]G))` **affine in `d`** —
equivalently `Q(d₁)+Q(d₃)−2Q(d₂) ~ 0` for every arithmetic triple, one principality test per triple,
decidable **without computing any discrete log**. **Result (M18): `0/666` additivity, `0/339` affine
triples**, controls fired. **Positive structure recorded, not glossed:** the lift is **non-degenerate**
(exactly half of `E∖O` lifts, forced by `χ₂(−1)=−1`) and lands on **high-order** elements, not
collapsed torsion. **Closed with its scope: the D1 route via an affine/homomorphic transfer. NOT
closed: D2** — the Lang-torsor twist bridge (does the exact `√p·ζ` rigidity survive
`L_{χ₂(y)} ⊗ L_{χ_a}`, giving `V(a)` exact algebraic values structured in `a`?), untouched by this
test; nor a **non-affine but efficiently invertible** `ℓ`.

## VII.5 The ½ saturation — the one measured anomaly with no account
M3/M4/N1. `χ₂(y)` reaches **0.470 → ½** of `4√p` while the same-dimension additive readout reaches
0.876; effectively only **2 of 4** eigenvalues carry weight-1 mass at the maximizing frequency (the
2+2 splitting). `V(a)` is purely real at `p≡1 mod 4` and purely imaginary at `p≡3 mod 4` — exact,
every row — but **parity does not cause the ½** (both classes ≈0.47). **Two distinct real structures;
the ½ mechanism is unidentified.** Twice attempted, twice not closed. **No explanation is offered.**

*(`mu6_cohomology_split_v1..v4.py`, `chi2y_saturation_v1.py`, `d1_fast_affine_v1.py`,
`RESULT_mu6_cohomology_supersingular_v1.md`, `RESULT_supersingular_cover_lever_v1.md`,
`RESULT_D1_lift_affine_test_v1.md`, `RESULT_external_review_idea_tests_v1.md`.)*

---

# PART VIII — SEMAEV / INDEX-CALCULUS

- **`S₃` irreducible/ℚ `[VERIFIED]`.** The `2·7` term is **correct** — do not "fix" it (§XII.22).
- **`C_t` smooth genus-1 for every `t∈F_p` `[VERIFIED — mechanism explicit]`** — P14.
- **`Δ(t)=−86704128(t³+7)⁴` — `[UNREPRODUCED]`.** Roots reproduce (`t³=−7`); constant/exponent do not
  (Weierstrass `y²=x³+7c³` gives `−355140108288(t³+7)⁶`). Not relied on downstream.
- **First-fall degree — `[HEURISTIC + CITED]`** *(the grade v3 carries; do not read the isobaric
  sub-fact as upgrading it).* **Proved sub-fact `[PROVED isobaric, all m]`:** `S₃` wt 4, `S₄` wt 12; leading forms
  free of `A,B`; `S₄` (deg 12, 35 monomials) and `S₅` (deg 32, 495 monomials) leading forms identical
  across 4 curves. *(The implication "isobaric ⇒ first-fall is curve-independent" was `[PROVED,general
  m]`, re-graded `[HEURISTIC+CITED]` in §XII.8; the isobaric fact itself is proved.)*
- **Solving degree also curve-blind `[VERIFIED, p≤307, m≤4]` (M9).** On an *identical* `V` and target
  across secp / non-CM / j=1728 — so the only difference is the lower-order `A,B` terms of `S₄` — the
  first-fall **and** solving degrees are identical (`d_ff=12`; `d_solv=15/18` at `B=2/3`; `|V|=3`:
  12/17/3 all three). **The one place a j=0 CM lever could hide is curve-blind at the tested scale.**
- **`S₄` singular-fibre locus `[VERIFIED]`.** Eliminating `x₁,x₂,x₃` from `(S₄,∇S₄)` gives the **zero**
  `t`-ideal — the singular locus is the diagonal `xᵢ=xⱼ` present in every fibre, **identically** for
  secp (0,7), non-CM (5,11), j=1728 (3,0) at `p=211` and `p=307`. No `B=7` collision.
- **`x·y` substitution cannot lower the degree `[reasoned + checked]`.** `w=x·y` satisfies
  `w² = x⁵ + B·x²` (x-degree 5, verified `B=7,11,0`) — **higher** degree than `S_m`, not lower. And
  `μ₃-weight(xy) = weight(x) = 1`, so `xy` carries the same grading as `x`.
- **S₄ leading form = the cusp `y²=x³` summation polynomial `[VERIFIED]`** (→ additive `Σuᵢ=0` at
  infinity); every `S₄` fibre singular exactly on the diagonal (generic to symmetric polys).
- **Scope of the whole part:** `p ≤ 307`, `m ≤ 4`. It does not speak to `p=2²⁵⁶`, to `m ≥ 5` (where the
  solving degree could in principle diverge), nor to non-Semaev index calculus.

*(`semaev_elimination_v1.py`, `semaev_pieceA_matched_v1.py`, `_audit_semaev_matched_largerV_v1.py` — Sage;
`RESULT_semaev_cm_lever_v1.md`.)*

---

# PART IX — SUBSTRATE  `[VERIFIED at small p — banner]`
secp at criticality (`|π|=√p`); `|T|²`~Porter–Thomas (thermal, no scar); transfer spectrum mixing
beyond μ₆ (no metastable soft mode; `|λ₂|~1/√n`). The `LRC→φ(n)→Berry–Keating→ζ` programme spans **two
substrates, bridged**: chaotic-GUE (ζ zeros, secp) vs rigid-arithmetic (LRC φ(n) totatives = hard-gap;
Berry–Keating `{πk²}` = picket-fence). "One programme" = the bridge, not one substrate. *(A
rigid/thermal magnitude statement — not a structure-absence claim.)*

---

# PART X — THE σ×χ₂ CONSERVATION PROGRAMME

The flap-sign × quadratic-character pairing is the **one live cross-class object** left by Claim F
(Part III): at `p≡3 mod 4`, `σ` and `χ₂` **share** field bidegree `(1,0)`, so Claim F does **not** force
the zero. Following it lands on the class number of `ℚ(√−p)`.

## X.1 The counting law, with forced cells removed
`σχ₂` is μ₃-invariant (`σ(βx)=σ(x)`, `χ₂(β)=1`) **and** field-even at `p≡3 mod 4` (odd×odd) ⇒ **μ₆(F_p)-
invariant**; the flap is μ₆-stable ⇒ `6 | flap` ⇒ **`FLD = 6·S`** with `S` a sum of `ORB := flap/6`
signs ⇒ **parity obstruction `S ≡ ORB (mod 2)`** (pre-registered; verified at every prime).

| regime | `FLD` | count | status |
|---|---|---|---|
| `p ≡ 1 mod 4` | `= 0` | 19/19 | **FORCED** by Claim F (field-parity mismatch) |
| `p ≡ 3 mod 8` | `≠ 0` | 29 primes | **FORCED nonzero** by the ORB parity obstruction — **carries ZERO information; must not be counted as evidence** |
| `p ≡ 7 mod 8` | `= 0` | **35/35** | **NOT FORCED ← the finding** (22/22 in-sample + 13/13 out-of-sample on fresh primes `[8000,14000)`) |

**Power:** parity *permits* `S=0` in the `p≡7 mod 8` regime; a generic signed sum would give
`Σ 2/√(2π·ORB) ≈ 1.86` expected zeros in-sample. Observed 22/22. **This is an exact law, not a
magnitude.** **Sub-law `H1`, 64/64:** `ORB = flap/6` is even ⟺ `p ≡ 7 mod 8` — a **Cap-Law-level
lattice fact** (flap cardinality mod 12), independent of any curve arithmetic. `p mod 8` is `χ₂(2)`.
**Mechanism hunt: the natural candidate is RULED OUT** — no `c∈F_p*` with `σχ₂(cx)=−σχ₂(x)` exists
(exhaustive at `p=127,823,967,991`). Whatever enforces `S=0` is **not** a multiplicative sign-flip.

## X.2 `|FLD| = 6·h(−p)` — the class-number law
- **The law (M11) `[EMPIRICAL, exact match]`.** `FLD(p)=0` unless `p≡19 mod 24`; `|FLD|=6·h(−p)` there.
  34/34 nonzero (h ≤ 11) + 103/103 zero, `p ∈ [100,2000)`. `p≡19 mod 24` = `(χ₂(2)=−1) ∧ (μ₃ present)`.
- **Reduction chain (status-tagged).**
  - `[PROVED]` `p≡1 mod 4` ⇒ `FLD=0` (negation antisymmetry); `p≡3 mod 4` ⇒ `FLD = 2·S+`.
  - `[VERIFIED 86/86, NOT proved]` **L1:** `|S+| = F4 = Σ_{p/4<a<p/2}χ₂`.
  - `[PROVED here]` **L2:** the `a→2a` fold gives `E4 = D(1+χ₂(2))/(2χ₂(2))`, so `F4=0` at `p≡7 mod 8`,
    `F4=D` at `p≡3 mod 8`.
  - `[CITED — Dirichlet]` `D = (2−χ₂(2))·h`. `[VERIFIED classical]` first moment `Σa·χ₂(a) = −p·h`.
  - Chaining ⇒ `|FLD| = 6h` at `p≡19 mod 24`, else 0 — **modulo L1 alone.**
- **⚠ Grade discipline.** This is **not** `[PROVED]`. Anyone quoting "the Class Number Law" must carry
  "modulo L1, verified 86/86, not proved" with it (§XI.8).
- **The enforcing symmetry is outside `F_p` `[VERIFIED + reasoned]`.** The reflection candidate (D₆'s
  six reflections `z→ζ₆ᵏz̄`) is killed exactly (0/16 flip `σ·χ₂`): conjugation `ω→ω²` does not descend
  to the prime field (no nontrivial `F_p` automorphism; it maps the ideal to the conjugate prime = the
  twist). Its home is the lattice / biquadratic field `ℚ(√−p, √−3)`, whose `p mod 24` splitting **is**
  the vanishing law.
- **L1 status, no verdict either way.** Verified 86/86, not proved. Routes tried and their outcomes:
  single-interval image (`T+` is a lattice-line∩triangle, 6–33 scattered runs — not an interval);
  multiplicative set-stabilizer (none flips `σ·χ₂`); first-moment/carry fold (**dissolves**: the carry
  `k=σ`, so `T1 = χ₂(M)·p(1−χ₂(2))h + p·FLD` — FLD plus a Dirichlet term, no independent handle on
  `S+`; verified 55/55). **Neither "needs analytic machinery" nor "elementary and reachable" is
  claimed — both were asserted earlier and retracted (§XII.12, §XII.13).**
- **Sign of FLD `[VERIFIED consistency, not intrinsic]` — the gauge sub-question is settled; the sign
  is unresolved.** `sign(FLD) = −χ₂(M)` (54/54 at
  `p≡19 mod 24`). The v1 headline ("their product is constant across 8 basis presentations, 792/792 —
  so the sign law is a function of the lattice") is **withdrawn (§XII.21)**: the full 24-element
  ordered-basis orbit produces **exactly 2 distinct `σ` vectors** (`σ` and `−σ`, 232/232 globally), at
  29/29 primes, because `σ` is odd and μ₃-invariant so μ₆ acts through `μ₆/μ₃ ≅ {±1}`. **8 presentations
  → 2 configurations ⇒ `792/792` was 99 forced bits, not evidence.** Consequently the `π_p↔π̄_p`
  chirality check is **void, not open**: `X∈ℤ` is conjugation-fixed ⇒ `σ'=σ` pointwise ⇒ `sign(FLD)`
  cannot flip. **But the sign-pinning still reads as an internal consistency between two
  reduced-basis-dependent quantities, NOT shown to be a deeper arithmetic symmetry** — `χ₂(M)` and
  `sign(FLD)` reduce to **none** of ~25 tested intrinsic invariants (`χ₂(2/3/√−3)`, `π_p` components,
  `sign(L)`/`χ₂(L)` from `4p=L²+27M²`, `χ₃(2)`, `p mod 48`). **This does not refute the "sign possibly
  convention-dependent" flag. The magnitude `|FLD|=6h` is the intrinsic result; the sign is
  unresolved** (§XI.9).

## X.3 The joint-shadow / isotype work
- **VIII-era results carried forward:** M14 (0.93 with its magnitude control), M15 (equipartition, the
  deficit = the excluded fixed point `d=0=O`), M16 (the `U`-built readout is forced μ₆-symmetric and
  cannot separate `d`), M20 (six μ₆-isotype-pure cheap readouts at the `φ≈0.1–0.5` floor; null = orbit-
  value permutation, the dilation `d→cd` explicitly excluded; controls fired: identities 0, purity
  ≤1e-15, planted φ=1 → `R_orb=1`).
- *(Side observation, not a leak: `Legendre(x)` is **over-dispersed** — flatter than the null,
  pR=1.0000 — the low discrepancy of the quadratic character sum; the anti-concentration direction.)*
- **M19, the bit-readout arm — the LBE-shaped test that has already burned twice.** v1 reported
  `x&1` z=5.80, `hi(x)` 5.33, `hi(y)` 7.91 — an "ESCAPE" — **but every readout showed rank-p = 0.0033**,
  a *systematic* shift = the tell of a symmetry-mismatched null. Mechanism: `x_{−d}=x_d` exactly ⇒
  `x&1, hi(x), x mod 4, x&15` are **even in `d`**; `y&1, hi(y)` complemented-even; the value-permutation
  null destroys that μ₂ symmetry. Against the `{d,n−d}`-orbit-matched null: `z ∈ [−1.05, 2.34]`.
  **This is retraction #6 recurring, and it is the single most likely failure mode of Part 0.**

*(`joint_shadow_decompose_v1.py`, `joint_shadow_mu3_v1.py`, `joint_shadow_cheap_isotype_v1.py`,
`bit_readout_leak_matchednull_v2.py`, `_sigma_chi2_scan_v1.py`, `_fld_classnumber_check_v1.py`,
`_fld_L1_fold_v1.py`, `_fld_interval_v1.py`, `_fld_involution_hunt_v1.py`,
`_reflection_symmetry_hunt_v1.py`, `twist_gauge_covariance_v1.py`;
`RESULT_joint_shadow_decompose_v2.md`, `RESULT_joint_shadow_mu3_v1.md`,
`RESULT_cheap_isotype_concentration_v1.md`, `RESULT_fld_classnumber_v2.md`,
`RESULT_reflection_conservation_hunt_v1.md`.)*

---

# PART X-bis — HOW IT FITS  (what is established; what it does not establish)
*(carried from v3 Part IX; v4 first dropped this Part, restored by the compile-diff audit)*

1. **Prime-order rigidity `[PROVED]`** (P14) ⇒ the only chaining readout is `d`; forces `C_t` smooth
   and `σ⊥s_y`; bounds the amicable transfer **only in the homomorphic case**.
2. **KS/Weil–Deligne `[PROVED|KS]`/`[PROVED|WD]`** (P6a/P6b) ⇒ every **bounded-degree** cheap readout —
   additive or χ₂ — is spectrally flat (a `√p` floor) **at the scales tested**.
3. (1)+(2) ⇒ concentration ≡ chaining ≡ correlation-with-a-character, **for bounded-degree readouts**.
   For general poly-time readouts there is **no reduction in hand** (`[GAP]`, N5, Part VI-3).
4. The μ₆-symmetric part of the joint readout is provably flat (M16); the cheap μ₆-isotype-pure
   complement is bounded above a power floor (M20); an exact conservation turns out to be a **class
   number** (M11) whose enforcing symmetry lives outside `F_p`; and the χ₂(y) readout lives on a cover
   whose new factor is supersingular (Part VII). **None of this is a statement about ECDLP.**
5. **What this does NOT say.** It does not say the doors are exhaustively mapped; **it does not say the
   DLP is the sole residual**; it does not say ECDLP is hard. The frontiers below are live. In
   particular the 0.93 shadow's **frequency-pattern** basis (M14/§XI.1), the **non-covariant cheap**
   readouts (M19), and the **½-saturation mechanism** (N1) are exactly the "right basis not yet found"
   places the language rule warns about.

---

# PART XI — LIVE FRONTIERS  *(carried from v3 §X unless a resolving artifact is named; renumbered)*

1. **A cheap *partial* of the joint (x,y) shadow** *(H3 verbatim)*: "…Can a cheap readout capture a
   *fraction* of that alignment? **Highest-value lead.**"
   → *Status: **PARTIALLY ADDRESSED, STILL OPEN.** Bounded by M20 (6 μ₆-isotype-pure readouts, no
   concentration above `φ≈0.1–0.5`), M14 (the 0.93 scalar magnitude does not separate character from
   random in the scalar-fidelity statistic), M19 (6 coordinate bits at the matched floor, one curve).
   **Frequency-support map: RAN, and it dissolved the concentration hope** (`harmonic_support_pattern_v1`,
   2026-07-20) — the joint readout is **Rayleigh across ~`p²` harmonics, no active/starved split, `l²`
   basis-invariant** (`Σ\|U\|²=p²(n−1)`, so no unitary basis change can concentrate it); it produced the
   one surviving anomaly, the **sub-Rayleigh deficit (N7 / §XI.15, `Z=−13.99`)**. **Still open, named,
   outside every test run:** **non-unitary / non-Fourier bases** of the shadow; **higher-degree joint
   readouts** (carried verbatim from v3 VIII.1); the `N_eff`
   multi-frequency channel at large `n`; **the non-μ₆-covariant cheap readouts** (raw coordinate bits —
   `x mod 2`, high bits of `x`), which live outside the μ₆ decomposition and which M19 bounds on
   **one curve at one `n` only**; multi-bit and multi-point joint readouts; sub-floor `φ`; larger `p`.
   **This is Part 0's primary target.***
2. **The odd-half / `T_y` max-bound.** → ***RESOLVED-BY `kohel_shparlinski_ants4_2000.pdf` (2026-07-17).***
   `max|U(a,b,c)| ≤ 4√p+1`, uniform, explicit, no polylog; no exceptional `(b,c)` escapes. §XII.11.
3. **Non-homomorphic amicable map.** → *OPEN. **Only the group-homomorphism case is ruled out**
   (Hom=0, coprime orders — §XII.4). The CM relation `π_n = π_p − 1` as a **non-homomorphic
   correspondence remains UNANALYZED**; the protecting lift obstruction is `[HEURISTIC]` (xedni).*
4. **`S₄⁺` / first-fall / solving degree — prime-field Semaev (R1).** → *OPEN, and REOPENED v5.
   Isobaric leading-form curve-independence `[PROVED, all m]`; the first-fall-DEGREE curve-independence it
   implies is `[HEURISTIC+CITED]` (§XII.8, retraction #8), `[VERIFIED]` at tested scope; narrowed by M9.
   **The prior matched solving-degree null
   (`RESULT_semaev_cm_lever_v1`) is re-scoped** (`RESULT_semaev_dsolv_statistic_power_v1`): its "clean"
   arm was the INCONSISTENT regime, whose solving degree is governed by the curve-independent leading
   forms ⇒ **provably curve-blind, no power.** The powered CONSISTENT regime was only measured UNMATCHED;
   there both CM curves (secp μ₆, j1728 μ₄) show MORE decompositions per target than non-CM (a
   generic-CM, NOT secp-specific, decomposition-count effect growing with `|V|`), confounded by group
   order at `p=211`, and NOT a solving-degree drop. **Open: a matched, group-order-controlled
   consistent-regime test (pre-registration owed); `m≥5` (S₆ build intractable in current harness);
   larger `p`; non-Semaev index calculus.***
5. **Everything at secp's actual `p`.** → *OPEN and global — the banner. **No measurement at `p ≈ 10⁵`
   has power against a structure at `2²⁵⁶`: a gap of ~239 binary orders of magnitude that governs every
   `[VERIFIED]`/`[EMPIRICAL]` conclusion in this document.***
6. **`C_T` inter-coordinate coupling.** → *OPEN — bounded-by `ANOMALY_DRILL_01` +
   `RESULT_ct_coupling_universality_v1`. Any coupling `< ~1.6%` in the Frobenius-norm estimator at
   `n≈1.3×10⁵`, this orbit/generator, `p≤2¹⁷`. **The refutation of the 2–3% split is empirical (a fired
   zero-coupling surrogate + pooled G² p=0.40), not analytical (§XII.25).** Next: `‖D_odd‖_F` at
   `n~10⁶–10⁷`, vary generator/prime.*
7. **Two-point / joint-SET bilinear bound.** → *NARROWED. The **diagonal** slice `v=k·u` is
   **KS-covered at fixed `k`** (Part VI, M8). **Open: `k` growing with `p`; genuinely joint multi-key
   readouts of the SET `{x([dᵢ]G)}`; the full two-point panel beyond **Theorem B** (`bilinear_closure_proof_v1.md`: the two-point sum
   over independent `(u,v)`, `|S|/n² = O(p^{−1/2})`).***
8. **L1: `|Σ_{T+}χ₂| = F4`.** → *OPEN. Verified 86/86; a proof would complete `|FLD| = 6h(−p)` and move
   M11 from `[EMPIRICAL]` to `[PROVED]`. It is a lattice-line∩triangle character sum equal to a
   quarter-interval sum.*
9. **FLD-sign intrinsic-ness.** → ***OPEN, carried verbatim from v3:*** *"`sign(FLD)=−χ₂(M)` verified
   54/54 but reduces to no tested intrinsic invariant."* **The substantive item remains open and
   unchanged.** Only its named *sub-check* is void: the `π_p↔π̄_p` chirality probe is
   `resolved-by RESULT_twist_gauge_covariance_v2` §5.2 (`X∈ℤ` is conjugation-fixed ⇒ `σ'=σ` pointwise
   ⇒ `sign(FLD)` cannot flip) — **do not run that probe**; that artifact explicitly declines to resolve
   the frontier itself. *(v4 first struck this whole item on the strength of the sub-check; restored by
   the compile-diff audit. Voiding a decisive check is not closing the question it was meant to
   decide.)*
10. *(new, v4)* **The mechanism of the ½ saturation (N1).** → *OPEN. `χ₂(y)` saturates 0.470→½ of
    `4√p` while same-dimension `bx+cy` saturates 0.876 — a 1.86× systematic gap at identical dimension
    that a max-over-frequencies artifact cannot produce. Effectively 2 of 4 eigenvalues carry weight-1
    mass at the maximizing frequency (the 2+2 splitting). **Twice attempted, twice not closed; no
    explanation is offered.** Next: D2 (the Lang-torsor twist bridge — does `√p·ζ` rigidity survive
    `L_{χ₂(y)}⊗L_{χ_a}`?).*
11. *(new, v4)* **Is `A_new` supersingular at secp? (N2)** → *OPEN as a proof obligation. The
    automorphism input is `[PROVED]`; the step `Q(i)⊆End⁰ + p` inert `⟹` supersingular is verified
    24/24 at small `p` and **not proved for dimension 2**. This is load-bearing for all of Part VII.*
12. *(new, v4)* **A discriminating numerical signature for the CM layer L3 (N3).** → *OPEN. Both
    designed tests failed. A real test would target the **CM type** (the specific embedding of
    `Q(ζ₁₂)` on the tangent space), not which field `L_new` splits over. Also open: the supersingular
    order sets `{1,3}` vs `{3,4}` (M6) need a larger sample before they are a law.*
13. *(v4; UPDATED v5)* **Cover transfer into `Jac(C)` — Route 3 (N4).** → *OPEN, now CHARACTERIZED over
    the whole family (`ANALYSIS_n4_cover_family_indexcalculus_v2.md`, gate-cleared): no genus-`g` cover of
    `E/F_p` beats Pollard by KNOWN index calculus (`Õ(p^{2−2/g})≥Õ(p)`, `g≥2`; genus-1 slower than `√p`);
    subfield-exploiting descent has no input over a prime field; our cover = bielliptic plane quartic ⇒
    heuristic `Õ(p)`. **Residual OPEN = live lever:** prime-field Semaev (R1, §XI.4), sub-GTTD algorithms,
    **D2**, a non-affine but efficiently invertible `ℓ`.*
14. *(new, v4)* **The growing-degree corner of the character-sum bounds (N5).** → *OPEN `[GAP]`. The KS
    constant grows with readout degree; for general poly-time readouts there is no reduction in hand.*

15. *(new, v6 — restored from `RETROSPECTIVE_FINDING_01_subrayleigh_demotion_v1.md`; was Frontier #17 in
    ADDENDUM_2, dropped in the v3→v4 Part-XI renumber and absent from v4/v5)* **The sub-Rayleigh deficit
    (N7) and its mechanism.** → *OPEN `[EMPIRICAL]`. The DLP character's mean harmonic magnitude runs
    0.06–0.10% below a random unit-phase target's, one-directional **7/7 primes**, pooled **Z=−13.99**,
    universal over 24 characters, **persistent** across a 79× `p`-range (decay excluded ≫8σ,
    `RESULT_subrayleigh_deficit_scaling_v1`). Survives the exact value-multiset matched null; two
    mechanisms ((0,0)-exclusion, Weil ceiling) refuted **without** refuting the effect — the project's
    cleanest "refuting a mechanism ≠ refuting the claim" case, and the one live residue of §XI.1. **Live
    mechanism candidate:** the row-budget shadow (per-frequency conservation `Σ_a\|U(a,b,c)\|²=n(n−1)`;
    `row_budget_lowtail_v1..v3`, F11 confirmed). **Under active investigation** — the arithmetic-scatter
    question (does the scatter compress to the Frobenius `a_p`?) is a parallel effort. Scope: enumerable
    model `p` only; no transfer to secp.*

16. *(new, v7)* **The source of the census identity `e₂=e₁²−χ₂(−1)p` (N8).** → *OPEN. The
    twist-discriminator PASS at **1171/1171 cells, 11 primes `43≤p≤1303`** is, by the exact symbolic
    reduction P16 (`twist_identity_reduction_v1`), **equivalent to this one scalar identity per cell** —
    strong evidence of an exact law, no account of its force. Reframes the "tensor-decomposition
    discriminator" from a 4-dimensional test to: **why this `e₂` identity?** Next: its representation-
    theoretic / geometric origin; the Katz Kummer-sheaf mechanism (§XIII.6). `[scale banner: p≤1303]`.*
17. *(new, v7)* **The `W`-piece and the `SL₂`-monodromy on `L/Q(ω)` (N9, N10).** → *OPEN. `ξ=ζ₃`
    constant is pinned (M22); the explicit 2-dim `W` is not. The algebraic-number layer (M23) locates
    two strata — the `Q(ω)`-layer and the degree-20 non-abelian `L/Q(ω)` — consistent with a
    `W⊕W⊗ξ` / `SL₂`-monodromy picture but not proving it. Concrete target: is `L/Q(ω)` generated by the
    predicted `SL₂` action? Exact group unpinned (degree 40 beyond PARI/KASH; needs Magma/resolvent).
    Owed: a `χ₂(−1)=+1`-branch confirmation of the mult-3 law.*
18. *(new, v7)* **The universal phase channel's secondary structure (M24).** → *OPEN as a
    characterization, not a leak. The `k=3`, `χ₂(b)`-coupled conditional channel is mechanism-explained
    (real-weight `μ₂` + cubic degree); its **amplitude** `A(E,a₀,p)∈[0.2,0.6]` carries curve-type-dependent
    secondary structure (`j=0` ≈0.51 > non-CM ≈0.43 > `j=1728` ≈0.32) not yet characterized. A refinement
    of Part V: the `x`-only channel is fully accounted, and adding `y` (the `xy` odd-half) puts the phase
    at the random floor — consistent with the Part V/VI closures. `[EMPIRICAL, p∈[5000,65000]]`.*

**Also live (lower stakes):** full-resolution `σ₁,σ₂` boundedness; is `ε` an arithmetic object
(symbol/norm condition)?; large-prime rank-10 μ₃ split; the `λ₂` transfer eigenvector ~50% μ₃-covariant
/ `λ₃` up to 85% (real, broadband, no closed form); a `p mod 8` law for `⟨σ,χ₃⟩` or `⟨eps,χ₂⟩`;
deriving `H1` (`ORB` parity) from the Cap Law's continuum geometry; an unconditional Part VI (needs
Weil–Deligne + KS reproved — a `[GAP]`). Cross-project: finite-field zeta as an RH test-bench;
LRC↔μ₆/μ₂ shadow.

---

# PART XII — RETRACTION LEDGER  *(1–13 carried from v3 §XI — see the note at the end of the Part on three dropped cross-reference
fragments; 14–26 new in v4. Do not re-claim any of these.)*

1. χ₂ "doubling transport law" → the textbook duplication formula. CITED, not a finding.
2. Test-A cubic-moment "null" → zero statistical power (N=82 needs f=1.0).
3. G "tested the blind corner" → tested a proxy (`d mod k`, a known-null hardcore bit).
4. v11 amicable "wall" → strawman; only the group-homomorphism case was ruled out. *(Re-claimed by v1,
   withdrawn again; §XI.3.)*
5. v14 "the ‖F‖_A gap is the only analytic door" → wrong; Wiener norm is a red herring.
6. v17 "6–7σ soft shadow" → a null-mismatch artifact (shuffle null destroyed the μ₆-invariance the
   readout has by definition). Against the correct μ₆-invariant null, z≈0.
7. aligned-leak scaling `~1/√log p` → retracted; data drift over too small a `p`-range.
8. `[PROVED, general m]` first-fall curve-independence → `[HEURISTIC+CITED]`; the isobaric fact is
   verified, the implication is not.
9. **"no concentration ⟺ ECDLP hard" → withdrawn.** `⟸` trivial; `⟹` has **no reduction in hand** from
   a lack of concentration to hardness.
10. **"KS bound covers χ₂" → withdrawn.** KS's Ψ is **additive** (proof via Artin–Schreier); **χ₂ is
    multiplicative** (a Kummer argument is a different theorem, not cited). χ₂'s flatness rests on the
    separate `‖F‖_A` argument. **Do not re-claim that KS bounds χ₂.**
11. "KS / Lange–Shparlinski" pairing for the mixed sum → withdrawn. **KS alone** carries it; L–S
    Lemma 2.4 bounds the untwisted `Σ_P χ(f(P))`, no `ω(P)` factor. Do not re-pair.
12. **"L1 needs analytic machinery / an honest wall"** → withdrawn. Asserted from three failed
    elementary probes; the `a→2a` fold (elementary) applies to `T+`. A difficulty verdict dressed as
    honesty.
13. **"L1 elementary and reachable through the first-moment formula"** → withdrawn. Built on two
    unchecked, narrow-sample-generalized formulas: `Σa·χ₂(a)=−p(2−χ₂(2))h` (WRONG; it is `−p·h`,
    120/120) and `Σχ₂(a)c(a)=0` (WRONG; it is `p(1−χ₂(2))h`). The corrected algebra shows the
    first-moment thread **dissolves**. Neither the wall nor the reachability claim was earned.
14. *(new, v4)* **"± flap counts are EXACTLY equal"** → **dissolved as a field-level conflation.** The
    recorded mechanism (`σ(−x)=−σ(x)` + `F_p*` negation-closed) is a statement about the **FIELD** and
    does not transfer to the curve, because `x→−x` maps `X(E)` to the x-set of the **sextic twist**.
    `(B1)=Σ_{x∈F_p*}σ(x)=0` `[PROVED]`; `(B2)=Σ_{P≠O}σ(x_P) = (B1)+C = C`, and **`C ≠ 0` generally**
    (49/49 exact, `C²/p ≤ ~3.7`). **Never restate this without saying "field".** *(Dissolution is a
    positive result: the sharper law is `(B2)=C`, and the mechanism is explicit — the curve part lost
    the `ℤ/2` that annihilates the field part, and lost it to the sextic twist.)*
15. *(new, v4)* **Bit-readout "ESCAPE" (5.80σ / 5.33σ / 7.91σ)** → **μ₂-symmetry null mismatch**
    (`x_{−d}=x_d`), a **re-occurrence of #6**; collapses to `z ∈ [−1.05, 2.34]` against the
    `{d,n−d}`-orbit-matched null. The tell was a *systematic* rank-p = 0.0033 across **every** readout.
16. *(new, v4)* **"`p≡7 mod 12 ⇒ √p·ζ₆`, a CM fingerprint"** → **FALSE.** CM `p=19` gives `ζ₂`; non-CM
    `p=43,79,103` give `ζ₆`; at `p=43,79` a non-CM curve gives the **byte-identical `L_new`** with the
    same ζ₆ angles. The ζ₆ is **geometric supersingularity** (μ₄ ⊂ Aut(C), any cubic), not CM.
17. *(new, v4)* **"`√−3` in the splitting field = a CM detector"** → **FALSE.** Non-CM shows `√−3` at
    `p=37,43,61,73,79`. And **"`L_new` splits over `Q(ζ₁₂)`" is uninformative by design** — it passes
    trivially when the roots already lie in `Q(i) ⊂ Q(ζ₁₂)` (non-CM passed 5/6).
18. *(new, v4)* **"non-CM splits over `Q(i)`"** → **FALSE, and the reasoning was wrong**: `Q(i)` has
    degree 2 acting on a **dim-2** `A_new` — degree 2, not `2·dim = 4` — so it is not CM and `π` need
    not lie in `Q(i)`. Observed 2/6 (CM 1/6). No separation.
19. *(new, v4)* **The `int1_frame_operator_v1.build` β-calibration** used a **single hardcoded probe
    `x=12345 = 3·5·823`**; at `p=823` the probe is `x≡0`, the test degenerates, and the **wrong root**
    is returned (0/822 exact `ω²` relations, carry classes garbage; the correct `b2=174` gives 822/822
    and flap/822 = 0.248 ≈ ¼). **`p=823` is the unique affected prime among `p≡1 mod 6`; secp is
    unaffected.** Any small-prime sweep that included `p=823` via that import produced garbage there,
    **silently**. The Cap Law is **not** contradicted — `p=823` was never a counterexample. Fix applied
    in `isotypic_selection_rule_v1.py` / `_sigma_chi2_scan_v1.py` (many probes, assert exactly one root
    qualifies). **Not yet fixed in the original file.**
20. *(new, v4)* **The σ×χ₂ tallies `64/64`, `42/42`, `20/20`** → **corrected to `35/35` unforced**
    (22/22 in-sample + 13/13 out-of-sample). `64/64` counted the parity-**forced**-nonzero regime as if
    it were evidence; `20/20` was the count of *all* `p≡3 mod 4` primes in `[8000,14000)`, not the
    `p≡7 mod 8` ones — denominator-mixing that produced the inflated `42`. **The law survived the
    audit; the tally did not.**
21. *(new, v4)* **"`sign(FLD)·χ₂(M)` constant across 8 basis presentations (792/792) ⇒ the sign law is
    a function of the lattice"** → **withdrawn.** The gauge group produces **exactly 2 distinct `σ`
    configurations** (`σ`, `−σ`) across the full 24-element orbit, at 29/29 primes — forced by `σ` odd
    + μ₃-invariant. **8 presentations → 2 configurations ⇒ `792/792` was 99 forced bits**, and the
    "theorem" reduces to `0 = −0`. **Before claiming invariance over `N` instances, count the group's
    DISTINCT configurations.**
22. *(new, v4)* **"The `2·7` in `S₃` is a typo"** → **do not 'fix' it.** It is the `2B` slot of the
    general `S₃` with `B=7`, survives `A=0`, and vanishes on **1406/1406** collinear secp triples;
    deleting it gives **0/1406**.
23. *(new, v4)* **"μ₃-closing raises the solving degree (`d_gb` 6 vs 3)"** → **retracted.** A
    `p=211`-only number; at `p=307` the same test gives `5 vs 5`. Worse, `d_solv = None` in every μ₃
    cell, so the comparison rested entirely on `d_gb` — a **proxy** for the degree of regularity —
    whose magnitudes do not reproduce across two primes. **What survives:** a β-invariant `V` never
    produced a *lower* `d_gb` than a random `V` (weak, proxy-based, two primes). **Do not cite "μ₃
    raises the solving degree."**
24. *(new, v4, standing)* **The residue-vs-component tautology.** Never correlate a residue `r = v − w`
    against `w`: it produces huge spurious MI (z ≈ +5000) that **the shuffle control does not expose**,
    because shuffling breaks the artifact exactly as it breaks real signal. **Leakage tests need a
    disjoint-construction feature and target.**
25. *(new, v4)* **"The `C_T` 2–3% split was refuted analytically as finite-`n` noise"** → **overstated.**
    The refutation is **empirical**: a zero-coupling surrogate reproduces the residual (z=+1.6/+0.1),
    pooled G² p=0.40, and the universality sweep gives `ε̂ ≤ 0.025` with `z_G²` up to +4.46 at one
    prime. The tensor law `C_T = C₁ ⊗ C₁` **is** confirmed more tightly (block trace 7.5e-5 from `2/3`;
    the degenerate block splits into exact swap-even and swap-odd channels), but the coupling statement
    is a **bounded magnitude with a stated floor (`ε ≳ 1.6%` detectable at `n≈1.3×10⁵`, zero power
    below, zero power at `2²⁵⁶`)** — not an analytical refutation.
26. *(new, v4)* **Two dismissals-by-declaration, both withdrawn.** (a) "The χ₂(y)-cohomology thread is
    geometric, not CM, **bound-irrelevant**, does not touch ECDLP" — the ζ₆-is-geometric finding stands,
    but **supersingularity is the classical ECDLP lever** (MOV / Frey–Rück) and secp's `p ≡ 3 mod 4`,
    so it is a pointer to a supersingular easy-DLP object in the cover's Jacobian. (b) "No MOV/pairing
    transfer follows; `A_new` is auxiliary" — a declaration, and careless, since **cover-based DLP
    transfer (GHS / Weil descent) is a real attack family and `C→E` is exactly a cover.** Both replaced
    with the three decidable route-checks of §VII.3. (c) Similarly withdrawn: "χ₂(y)'s ≈2√p is a
    max-over-frequencies artifact" — that argument compared **raw** values and erased the normalized
    object; the saturation table (M3) refutes it.

*(Carry note on 1–13: three cross-reference fragments of v3's wording were dropped in the v4 restatement
— the "` (VIII.4)`" pointer in #12, and in #13 "— no independent handle on S+ (verified)" and "; both
were flagged by the self-certifying word 'honest.'" The substance of all three survives in §X.2 and in
the process note below; recorded here so the successor knows they were shortened, not lost.)*

*(Process note carried forward: the recurring failure mode is reaching for "honest/honestly/genuinely"
exactly when asserting unchecked algebra or generalizing from a few primes. The fix is to run the check
the word papers over. See feedback memories `self_cert_words_audit_trigger`,
`negative_bias_enlarge_nulls`, `prereg_abstention_is_the_finding`.)*

---

# PART XIII — THE COHOMOLOGICAL TENSOR / SPLITTING-FIELD LAYER  *(new in v7; folds ZCode `tensor-decomp` 2026-08-09 + `RESULT_algebraic_number_layer_v1.md` 2026-07-31)*

*Deepens Part IV (CM / L-function / twist) and Part VII (the χ₂(y) cover / `A_new`). Governed by the
scale banner: exact arithmetic, but at `p ≤ 1303`. One positive exact law and one field-theoretic
structure — stated with care about what the headline "1171/1171" does and does not establish.*

## XIII.1 The object and the hypothesis
`C : w⁴ = x³ + 7`; `H¹_c(C, L_{χ₂(y)} ⊗ L_{χ_a})` carries a degree-4 Frobenius `L*(T)` at each cell
`a∈F_p^×`. The **120° law** is `g = deg gcd(L*(T), L*(ζ₃T)) ≥ 2` for every cell — a `ζ₃`-pairing of the
four eigenvalues. The **tensor-decomposition hypothesis** is the stronger `H¹ ≅ W ⊕ (W⊗ξ)` for a 2-dim
`W` and an order-3 unramified `ξ`; it *implies* the 120° law and constrains the full 4-dim module.

## XIII.2 The per-cell discriminator — and its exact reduction (the honest headline)
The ZCode `tensor-decomp` discriminator asks whether each `L*(T)` factors over `Q(ζ_{3n})` into two
`ζ₃`-twisted quadratics `(T²+AT+B)(T²+ζ₃AT+ζ₃²B)`. **Result: 1171/1171 cells PASS across 11 primes
`43≤p≤1303`, zero failures** (PATH A exact ≤127; PATH B modular reproduces and extends — M21), with twist
character **constant `ξ(Frob_p)=ζ₃`** (M22).

**But the discriminator is necessary-not-sufficient, and its evidential weight is exactly one scalar
identity.** The exact symbolic reduction (P16, `twist_identity_reduction_v1`) eliminates `A,B`; once the
census-forced `e₃=χ₂(−1)p·e₁` and `e₄=p²` are imposed, the two residuals collapse to `R₀≡0` (identically)
and `R₂=0 ⟺ e₂=e₁²−χ₂(−1)p`. Therefore:

> **The "tensor-decomposition discriminator PASS" is algebraically equivalent to the single scalar census
> identity `e₂=e₁²−χ₂(−1)p` holding in that cell.** The 1171/1171 is 1171 confirmations of one scalar
> law, not 1171 independent confirmations of a 4-dimensional module splitting.

This is a **sharpening, not a demotion** (the Anomaly-Drill rule: a dissolution into a sharper law is a
positive result). What is exact and real is the law `e₂=e₁²−χ₂(−1)p`, uniform across the tested family
(N8 asks *why*). What the discriminator does **not** establish is the module splitting itself — a
nontrivial extension class could be invisible at the eigenvalue level for every Frobenius tested. The
ZCode writeup `RESULT_tensor_decomp_discriminator_v1.md` reads the 1171/1171 as strong evidence "the
structure is real"; at the *per-cell* level that overreads. **Correct grade: the scalar identity is
`[VERIFIED — exact]` / `[PROVED — exact symbolic]` (P16); the tensor decomposition remains a
`[HYPOTHESIS]`, necessary-condition-satisfied.** (`ξ=ζ₃` is a real measurement of the twist *direction*
on top of the identity — the `[2,2]` canonical arm 1560/1560 — not itself forced by `R₀=R₂=0`.)

## XIII.3 The global algebraic-number layer — genuinely independent, and exact
Separately, at the `Q`-Galois / global level (`RESULT_algebraic_number_layer_v1.md`, M23), the eigenvalue
splitting field carries structure the per-cell identity does not touch:
- `Q`-minpoly of `N_{Q(ζ_n)/Q}(L_a)` — degree **`4(n−1)/3`, multiplicity 3** (`p=43,67,127`): the `μ₃`
  signature at the field level (three equal `Q`-Galois orbits).
- Tower `Q⊂Q(ω)⊂L`, `[L:Q]=40` at `p=43`, `Q(ω)` the unique quadratic subfield; deg-20 factors
  `ω↔ω²`-conjugate and **even in `T`** (the forced involution `α↦−ᾱ`, at the field level).
- `G⊆A₄₀` (square discriminant), generic cycle type `(10,10,10,10)`, all cycle lengths `∣10`; `L/Q(ω)`
  **non-abelian** ⇒ commutative-CM ruled out at the field level.

This is field/Galois data — a different observable class from the archimedean `|α|,arg α`, and
**untouched by the ideals-argument circularity** (`120°⇒(α₁)=(α₂)` as ideals is tautological; this is not).
It is exact, not statistical or archimedean.

## XIII.4 How the two levels connect — and what they jointly establish
The per-cell identity (XIII.2) and the global tower (XIII.3) are **logically independent**: a world where
the tensor decomposition is false could in principle satisfy the per-cell scalar identity without the
global tower, or vice versa. That **both** hold is real evidence the structure is not a one-methodology
artifact — the joint constraint is what the tensor / `SL₂`-monodromy candidate predicts (`Q(ω)` as the
`R=1⊕ξ` layer; the degree-20 non-abelian `L/Q(ω)` as the `W`-piece). It does **not prove** the candidate.
Commutative-CM alternatives are refuted at every level examined (non-abelian Galois group, non-abelian
eigenvalue field `anew_eigenvalue_verify_v4`, square-discriminant, four-block cycle type).

## XIII.5 Open targets (N8–N10, §XI.16–17)
1. **Why `e₂=e₁²−χ₂(−1)p`?** (N8) — the one scalar law the discriminator actually poses.
2. **The explicit `W`** (N9) — with `ξ=ζ₃` pinned, identify `W` as an abelian subvariety / motive.
3. **`L/Q(ω)`** (N10) — is the degree-20 non-abelian extension generated by the predicted `SL₂`
   monodromy? Exact group unpinned (degree 40 beyond PARI/KASH). `+` a `χ₂(−1)=+1`-branch confirmation of
   the mult-3 law.

## XIII.6 Direction for proof
Katz's Kummer-sheaf literature — the mechanism by which a Kummer cover forces a tensor-product
decomposition of cohomology — is the source the `e₂` identity and the tower should reproduce
(`[CITED — TO VERIFY]`, Appendix C; run `citation-verifier` before any grade moves up on it). The Weil
bound on `W` (Satake `|α|=√p`) is consistent with the census but not directly verified. **This is a
structural/number-theoretic programme; it makes no ECDLP claim, and the scale banner (`p≤1303`) governs
every measured input above.**

---

# PART XIV — THE UNIVERSAL PHASE CHANNEL  *(new in v7; ZCode `secp256k1-structure` Threads #2/#5/#6, 2026-07-25)*

*A refinement of Part V (the joint-aligned-leak phase). Scale banner: `p∈[5000,65000]`. A conditional
(not marginal), controls-validated structural law — and explicitly **not** a leakage channel.*

## XIV.1 The law
For any Weierstrass `E/F_p`, with `T(a₀,b)=Σ_{d=1}^{n−1} e_p(b·x_d) e_n(a₀d)`, `x_d=x([d]G)`:
`χ₂(−1)·sin(3·arg T(a₀,b) + φ_p) ≈ A(E,a₀,p)·χ₂(b)`, `b∈F_p^×`, `φ_p=0` (`p≡3 mod 4`) / `π/2` (`p≡1`).
The coupling is **exclusively at frequency `k=3`** (`A(k=1,5,7)` 10–100× weaker) — a clean spectral line.
`A∈[0.2,0.6]`: `j=0` ≈0.51, non-CM ≈0.43, `j=1728` ≈0.32. Verified 14/14 primes across `j=0`, `j=1728`,
and **non-CM** curves.

## XIV.2 The mechanism (NOT CM — corrects the earlier μ₃ story)
1. Real weights: `x_{−d}=x_d` ⇒ `T=2Σ_{d>0} e_p(bx_d)cos(2πa₀d/n)` has real coefficients ⇒
   `T(−b)=conj T(b)` ⇒ `arg T(−b)=−arg T(b)` (a `μ₂` parity).
2. Parity match: `sin(3 arg T)` is odd under `b→−b`, `χ₂(−b)=χ₂(−1)χ₂(b)` — sin fires when `χ₂(−1)=−1`,
   cos when `+1`.
3. `k=3` selection: the curve is degree-3 in `x`; `k=3` is the lowest mode where the real-weight parity
   and the cubic degree interfere coherently. **Not `μ₃`** — the earlier Thread #2 `μ₃`-invariance story
   was sufficient (for `j=0`) but not necessary; the channel appears on non-CM curves too.

**Decisive control:** replacing the real weights with complex `e^{2πia₀d²/n}` (breaks `T(−b)=conj T(b)`)
drops `A(k=3): 0.560→0.008`, `R²: 0.180→0.000`.

## XIV.3 What it is NOT (and the reinforced closures)
- **Not a leakage channel:** the structure lives in the free parameter `b`, not the key. Conditional MI
  of every contorted keyed readout (Eisenstein lift, sextic, formal-group, GLV, sextant/flap) given `d`
  is at the null (Threads #3–4; Appendix A). Part V/VI hold at the conditional-MI level across the
  contortion toolkit.
- **Not present for `y`-twists:** `U(a₀,b,c≠0)` has `R²=0.0000` — the channel exists iff the twist is
  `x`-only. Adding `y` (the Part V `xy` odd-half) destroys it, so the `xy` phase is at the random floor
  (consistent with the closure).
- **Not the naive Gauss-sum projection** (`corr(cos(2πa₀d/n), χ₂(x_d))=0.0006`).

## XIV.4 Status
`[EMPIRICAL — controls-validated]`, 14/14 primes, `p∈[5000,65000]`, `a₀=1`. Open (§XI.18): the amplitude
`A`'s curve-type-dependent secondary structure. The precise quantitative law (`k=3` exclusively,
`χ₂(−1)` phase, complex-weight control) does not appear in standard references (Ostafe–Shparlinski,
Kohel–Shparlinski, Kowalski bound *magnitudes*; Sato–Tate gives only marginal phase equidistribution) — a
candidate short writeup, but **not** an ECDLP lever.

---

# APPENDIX A — EMPIRICAL NULLS (scoped facts with firing controls — NOT completeness claims)

> **Critical caveat (verbatim, H3):** "every one of these used a *misaligned* readout, so each is a
> scoped fact about that readout at that scale, **provably consistent with a hidden aligned leak**."

Each bounds a *magnitude* about *that object at that scale with a control that fired* — at
`p=211→6397`. Single-key `(X,Y)→n,k,D` ~1e-5 bits (controls fire); bilinear-additive joint sum flat
`O(n)` (planted rank-1 fires); H² carry not coordinate-leaked (z=849); difference-set μ₃/cubic/xy
geometry at the AP-control floor (control fires 13–36×); no metastable soft mode (`|λ₂|~1/√n`);
finer-m difference scan at floor (z=1050); phase-hunt beyond μ₆ at floor (9 CM/Frobenius candidates —
the only *known computable* phase structure is the μ₆ group); GLV/CM ⊥ key-coordinate on the 82;
derr↔cap = a bit-length confound (dissolves at fixed bits, P=0.34–0.89). **`λ₂` transfer eigenvector
~50% μ₃-cov / `λ₃` up to 85% (real, broadband, no closed form — OPEN, not resolved).**

**Also scoped (carried verbatim from H3 — each a magnitude with a firing control, NOT a completeness
claim):** hybrid sum `χ_k`×additive ≈2√p; scalar-mult `ψ(d)`;
cubic-moment / S3 tensor; bilinear difference-set (powered to 1.4%); joint `(x,y)` *magnitude*
distribution (CM = non-CM); 3-point group law / collinearity; index-calculus relation yield
(β-invariant lever 1.5×, bounded) and S₄/S₅ decomposition (β-lever → 1.0); easy-target predictability
(no lever).

**Also scoped (new in v4):** the exposed-pubkey relations null — **the original run had NO firing
control and was uninformative**; redone with plant + random controls it is a scoped null (exposed
points relation-free at small coefficients, like random keys; large-coefficient relations are
DLP-hard, hence not excluded). *Lesson: audit OLD nulls for a firing control before trusting them.*

**Also scoped (new in v7 — ZCode `secp256k1-structure`, conditional-MI given `d`, `p∈[5000,65000]`):**
the "contorted readout" family (Eisenstein lift, sextic decomposition, formal-group parameter, GLV
split, sextant/flap) carries **no** residual bits beyond what `d` determines — conditional MI of each vs
`(n,k,d_err,D)` given `d` is at the null (Thread #4; controls fired: C1 planted, C2 generic,
replication). The two-point sum `U(a,b,c)` opens no channel for any `c≠0` (`R²=0.0000`, 200 samples) and
the cross-key pair sum `T_pair` is a clean null (Thread #5). Each **reinforces** the Part V/VI closures at
the conditional-MI level; each is a scoped magnitude with a firing control, **not** a completeness claim.
Methodological data point: Thread #5b's initial `+0.116` correlation was a **wrong-`λ`-root artifact**
(used `λ²`, which flips `y`) that vanished with the verified root — "structural parameters must be
verified before use" (cf. retraction #19, the β-probe; a re-occurrence of that failure mode).

*(Language: each is "at the matched floor for that readout/statistic/scale," never "nothing there"; a
hidden aligned leak, another basis, or `2²⁵⁶` is consistent with every one of them.)*

# APPENDIX B — HEURISTICS
`[HEURISTIC]` "genus-1 ⇒ no index-calc lever" (Diem 2011). `[HEURISTIC]` canonical-lift obstruction
(xedni) protecting the amicable transfer — what §XI.3 turns on. `[HEURISTIC+CITED]` isobaric ⇒
first-fall curve-independence (BFS).

# APPENDIX C — CITED INPUTS (verify before relying)
- **✅ Kohel–Shparlinski**, ANTS-IV 2000, LNCS 1838, 395–404. **VERIFIED 2026-07-17** against the
  source; `kohel_shparlinski_ants4_2000.pdf`, SHA-256
  `645d9022e029055271ae60387518b440075fad282886d8baa9df35f5b55d8d2a`. Thm 1
  `|S| ≤ Σmᵢdeg(𝔓ᵢ)q^{1/2}`; eq (3) `|S| ≤ 2deg(f)q^{1/2}`. `ω ∈ Hom(E(F_q),ℂ*)`, ψ **additive**.
  **Scope from the text: additive ψ only — NOT χ₂ (§XII.10).**
- **⚠ Lange–Shparlinski**, JMC 1 (2007) 1–11; SHA-256 `f29c524a9670…c6edec`. Lemma 2.4 bounds the
  UNTWISTED sum only. **NOT load-bearing; do not cite for the mixed sum (§XII.11).**
- **Tate's isogeny theorem** — carries `Hom(E,A_new)=0` from the disjoint Frobenius eigenvalues (P13).
- **Genus-`g` index calculus `Õ(q^{2−2/g})`** (`g` fixed, `q→∞`): **Gaudry–Thomé–Thériault–Diem 2007 +
  Nagao** (two-large-prime); carries to arbitrary/plane curves via **Diem** (ANTS 2006 — heuristic
  `Õ(q^{2−2/(d−2)})`, genus-3 quartic → `Õ(q)`). Verified from Enge survey arXiv:0712.3916 §2.6 + Diem
  primaries (`ANALYSIS_n4_cover_family_indexcalculus_v2.md`; §VII.3 Route 3; N4). **Cover/Weil-descent
  (GHS, Gaudry, Joux–Vitse) needs a proper subfield ⇒ no input over a prime field; quasi-subfield
  polynomials (HKPYY / Euler–Petit) give no prime-field speedup.** Statements about KNOWN algorithms,
  not lower bounds.
- Dirichlet class-number formula `h(−p) = D/(2−χ₂(2))` and first moment `Σa·χ₂(a) = −p·h` — classical,
  verified in code (§X.2).
- **Weil–Deligne / Grothendieck–Lefschetz / Ogg–Shafarevich** — P6a and, via the **Kummer** sheaf,
  P6b (the χ₂ rows KS does not cover). **Derived on disk: `weil_deligne_character_bound_v1.md` §6′,
  verification `weil_deligne_bound_verify_v1.py` + `.log`.** Reproving Weil–Deligne itself is what an
  unconditional Part VI would need — a `[GAP]`.
- Boneh–Shparlinski (LSB/MSB hardcore) — does **not** support the withdrawn `⟺` of Part VI-3.
- Xedni-calculus lift obstruction (Silverman 1998; JKSST 2000). MOV/Tate. BFS first-fall.
- **Tensor-decomposition discriminator + census identity** (ZCode `tensor-decomp`, 2026-08-09):
  `discriminator_tensor_decomp_v1.py` (PATH A exact / PATH B modular), `twist_identity_reduction_v1.py`
  (the exact symbolic reduction, P16), data `discriminator_tensor_decomp_v1{,_modular,_large_primes}.json`,
  writeups `RESULT_tensor_decomp_discriminator_v1.md`, `RESULT_twist_identity_reduction_v1.md`. Census-
  identity lineage in this folder: `RESULT_e2_identity_extended_verification_v1.md`,
  `verify_e2_identity_extended_v1.sage`, `xcheck_120deg_identity_vs_census_gcd_v1.py`,
  `CORRECTION_120deg_census_certification_direction_v1.md`.
- **Algebraic-number / splitting-field layer** — `RESULT_algebraic_number_layer_v1.md` (2026-07-31; on
  disk here since before v6 but **not carried by v4/v5/v6** — folded in at v7). Built on
  `anew_eigenvalue_verify_v4.sage` (non-abelianity), `powersum_ladder_routeA_v1.sage` (norm-and-factor).
- **Universal phase channel** (ZCode `secp256k1-structure` Threads #2/#5/#6) — `cm_generality_detector.py`,
  `channel_mechanism_verify.py`, `select_cm_curve_primes.sage`; arc writeup `notes/arc_writeup_v1.md`;
  pre-registrations `notes/PREREG_*.md`.
- `[CITED — TO VERIFY]` **Katz, Kummer / hypergeometric sheaves** (the mechanism by which a Kummer cover
  forces a tensor-product decomposition of cohomology — the source §XIII.6 should reproduce). Not yet
  checked against the exact claim; **run `citation-verifier` before any grade moves up on its strength.**

---
*Full detail: `cap_law_proofs_v1.md`, `masked_structure_findings_v1–v38.md`, `RESULT_*` files,
`PREREG_*` files, `glv_*` narratives, handovers in `archive_handovers/`. Degradation trace:
`DEGRADATION_AUDIT_H3_TO_MASTER_v1.md`. External-review adjudications: `GLM_AUDIT_RESPONSE_v1.md`,
`RESULT_external_review_idea_tests_v1.md`. Agent rationale: `AGENT_DESIGN_ANALYSIS_v1.md`.*
