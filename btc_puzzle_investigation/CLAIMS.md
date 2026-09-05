# CLAIMS — the single current-state ledger

**THIS IS THE ONLY DOCUMENT THAT IS CURRENT.** Everything else in this folder is either a *journal*
(`RESEARCH.md` — what happened, append-only) or a *snapshot* (`RESULT_*`, `PREREG_*`,
`POSITIVE_FINDINGS_MASTER_v*` — true when written, silently rots afterwards).

**Compiled:** 2026-09-01 · from `POSITIVE_FINDINGS_MASTER_v12` PART A (last full compile) + deltas
v13–v18 + ADDENDUM 1–4 + the 16 documents that postdated v18.
**Guard:** `python3 check_ledger.py` — fails when any `RESULT_/NOTE_/CORRECTION_/AUDIT_` doc is newer
than this file. Run it at session start and before reporting any result.

---

## The four rules

1. **Edit this file in place. Never create `CLAIMS_v2.md`.** Git carries the history. The v13–v18
   delta chain is exactly what happens when a state document gets versioned by copy: to know what was
   true you had to compile six documents, and a v12-era loss became — in v18's own words —
   *"structurally unseeable"* to every later delta.
2. **A session that establishes, moves, or retracts a claim edits this file in the same session.**
   Not the next one. The write-up is not the record; this is.
3. **This ledger indexes STATUS, not statements.** The full statement of every row lives in its named
   artifact and in the frozen `POSITIVE_FINDINGS_MASTER_v12.md` PART A. Never compress a row by deleting
   its artifact pointer — that is precisely the v12→v14 reorg loss.
4. **Grade changes need the user's agreement.** Proposed moves sit in `⟳ PROPOSED` until then.

---

## A.1 — Proved *(rigorous; scale-free unless noted)*

| # | claim (one line — full text in artifact) | grade | last touched |
|---|---|---|---|
| P1 | `p_secp ≡ 3 mod 4`, `≡ 1 mod 3`, `≡ 7 mod 12` | `[PROVED]` **reaches secp** | v12 |
| P2 | `p≡3 mod 4` ⇒ `Σ_P χ₂(y_P) = 0` exactly; converse false | `[PROVED]` **reaches secp** | v12 |
| P3 | `C: w⁴=x³+B` genus 3; `H¹(C)=H¹(E)⊕H¹_new`, dim 2+4 | `[PROVED]` | v12 |
| P4 | `ζ₄∈Aut(C)` ⇒ `Q(i) ⊆ End⁰(A_new)` | `[PROVED]` | v12 |
| P5 | `x³+B` only: `ζ₃∈Aut(C)` ⇒ `Q(ζ₁₂) ⊆ End⁰(A_new)` | `[PROVED]` | v12 |
| P6a | Additive character-sum bound (Weil–Deligne; also Kohel–Shparlinski) | `[PROVED\|WD]=[PROVED\|KS]` | v12 |
| P6b | Multiplicative χ₂ rows — **different theorem, Kummer sheaf. Do NOT attribute to KS** — confirmed 2026-09-01c against the KS primary source (their `Ψ=Hom(F_q,C*)` is **additive only**; Thm 1 single-pole gives `(1+deg f)q^{1/2}` = **4√q for `f=y`**, matching our WD constant exactly). **⚠ NOVELTY CAVEAT:** it is a routine change of conductor inside KS's *own* method — novel as a stated result, referee-exposed as an exercise | `[PROVED\|WD]` | 2026-09-01c |
| P7 | `E` is ORDINARY at secp | `[PROVED]` | v12 |
| P7′ | `ord_n(p)=(n−1)/6` (MOV embedding degree) | `[VERIFIED — 254-bit]` | v12 |
| P8 | **Claim S** — μ₆ selection rule on the curve | `[PROVED]`+`[VERIFIED]` **reaches secp** | v12 |
| P9 | **Claim F** — FIELD-level rule, strictly stronger (F1 6 sectors / F2 3 sectors) | `[PROVED]`+`[VERIFIED]` **reaches secp** | v12 |
| P10 | The missing `ℤ/2` is the sextic twist | `[PROVED]` **reaches secp** | v12 |
| P11 | **Cap Law** — flap geometrically forced; ¾:⅛:⅛ | `[PROVED — continuum]` | v12 |
| P12 | **CM spine law** — `eis(βX)=ζ·eis(X)+c`, ¾:⅛:⅛ | `[PROVED — continuum]`+`[VERIFIED]` | v12 |
| P13 | `Hom(E,A_new)=0` at secp — **⚠ INHERITS N2; never quote at secp without N2 attached** | `[PROVED]` *(conditional)* | v12 |
| P14 | Prime-order rigidity; `d` is the only chaining readout | `[PROVED]` | v12 |
| P15 | Reduction `Corr_F(a)=⟨F,χ_a⟩_d` | `[PROVED]` **reaches secp** | v12 |
| P16 | Twist-factorisation reduction ⇒ **discriminator PASS ⟺ `e₂=e₁²−χ₂(−1)p`** per cell; necessary-not-sufficient for `H¹≅W⊕W⊗ξ` | `[PROVED — exact symbolic]` | v12 |
| P17 | GLV-orbit carry-conservation; 18-class joint law; label ⊥ carry | `[PROVED — exact]` | v12 |
| P18 | slope² + un-normalised k=3×χ₂ channel | `[PROVED]` | v12 |
| P19 | **The `e₂` identity / 120° law is `[PROVED — uniform]`** by elementary Galois descent on `E[2]` — genuinely scale-free, **joins the carve-out list** | `[PROVED — uniform]` **reaches secp** | v18 R4 |
| P20 | **N31 purity**: `F^{I_x}=0` at all four punctures (odd `ord_x(y)`) ⇒ `H¹_c ≅ H¹(C,j_*F)`, pure by Weil II 3.2.3(3). Elementary, uniform in `p`. **+2026-09-01c:** that document's §5 "replace Weil II by Weil I" is **NOT new** — it is Kohel–Shparlinski's own method (Prop 1 conductor/degree + **Prop 2 = RH for function fields**), read verbatim from the ANTS-IV primary source; regraded there `[HYPOTHESIS]`→`[STANDARD — no novelty]` | `[PROVED]` ⟳ **PROPOSED** regrade from `[CITED — ×4 failed]` | 2026-09-01c |
| P21 | **Brick 2 converse**: the `[2,2]`-with-ρ-rescaling structure is *equivalent* to P16/M21's identity (not merely implied); `e₃²=e₄e₁²` is automatic and inert | `[PROVED — exact symbolic]` | 2026-09-01b |
| P22 | **No `Q(ζ_n)`-rational labelling of the two ζ₃-conjugate planes exists** — half of `Gal(Q(ζ₁₂ₙ)/Q(ζ_n))` swaps the factors (5/5 cells, p=43/61/79). Promotes route B by elimination | `[PROVED]` | 2026-09-01b |
| P23 | **Brick D2 CLOSED at `p ≡ 7 mod 12` (secp's class)**: `J(χ₃,χ₄) = −p` PROVED — rationality by Hasse–Davenport, sign by a mod-λ congruence (both regimes). Closed form of `S` is a theorem: `S = −2p` if `B` a cubic residue, `+p` otherwise. **Does NOT extend to `p ≡ 11 mod 12`** (rationality half provably fails) | `[PROVED — PROVISIONAL, citation-verifier unavailable]` | 2026-09-02 |

## A.2 — Measured *(the scale banner governs every row: none has power at 2²⁵⁶)*

| # | claim | status | last touched |
|---|---|---|---|
| M1–M20 | *(carried verbatim from v12 PART A — `A_new` ordinary ⟺ `p≡1 mod 4`; `gcd(L_E,L_new)=1`; the ½ saturation; `V(a)` reality; `FLD`=6h(−p); `⟨σ,χ₂⟩` law; joint-(x,y) readout + its forced non-separation; equipartition; D1 no affine structure; bit readouts; isotype readouts)* | unchanged | v12 |
| M21 | **`e₂=e₁²−χ₂(−1)p ⟺ V₂=V₁²−2χ₂(−1)p`** — 1171/1171 μ₆-orbit cells, 11 primes `43≤p≤1303`; exact integer convolution `f=h₂−h₁⋆h₁` at 9 primes. **See P19: now also `[PROVED — uniform]`** | `[VERIFIED]` → `[PROVED]` via P19 | v18 R4 |
| M22 | Twist character constant `ξ(Frob_p)=ζ₃`; canonical arm 1560/1560 | `[VERIFIED]` | v12 |
| M23 | Algebraic-number layer: minpoly degree `4(n−1)/3`, multiplicity 3; `L/Q(ω)` non-abelian | `[VERIFIED — exact]` | v12 |
| M24 | Universal phase channel, k=3 exclusive. **Null:** conditional MI of every contorted keyed readout given `d` is at the permutation null ⇒ **no keyed-readout channel above that floor over 14/14 primes, `p∈[5000,65000]`**; structure lives in the free parameter `b`. *(Was worded "NOT a leakage channel" — object-language on a test-bounded result; the artifact's scope column was dropped in the v12→ledger compression.)* `POSITIVE_FINDINGS_MASTER_v12.md` §XIV + `CONFIRMED_k3_phase_channel_weierstrass_v1.md` | `[EMPIRICAL]` | v12 · scope restored 2026-09-05 |
| M25 | Semaev CM relation-yield lever. **Null:** no j0-specific excess **> ±5% yield** (95% CI on mean diff `[−0.081,+0.053]`) at **MDE 0.095 log-units**, over **matched `p∈[523,823]`, indices k=2/4/6, |V|=6, m=3, K=25**. ⚠ v2's table covered **20 of 24** j0 primes and omitted the three **highest-lever** indices (n₂=14,16,24) — run 2026-09-05, tail mean −0.081, null holds. Arm C verdict **UNFORCED**: a planted lever of v1's size fires at z=+12.5 through the same matched control. `RESULT_h5_cofactor_restoration_v2.md` | **`[null — cofactor/sampling artifact, model scale]`** (was `[A−]`) · **⚠ OWED EXTERNAL REVIEW** (v18 §B: bias-direction conversion) · v2 correction: at matched p AND index, confinement fully reproduces j0's lever, **no residual** (v1's residual was a p-scale confound) | v15 H-5; v18 B; 2026-08-31 |
| M26 | x-closure effect **IS β/CM-specific**, mechanism = GLV relation-triples. **Scope:** `p∈{211,307,421,631,907,1093}` (≡1 mod 3, j=0), m=3, `|V|∈{9,12}`, S=18 instances/arm, K=30 generic; orbits at the permutation-null floor `perm_p=0.001`, both `|V|` arms. ⚠ **"scaling FLAT" conflicts with the artifact**, whose P-b row reads **6/6 primes non-flat/rising** — resolve which quantity each refers to before quoting either. `RESULT_h2_order3_cm_specific_v1.md` | `[VERIFIED]` upgraded | v15 H2 · flagged 2026-09-05 |
| M27 | GLV/cubic-character orbit readout exact on real puzzle keys #135/#140. **Null:** 0 operational reduction *on those two keys, at the tested readout class* — **no power figure and no artifact pointer found in the corpus** (the phrase occurs only here and in `ANALYSIS_intersection_leads_v1.md`). **⚠ OWED: locate the establishing artifact or restate with X/Y/Z.** Until then "0" is unconditional wording on `[VERIFIED]`. | `[VERIFIED]` | v12 · flagged 2026-09-05 |
| M28 | k=3 phase channel survives negation-parity-matched null | `[VERIFIED]` | v12 |
| M29 | μ₆-quotient relation multiplication — **constant-factor ≤6×, NOT an exponent change; known technique** | `[VERIFIED — scoped]` | v12 |
| M30 | Characters index μ₆ orbits — 9σ grading + scoped null on blocking | `[VERIFIED]`+scoped null | v12 |
| M31 | **D2 twist-rigidity certificate** exact, 8 primes, both mod-12 arms, every cell; non-abelianity COMPLETE at 9 generic primes, zero exceptions | `[VERIFIED — exact, decidable artifact]` | 2026-08-27 |
| M32 | **L-mono brick 2** — T2 at factor level exact 7/7 cells. **⚠ re-measures M21 at 1/167 the coverage and ~10⁵× the cost** (deg-240–792 factorisations vs exact convolution) | `[VERIFIED — exact, 7 cells]` | 2026-08-30 |
| M33 | **L-mono brick 1A** — Goursat moment table; only SU(2) matches; torus excluded at m₂, `N(T)` at m₄ | `[VERIFIED]` | 2026-08-31 |
| M34 | **A_new cyclic whenever `M=p²+p+1` squarefree**; automatic-√p witness `r=1+p`; S-visibility = embedding-sign question. **S-blindness RARE: 1 blind point (211's ℓ=13) in ~25 (p,ℓ); plain Legendre law FAILS; `ℓ≡7 mod 12` seen 6/6** | `[VERIFIED]` · **the `ℓ mod 12` law is DISSOLVED by M39/SB** | 2026-08-27 |
| M35 | **Semaev structure**: prime-field first-fall degree is a **FORCED support invariant** — no lever from group-law coefficients or `S_m` symmetry. **⚠ STALE CLAUSE (fixed 2026-09-01c): "symmetric reduction RAISES solving degree" was WITHDRAWN by `RESULT_semaev_symmetric_reduction_lastfall_v2`** — a censored Macaulay statistic; the blind exact `d_gb` re-measurement gives **LOWERS, 6→2** | `[VERIFIED-scope]` ×3 scoped component nulls · **⚠ 2026-09-02: the growth-rate reading ("d_ff tracks 2^{m−1} ⇒ the non-subexponential direction") is WITHDRAWN as an inference — see M40, d_ff is a closed-form combinatorial quantity** | 2026-09-02 |
| M36 | **Brick D2 at `p≡7 mod 12`**: "prove `J` rational" reduced to one explicit sign identity; barred `g(χ₄)` sign rule DERIVED | `[EMPIRICAL 12/12]`, reduction proved | 2026-09-01 |
| M37 | **E3 chirality split.** Exact: `E3 = ¼·EVEN² + ¾·ODD²`, `EVEN=2a−b−c=1ᵀC1` (fixed by `ω↔ω²`), `ODD=b−c` (**negated** by it). Real 82: **10.7% / 89.3%**. Vs the FROZEN null (seed 20260818 regenerated, N=20000): `EVEN` 63.90th pct `p=0.361`; **`ODD` 99.17th pct `p=0.0084`**, real 125 vs null median **32** — sharper than E3 itself (98.24th). ⇒ `RESULT_spectral_decomp_v1`'s stated identity `E3=¼\|1ᵀC1\|²` is **FALSE** (`=¼EVEN²=1406.25`, not 13125), so its "not coherent / bounded at the spectral level" verdict measured 10.7%; and the group-law arm is **90.2% EVEN**, so its null does **not** test the reject's channel. `NOTE_e3_chirality_decomposition_v1` | `[EMPIRICAL — ⚠ POST-HOC: `ODD` chosen after seeing the split; experiment-designer prereg + OOS owed before ANY grade]` | 2026-09-01c |
| M38 | **N8/M21 pointwise form** — `h₂ = h₁⋆h₁ − 2·leg·p·δ₀`: `f[d]=0` for every `d≠0`, `f[0]=−2·leg·p`. Exact integer, 11 primes, both leg arms, **4 with composite `n`** (111,147,133,219) — escapes M21's cell framework. `NOTE_n8_pointwise_convolution_v1` | `[VERIFIED — exact]` | 2026-09-01c |
| M39 | **S is a SCALAR.** `ζ₃:(x,w)↦(ωx,w)` fixes `w` and `lift` is written in `(x,w)` ⇒ `lift` is φ-equivariant ⇒ on cyclic `A_new(F_p)≅Z/M`, `S = λ·lift` with `λ = 1+b₂c+βc² mod M`. **`ℓ` blind ⟺ `ℓ\|λ`** — a ~`1/ℓ` arithmetic event, **not a character**. `RESULT_s_visibility_scalar_lambda_v1` | `[PROVED — derivation]` · predictor **8/8 primes** with `c` measured independently; φ-equivariance measured 5/5 | 2026-09-01c |
| M40 | **Scope: this harness only** — m=2 `|V|=2..8`, m=3 OOS `|V|=3..7`, 12/12 exact. `RESULT_semaev_dff_closed_form_v1.md`. **Semaev `d_ff` has a CLOSED FORM** in this harness: `d_ff = max(2^{m−1},\|V\|) + (m−1)·2^{m−1}` — the S-pair lcm of the dense box's unique top monomial with `x_i^{\|V\|}`. **Verified 12/12 exact** (m=2, \|V\|=2..8; m=3 OOS, \|V\|=3..7 incl. the non-obvious flat at \|V\|=3,4). **No arithmetic content** — explains the zero variance over 24 draws. m=4 ⇒ **32**, and v2 used `Dmax=30`, so "CENSORED >30" was guaranteed a priori; m=5 ⇒ 80 by hand. In the real regime `\|V\|≈p^{1/m}` it is **linear in the factor base**, so it can never be low ⇒ **cannot test the Petit–Quisquater assumption in either direction**. `RESULT_semaev_dff_closed_form_v1` | `[PROVED — derivation]` + `[VERIFIED — 12/12]` | 2026-09-02 |

## A.3 — Not established *(open — NOT closed)*

| # | item | why open | last touched |
|---|---|---|---|
| N1 | Mechanism for the **½ saturation** — the one measured anomaly with no account | unexplained; **controlling grade OPEN** (v13 found three conflicting grades for this one object) | v13 |
| N2 | Is `A_new` supersingular **at secp**? | dim-2 proof gap; **load-bearing for P13 and all of §VII** | v12 |
| N3 | No numerical discriminator for the CM layer (L3) | two designed tests failed | v12 |
| N4 | Cover transfer into `Jac(C)` | family bounded vs *known* index calculus; residuals R1 (prime-field Semaev) / R3 (sub-GTTD algorithm) open | v12 |
| N5 | Unbounded / growing-degree corner of the character-sum bounds | `[GAP]` — no reduction in hand | v12 |
| N6 | **Everything in A.2 is `p ≤ 2¹⁷`; none has power at `2²⁵⁶`** | the banner | v12 |
| N7 | *(artifact: `RESULT_subrayleigh_cubic_coherence_v1.md`; refutation arm `RESULT_n7_finite_rank_refuted_v1.md`, graded there `[EMPIRICAL — suggestive, n=6, min-statistic]`)* **Sub-Rayleigh deficit** — 0.06–0.10%, one-directional, Stouffer −71.8 (30 primes), survives the Hermitian matched null, **persistent over a 79× p-range**. Carried by the **low tail** (+130–166%) + high tail (+27–74%), offset by a mid excess; **~8% near-zero excess, stabilising**; `M4` structurally blind (`r⁴≈0` there); **every character**, and **no (b,c) locus** | **carrier STILL UNIDENTIFIED.** Note: `R²=0.563` is the fraction the smooth δ(p,n) surface *explains* (~44% residue), and after surface removal there is no residue at `a_p mod 3/4`. **+2026-09-02: free-phase FINITE-RANK REFUTED** (pre-registered; r=4 over-predicts the near-zero excess ~6×, +50% vs measured +6–8%; Rayleigh out-fits r=4 on the char bulk). Null **confirmed Rayleigh** (N7-A). `c=0` depletion **retired as probably finite-size** (min-ratio 1.7×→0.7× over p=349→2089) — narrowed, not discharged (min-statistic, n=6). **Untested:** a *constrained* one-angle/ω-orbit finite-rank model; imaginary-part isotype; higher-order phase invariants; co-occurrence arms | 2026-09-02 |
| N8 | **Why does `e₂=e₁²−χ₂(−1)p` hold?** **+2026-09-01d: REDUCED TO ONE LEMMA** (`NOTE_n8_pencil_reduction_v1.md`). The `p+1` `F_p`-rational degree-2 divisors with `sum(D)=R` are the fibres of `φ_R:E→P¹` from `\|(R)+(O)\|`; `χ₂(N(z))=χ₂^{(2)}(z)` makes the fibre-norm of `y` ONE function on the pencil. **LEMMA: `n` odd ⇒ `Sp(R) − I(R) = 1` for every `R≠O`** (split minus inert, `(O)+(R)` weight 0) — `[VERIFIED — exact, all R, 5 curves, j=0 AND non-j=0; even-n control fails at EVERY R]`. The remainder is closed-form and machine-checked: `Sp=(h₁+1)/2`; `h₁(O)=(n−1)χ`; **`I(O)=−χ(2p+1−n)/2`** (`Frob Q=−Q ⇒ χ₂^{(2)}(y_Q)=−χ` constant, set = quadratic twist, size `2p+2−n`); ⇒ `V₁²−V₂=(n−1)χ−2I(O)=2χp`. **`n` odd is used three independent times.** Also: `n` odd ⟺ `x³+Ax+B` IRREDUCIBLE ⟺ **Frobenius 3-cycles `E[2]∖{O}`** — the source of the ζ₃ on a curve with no μ₃ automorphism; **+same day: LEMMA MADE EXPLICIT.** Translating by the rational `Q₀=R/2` turns the pencil into the fibres of `x`, so **Lemma ⟺ `Σ_{c∈F_p} χ₂(f(c)) = 0` for the DEGREE-7 `f(c)=(c³+Ac+B)·∏_i(c−x(T_i+Q₀))·(c−x(Q₀))`** — `[VERIFIED — exact, every R, 6 curves j=0 and non-j=0]`. Mechanism reconstructed: `E[2]` descends to a **Klein four-group of Möbius involutions of `P¹=E/±`**, `σ_i(x)=(t_ix+2t_i²+A)/(x−t_i)`; `n` odd ⟹ Frobenius 3-cycles them ⟹ the three nontrivial `V`-characters are permuted cyclically ⟹ trace 0. Matches P19's route, re-derived from scratch and made laptop-checkable. **+PROOF OUTLINE:** `f` has branch locus `x(E[2]) ∪ x([2]⁻¹R)` (8 pts with ∞) ⇒ `C:y²=f` genus 3, `V`-stable, `C/V≅P¹`, three genus-1 quotients, `Jac(C)~E₁×E₂×E₃` **cyclically permuted by Frobenius ⇒ trace 0**. **Mechanism's own falsifier RUN and PASSED**: sum vanishes over `F_p` AND `F_{p²}` (Frob² still a 3-cycle) and is NONZERO over `F_{p³}` (Frob³ trivial) — 4 curves; and every `F_{p³}` value is **divisible by 3**, independently corroborating the three-block decomposition. Steps 3–4 (genus formula, Kani–Rosen) standard, not written out. **⚠ dead hand-step recorded:** `Jac(C_R)≅E` for the quartic is FALSE (`Σ_cχ₂(q_R)` varies with `R`)  **+2026-09-04 (duplication notice, no grade move):** a later session re-derived this row's content from scratch — the `n`-odd hypothesis, the `Q₀=R/2` translation, the degree-7 x-line reduction, the genus-3 framing, the `R=O` evaluation, and `s₁=s₂=0` (= the falsifier's `F_p`/`F_{p²}` columns) — in `NOTE_n8_{pointwise_convolution,branch_confinement,twist_reduction,mu3_structure}_v1.md`, having run neither `check_ledger.py` nor read this file. Those notes carry withdrawal/supersession headers. **⚠ One of them asserts the `t³`-structure comes from a μ₃ action / CM by `Z[ω]`. That is REFUTED by this row's own data** — the Lemma holds on **non-`j=0`** curves with no μ₃ automorphism; the ζ₃ is **Galois** (Frobenius 3-cycling `E[2]∖{O}`), not CM. The distinguishing test is `k=3`: CM-style reasoning stops at `k=1,2` where both stories agree, while the block story predicts **nonzero over `F_{p³}`, divisible by 3** — already run here. | 2026-09-01d |
| N9 | The explicit 2-dimensional piece `W` | not identified. **+P22:** it cannot be identified from `L*(a)` — must come from the sheaf side | 2026-09-01b |
| N10 | Degree-20 non-abelian `L/Q(ω)` — is it the predicted `SL₂` monodromy? | group unpinned (deg 40 beyond PARI/KASH) | v12 |
| N11 | Mechanism of the M25 yield lever | **largely superseded — M25 is now null (v15).** Symbolic anchor stays proved | v15 |
| N12 | Where the M25 power law bends | **moot while M25 is null** | v15 |
| N13 | μ₃-graded syzygy module — scoped NULL, not a wall | matched-quo Betti sweep + m=4/5 owed; **m=4 wall: `d_ff>30` after 114 min, m=5 unreachable by brute Macaulay** | 2026-08-31 |
| N14 | Partial-`d` info in the isotypic trace `ℓ(d)` | no mechanism; scale blocked | v12 |
| N15 | **Joint multi-readout restriction.** **Null:** no cheap `f(d)` predicts the joint 18-cell readout above the family-wise permutation floor — **detectable at 7.7e-3 bits against a ceiling H(T)=3.647 bits**, over **bands 32/64/128/256 at N=100,000 plus `b=16` full enumeration**, frozen 45-predictor family. The floor **rises** as readouts are added (2.585→3.65), so this is a bound, not a ceiling. Arm C verdict **UNFORCED** (planted joint-only signal reaches the floor at 0.92 bits while all per-readout MIs stay at 5e-5–9e-5). ⚠ **Two supporting sentences are FORCED**: the "max predictor = `d%7+d%12` in 5/5 bands" is fixed by alphabet size (same argmax on shuffled T, ρ(I,K)=0.993), and "far below the singleton floor 1.35e-3" cites the wrong table's floor (own floor 1.59e-4). ⚠ **4 prereg departures unrecorded in DEVIATIONS**: B=9999→2000; 8 bands→4; the mandated second joint plant absent; "full log archived" — no log exists tree-wide. `RESULT_n15_joint_readout_confinement_v1.md` | `[VERIFIED-scope — scoped null]` (was OPEN since v11) · **⚠ OWED EXTERNAL REVIEW** (v18 §B) · named untested channels remain | v17; v18 B |
| N16 | Does coordinate flap `eps(x)` equal scalar carry `ε_LBE`? | **FOLDED — both clauses discharged 2026-08-18** | v15 |
| N31 | Non-archimedean purity citation | **RESOLVED** → P20. `RESULT_nonarchimedean_purity_statement_v1.md` §2 **REFUTED exactly** (its "all slopes ½" is the supersingular condition, not purity) | 2026-09-01a |
| N39 | A-joint-HO, 6 channels | scoped null, model scale. **⚠ NO ARTIFACT IN THE CORPUS** — the identifier `N39` occurs only in this file and `POSITIVE_FINDINGS_MASTER_v17.md`; no establishing document, no script, no power figure, no channel list. **OWED: locate or retire.** | v17 · flagged 2026-09-05 |
| R1 | **Frontier 9 — FLD-sign intrinsic-ness.** `sign(FLD)=−χ₂(M)` 54/54 but reduces to no tested intrinsic invariant. **Its π↔π̄ chirality sub-probe is VOID — do not run it**; voiding a decisive check is not closing the question | `[OPEN]` · *twice lost, twice restored* | v18 A |
| R2 | **Frontier 6 — `C_T` coupling next step.** Refutation of the 2–3% split is empirical, not analytical. Next: `‖D_odd‖_F` at `n~10⁶–10⁷`, vary generator/prime | `[OPEN]` | v18 A |
| R3 | **"Also live" tail, 7 items** — σ₁,σ₂ boundedness; is `ε` an arithmetic object?; large-prime rank-10 μ₃ split; a `p mod 8` law for `⟨σ,χ₃⟩`/`⟨eps,χ₂⟩`; deriving H1 from Cap-Law geometry; unconditional Part VI (`[GAP]`); cross-project ff-zeta RH test-bench + LRC↔μ₆ shadow | `[OPEN]` | v18 A |
| SB | **S-blindness — NOT a character question (M39).** Expected blind under the `1/ℓ` model over the 17 tested `(p,ℓ)` pairs = **0.865**; observed **1**; `P(≥1 blind)=0.60`. The `ℓ≡7 mod 12` "6/6 seen" is really **14/14 with 0.76 expected blind** (`P≈0.47`) — post-hoc class-carving around one event. `(211,13)` is **FORCED by the sweep's arbitrary `β`**: `β=14`, `β²=196<211` so `b₂=β²` exactly, and `β−1=13\|M` ⇒ `β≡b₂≡1 mod 13` ⇒ `λ≡1+c+c²≡0` for either `c`. **Convention-driven, like ρ_p.** Scan: **3/139** primes `p≡7 mod 12` in `[13,4000)` are forced-blind, all `ℓ=13`, 211 among them | **⟳ PROPOSED: close as a `1/ℓ` coincidence.** **PR4 ✅ CONFIRMED** (β-swap at 211: both β give SEES[3,31,37]/BLIND[13] — identical, **no exchange ⇒ eigenplane model REFUTED**). PR1–PR3 open | 2026-09-02 |
| SB-owed | **CLOSED 2026-09-02.** `c` measured from the φ-action (`s_lambda_c_v1.sage`, `S` never used ⇒ non-circular): p=79 `c=2027/6241`, p=163 `c=26569`, `gcd(λ,ord)=1` at all — both `ℓ=7` over-predictions resolved, the true `c` is the other root. **`c³≡1 mod ord` at 5/5 points ⇒ `lift` is φ-equivariant, MEASURED** (the derivation's load-bearing step). Predictor now **8/8 primes** | `[CLOSED]` | 2026-09-02 |
| MB | **The m-law's empirical bridge — CLOSED 2026-09-04.** `m = Re(S)/p` was *not derived anywhere in the corpus*; it entered `RESULT_mu4_eigenvalue_individual_v1` as a **firing control** (155/155 OOS + 30/30). **Now PROVED** (`RESULT_mlaw_theorem_secp_class_v1.md`, `mlaw_lefschetz_bridge_v1.py`) by Lefschetz point counting on `C : w⁴=x³+B`: (i) `gcd(4,p−1)=2` at `p≡3 mod4` ⇒ `#C(F_p)=#E(F_p)` ⇒ `a_new(1)=0` ⇒ **`b₁=0`** — this *derives* the "μ₄ argument" the predecessor invoked without proof; (ii) `#{w:w⁴=u}=1+χ₂+χ₄+χ̄₄` (`u=0` included) ⇒ `a_new(2)=−2Re(S)`; (iii) Newton ⇒ `b₂=Re(S)`. Chained with **P23**: **the m-law H2 at `p≡7 mod 12` is a THEOREM and is scale-immune (an identity in `p`, valid at `2²⁵⁶`)**. H1 (`p≡11 mod12`) still `[EMPIRICAL]` — P23's rationality half does not extend there | `[OPEN]` → `[PROVED — PROVISIONAL, citation-verifier unavailable]` ⟳ **PROPOSED** | 2026-09-04 |
| E3 | **Measurement DISCHARGED 2026-08-18/19** (`RESULT_e3_owed_measurement_v1`): reject survives a generator-free structural null (98.24th pct, `p=0.0354`), set-specific (`q_MT=0.015`, band-matched MT median at 48.6th), instrument fires (FPR 0.022, power 0.878 @Δ=100), **CM-mediated** (non-CM `E′` same prime: 67.1st pct, fail-to-reject). Family-wise `p_FWER=0.083` at the **N=82 power ceiling — underpowered, NOT null**. **+2026-09-01c: the reject is 89.3% CHIRALITY (M37); both documents that bounded it measured the other 10.7%** | `[EMPIRICAL @ secp — bounded, set-specific, CM-mediated]` · **⚠ EFFECTIVELY RE-OPENED**: the reject is 89.3% chirality and *both* documents that bounded it measured the other 10.7% (`AUDIT_session_2026_09_01_honesty_flags_v1` F1: "their instinct that E3 was live was vindicated"). **Do not report E3 as closed.** | 2026-09-02 |
| A-2a | "0 operational reads wider than the layer" | **RESOLVED to OPEN** (suppression-direction fix) | v17 |
| BE | **Brick E degree statistic.** p=43 → D=14 (generic). **163/211 structurally INADMISSIBLE** (needs CRT factor `q>|Q|`; 67<69, 37<99). Powered rungs: 43, 547 (running), 1051 | `[IN FLIGHT]` | 2026-08-27 |

## Retracted / do-not-reclaim

Full retraction ledger: `POSITIVE_FINDINGS_MASTER_v12.md` (frozen in place, banner-stamped) PART XII (26 retractions, all
carried through v17 with zero re-claims — verified by `AUDIT_v12_to_v17_loss_and_deflation_review_v1`).

| # | retracted | date |
|---|---|---|
| ρ_p | **The "global branch invariant"** — forced by `e₄=p²` composed with `canon()`'s lex sort; the value is `χ₂(−1)`, i.e. `branch=1 ⟺ p≡3 mod 4`. OOS-confirmed at p=163. The named follow-up "connect ρ_p to the `Q(√p,ζ₃)` embedding sign" is **VOID** (P22). `RESULT_lmono_brick1_gkr_inputs_v1` §2 retracted; §1 (moment table = M33) stands | 2026-09-01b |
| — | "The L-MONO finite evidence is maximal / cannot get sharper" (`RESULT_lmono_brick1` §3) — false when written | 2026-09-01b |
| — | The centralizer conjecture's **fourth** explanatory item ("the S-visibility embedding-sign texture — same character"). `ρ_p=χ₂(−1)`; S-visibility fails the plain Legendre law and lives on `ℓ mod 12`. **Never the same character** | 2026-09-01b |

## Standing flags

- **⚠ GATES UNAVAILABLE (2026-09-01/02).** `compile-diff`, `citation-verifier`, `experiment-designer`
  and `memory-drafter` were all unavailable across these sessions. Per CLAUDE.md §2a a self-audit
  covers the *mechanical* layer only and buys nothing on the *frame* layer. P23's two Hasse–Davenport
  citations are unverified (not refuted). `AUDIT_session_2026_09_01_honesty_flags_v1` F4.
- **⚠ One-way suppression bias.** M25 and N15 — the two highest-stakes objects — both converted
  toward null, each correctly artifacted, each in the documented bias direction. Same-model gates do
  not catch this. **Owed an external/human review** (`/code-review ultra` — user-triggered only).
- **⚠ Concurrency.** Multiple sessions write this folder simultaneously (observed 2026-09-01:
  two documents landed 8 minutes apart from different sessions). Re-read this file before editing it.
- **⚠ WRONG INSTRUMENT — `anew_sorder_sweep`.** Cost superlinear: p=43 104s → 163 66m → 547 12h →
  823 23h → **1051 55h**; the v2 job (p=1303) has run **37h+ with a 0-byte log**. Weeks of compute for
  a **1-bit** question that M39 answers in O(1). **Recommend killing it**; test PR1–PR3 by the λ route.
  (Not killed — another session's job.)
- **✅ VERSION HISTORY RESTORED 2026-09-05** — commit `426d47b`, 4105 files / 62 MB, on branch
  `btc-ranked-menu-arc-2026-07-17`. This file is now tracked; rule 1's "git carries the history" is
  true for the first time and "edit in place" has an undo.
  **Two corrections to what this flag used to say.** (i) It claimed the *"largest untracked file is
  1.6 MB, so a full add is safe on size"* — **false**: the folder is 460 MB, the largest file is
  54 MB, and 15 files hold ~200 MB. Those 15 are regenerable caches and are now `.gitignore`d
  (`constructed_keys_*`, `_angcache_*`, `_decomp_cache_*`, `p*_feats.npz`); `git add -f` to include
  them. (ii) Two handoff entries recorded the cause as *"repo not a git checkout at this path"* —
  also false; it is a checkout, the files were never added.
  The concurrency caution stands and was checked before staging (no other session had written in the
  preceding 10 minutes): **a blanket `git add -A` can still snapshot another session's half-written
  work**, so check before the next one.
- **✅ OPEN-REPRO PACKAGE BUILT (2026-09-02):** **`~/Desktop/odd-order-frobenius-identity/`** (moved OUT of `Math Ex` 2026-09-02 — see below)
  — 1001 lines, self-contained, **zero dependency on this folder**. `common.py` + `identity.py`
  (the theorem, all `ψ≠1` at once via one integer-vector test) + `pencil.py` (the lemma) +
  `frobenius.py` (the falsifier: `F_p`/`F_p²` vanish, `F_p³` non-zero and divisible by 3) +
  `purity.py` (P20, citation-free). Stdlib only except `purity.py` (sympy). **No float anywhere.**
  Every script exits non-zero on a spec violation; even-`n` controls fail everywhere they should.
  All four pass. `CITATIONS.md` states the prior art (Winterhof's "elliptic curve Legendre
  sequences" verbatim, Chen–Li–Xiao/Chen 2008, KS Thm 1, Deligne 3.2.3 via Katz, Kani–Rosen) and
  what is claimed as new. **+`PROOF.md`**: proves the `E[2]` lift to the genus-3 curve **splits**
  (every lift is an involution, since the `σ_T`-fixed points avoid the branch locus ⇒ exponent 2 ⇒
  `(Z/2)³`), replaces Kani–Rosen with an **isotypic decomposition** (so **Kani–Rosen is NOT needed**),
  and reduces all that remains to **one finite local computation** at six points (§3.4: the
  Frobenius-stable complement `H` has `g(C/H)=0`).
  **git: standalone repo, `main`, one clean commit (10 files, 1001 lines).** It was moved out of
  `Math Ex` first: that tree is a git repo with only **52 tracked files against 2430 status lines**,
  on a stale branch, carrying other sessions' uncommitted work — nesting or committing a public
  artifact there was the wrong move. The `Math Ex` tree is untouched.
  **⚠ THREE of my own claims died on checking, all recorded in `PROOF.md` §5:** (i) `Jac(C_R) ≅ E`
  for the quartic — false, `Σ_cχ₂(q_R)` varies with `R`; (ii) **"3 | the `F_{p³}` sum is independent
  corroboration of the three-block structure" — FALSE, it is forced by `S₁=S₂=0` via `e₃=S₃/3`
  being an integer.** The correct and stronger statement: `S₁=S₂=0` ⟺ **`L(C/F_p,T)=1−(S₃/3)T³+p³T⁶`
  is a polynomial in `T³`**, which is the 3-cycle signature itself, not a proxy; (iii) the control
  below. **⚠ A control of my own design was WRONG and the repo caught it:** an `n` even arm in
  `frobenius.py` — at p=13,A=B=1 the sum vanishes anyway, because `q_R` presupposes a *unique
  rational half* `Q₀=R/2`, which needs `n` odd. Ill-posed, not falsified. Removed, documented in
  the module docstring. The even-`n` control is valid in `pencil.py`/`identity.py` and fails there
  at every cell.
- **⚠ Literature audit — NOVELTY GATE CLOSED for spine purposes (2026-09-02).** The object is
  **definitively published**. Winterhof, *Measures of Pseudorandomness III* (Fields Inst. 2010), verbatim:
  *"**Elliptic curve Legendre sequences.** `E: y²=x³+ax+b` over `F_p`, `p>3`; `P` a finite point on `E`;
  `f(x,y) ∈ F_p[x,y]` squarefree, `deg(f)=d≥1`; `e_n = (f(nP)/p)`"* — that is exactly our `V_y(a)` with
  `f=y`. Published bounds: **Chen 2008 — `W(E_N) ≤ d·p^{1/2} log p`, `C_k(E_N) ≤ d·k·p^{1/2} log p`**;
  construction paper Chen–Li–Xiao, SETA 2006, LNCS 4086, 285–294.
  **Consequence — the categories are different and this decides the spine.** That literature is
  *measure-theoretic pseudorandomness*: well-distribution / correlation measures over INTERVALS, with a
  Polya–Vinogradov `log p`. It never computes the L-polynomial's coefficients. **A bound `d√p log p`
  neither implies nor is implied by `e₂ = e₁²−χ₂(−1)p`.** So: **the BOUND side (P6b, 4√p, 2√p) has
  definite prior art and must be presented citing KS Thm 1 + Chen–Li–Xiao/Chen 2008 + Winterhof.
  The IDENTITY (M21/P19), the pencil Lemma (N8), and purity (P20) are a different kind of statement and
  remain unmatched by anything found.** Lead with the identity.
  **Named residual (narrow, non-blocking):** Chen–Li–Xiao's own complete-sum constant for `f=y` is still
  unread — paywalled; two free-PDF routes failed, one 404. It affects only how `cap.py` is framed, not the
  spine. **TASK 1 CLOSED 2026-09-02 as far as open sources allow.** ~12 routes tried; constant still unread.
  Exact request (any one): **Chen, Monatsh. Math. 154 (2008) 1–10**; Chen–Li–Xiao, LNCS 4086, 285–294;
  **Mérai, Publ. Math. Debrecen 80 (2012) 199–213**. **RISK NOW BOUNDED WITHOUT THE PAPER:** `|V_y(a)|`
  *saturates* `2√p` (measured max/√p → 2.00), so **any correct bound has constant ≥ 2**; Chen's is in
  `[2,∞)` and ours is exactly 2. The unread constant can tie ours, never beat it, and cannot touch the
  identity or the lemma. KS constants independently re-confirmed verbatim from a second source:
  `≤2·deg(f)·q^{1/2}` general, `≤(1+deg f)q^{1/2}` single-pole ⇒ **4√q for `f=y`**.
  Other items: Kosters–Yeo published the first-fall-degree doubt (char 2 / Weil descent) — bears on M35;
  cover attacks are an **extension-field** literature, secp is a prime field — bears on BE/N4.
  **Never searched:** elliptic Gauss sums, **Eisenstein case** (secp's own CM) — nearest classical relative
  to P11/P12/P17, cited nowhere in this folder.
- **⚠ The scale banner.** Only P1, P2, P8, P9, P10, P15, P19 and the Part I congruences reach secp.
  Everything else does not. P13 inherits N2. The cap `|V_y|≤2√p` now rests on P20.
