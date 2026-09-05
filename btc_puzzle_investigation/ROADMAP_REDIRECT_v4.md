> # ⚠ CORRECTED 2026-09-04 — THIS FILE WAS WRITTEN WITHOUT CONSULTING `CLAIMS.md`
>
> **`CLAIMS.md` (compiled 2026-09-01, before this roadmap) is the project's single current-state
> ledger**, and says so in its own first line. It has a guard, `check_ledger.py`, which it instructs
> every session to run **at session start and before reporting any result**. I ran neither.
>
> 1. **§0's defect D-3 is WRONG.** It asserts "no master has ever consumed the brick programme" and
>    prescribes a `POSITIVE_FINDINGS_MASTER_v19`. `CLAIMS.md` already *is* that consolidation — and
>    its **rule 1** forbids exactly the versioned-copy pattern I prescribed ("Edit this file in place.
>    Never create `CLAIMS_v2.md`"), naming the v13–v18 delta chain as the failure it exists to end.
>    **The v19 prescription is withdrawn.** D-1 and D-2 stand; D-3 does not.
> 2. **§3.1 over-states N8** — see its correction box.
>
> Brick statuses below were transcribed from artifacts and are, as far as checked, accurate;
> `CLAIMS.md` is the authority wherever the two differ.

# secp256k1 — Working Roadmap (Bricks) — **v4, 2026-09-01**

> **Supersedes `ROADMAP_REDIRECT_v3.md` (2026-08-18 13:09).** v3 is the direct cause of a
> documented review failure and must not be read as a live task list again.
>
> **Why v3 went stale, precisely.** v3 was written at 13:09 on 2026-08-18 — the same morning its own
> bricks began discharging. Brick A discharged that day; Brick B's first sub-step discharged that
> day; the Brick B analytical step discharged that day; Brick B(ii) on 08-19/20; Brick C on 08-21.
> None of it was folded back. v3 therefore describes **every brick as work still to be done**, and a
> 2026-09-01 state-of-play review reproduced it verbatim as an open-avenue list: **five of six items
> were already executed.** Two further defects compounded it — see §0.
>
> > **Concurrency note.** Another account appended `Session 2026-09-01 (b) — E3 SPLITS` to
> `RESEARCH.md` *while this file was being written*, re-opening Brick A. It is folded in below. Two
> entries now both carry the label `2026-09-01 (b)` (the ρ-branch retraction and the E3 split);
> disambiguate by title, not by letter. **Anything in this file dated 2026-09-01 may be younger than
> a concurrent session's work — check `grep -n "^## " RESEARCH.md | tail` before relying on it.**
>
> **v4 is a status document, not a new plan.** Every brick below carries its outcome, its artifact
> and its grade. The live frontier is §3, and it is short.

---

## 0. The document-layer defect this version repairs

Three independent faults let a review of the corpus return a list of already-closed work. All three
are recorded here because the failure mode is structural, not clerical.

| # | defect | evidence | repair |
|---|---|---|---|
| **D-1** | `ROADMAP_REDIRECT_v3.md` frozen at the hour its bricks started discharging; the **only** document describing the brick programme, and it describes all of it as pending | v3 mtime 2026-08-18 13:09 vs `RESULT_e3_owed_measurement_v1` / `RESULT_n16_eps_object_identity_crosscheck_v1` / `RESULT_eis_carry_2d_dlp_reduction_v1`, all 2026-08-18 | **this file** |
| **D-2** | `RESEARCH.md` states "**Newest first**" but is newest-first only to ≈ line 370 (top entry `2026-08-16`); from line 377 it switches to **append-at-bottom**, running `2026-08-21(b) → 2026-09-01(b)`. A reader honouring the stated contract stops at 08-16. **And `2026-08-17…08-20` has no entry at all** — the exact window of the Brick A / Brick B discharges | `grep -n "^## " RESEARCH.md`; `grep -cE "^## .*2026-08-1[7890]" RESEARCH.md` → **0** | navigation banner + the four missing entries, appended 2026-09-01 |
| **D-3** | **No master has ever consumed the brick programme.** `POSITIVE_FINDINGS_MASTER_v18.md` (2026-08-27) contains **zero** occurrences of "Brick A/B/C/D/E" or of any brick artifact, and states "No grade is moved"; v17 mentions only `lmono_gkr`, twice. ~40 `RESULT_*` files from 08-18 → 09-01 have no consolidated home | grep over v17/v18 | **OWED: `POSITIVE_FINDINGS_MASTER_v19` (delta), `compile-diff` gate mandatory** |

**Standing rule proposed (from D-1).** A roadmap that names bricks must carry a *discharge line per
brick*, updated in the same session the brick discharges — or be superseded. A plan document whose
items have outcomes elsewhere is not merely incomplete; it actively misreports the frontier, because
a reviewer reads a plan as a to-do list. This is the `DEGRADATION_AUDIT_H3_TO_MASTER_v1` failure mode
(live frontiers 5 → 0 across one consolidation) in its inverse form: **closed frontiers reported as
live**.

---

## 1. Brick outcomes — B and C closed, D mostly closed (D3 still live), A re-opened today, E unverified

### Brick A — E3 cubic difference-set · **DISCHARGED 2026-08-18**
`RESULT_e3_owed_measurement_v1.md`, executing frozen `PREREG_e3_owed_measurement_v2.md` (arms A1–A4).
Set-specific cubic reject survives the generator-free structural null (`p=0.035`, 98.2nd pctile) but
is **family-wise non-significant**: `p_FWER=0.083` over `{E2,E3,E6}`, Bonferroni `0.248` over the
7-statistic session; `N=82` power ceiling.
**Grade `[EMPIRICAL @ secp — BOUNDED; not dissolved, not family-wise significant]`.**
*The MC-correction, the reproduction and the matched null the master owed were all run.*

> **⚠ RE-OPENED THE SAME DAY THIS FILE WAS WRITTEN — 2026-09-01 (b), another account.**
> `NOTE_e3_chirality_decomposition_v1.md` (RESEARCH.md `Session 2026-09-01 (b) — E3 SPLITS`).
> The exact integer identity `E3 = A3²−A3B3+B3²` splits **orthogonally** as
> `E3 = ¼·EVEN² + ¾·ODD²`, with `EVEN = 2a−b−c` fixed by `ω↔ω²` and `ODD = b−c` **negated** by it
> (chirality — the Galois swap of the two primes over 3 in `ℤ[ω]`). On the real 82 keys the
> field-difference reject is **89.3% ODD**; against the *frozen* null (seed 20260818, bit-identical)
> `ODD` sits at the **99.3rd pctile, p=0.007** (real 125 vs null median 32) — **sharper than E3
> itself**, which pooled it with a null `EVEN` term. Two documents that bounded E3 measured the other
> 10.7%: `RESULT_spectral_decomp_v1.md` states a **false identity** (`E₃ = ¼|1ᵀC1|²`; its own
> `spectral_decomp_meta_v1.json` gives `|1ᵀC1| = 75`, so that term is 1406.25, not 13125), and the
> group-law null is 90.2% `EVEN` — near-orthogonal to the channel the reject actually lives in.
> **⚠ POST-HOC and no grade has moved:** `ODD` was chosen after seeing the split; ×2 selection gives
> p≈0.014 and the honest FWER over `{E2,E3,E6}×{EVEN,ODD}` is not done. `experiment-designer` prereg
> + OOS are owed before the chirality statistic carries any grade. The algebra and the false-identity
> finding are **not** post-hoc.
> **Read Brick A as: the bounded result stands for the statistic it measured, and a sharper,
> near-orthogonal statistic on the same 82 keys is now live and ungraded.** This is precisely the
> "more resolution from the same 82 keys" route that `RESULT_e3_owed_measurement_v1.md` §4 named as
> the only way past the `N=82` ceiling.

### Brick B — the public-ε linchpin + CM-lattice unfolding · **RESOLVED, all four parts**
The single most load-bearing dependency of the programme. Every sub-question v3 posed has an answer.

1. **N16 `|u−v| ≤ ½ == build.eps` — DISCHARGED 2026-08-18.** `RESULT_n16_eps_object_identity_crosscheck_v1.md`:
   200,000/200,000 identical on all three comparisons plus both real puzzle keys, core fraction
   0.748925. Mechanism, not coincidence: `BP_SECP = A_SP − B_SP`, so the proof script and the
   canonical build generate the **same** GLV/Eisenstein lattice in **conjugate bases** — the `eps`
   core/flap partition is basis-choice-invariant. Re-verified first-hand 2026-08-21
   (`NOTE_v14_item9_n16_state_v1.md`). **`[VERIFIED — exact]`.**
2. **"Is `eis(X)` computable from public `(x,y)` in poly time?" — NO.**
   `RESULT_eis_carry_2d_dlp_reduction_v1.md`: `ε_LBE = f(a,b)` on the GLV halves (R1/R2/R3
   exact-verified), so computing it from `P` is the **2-D simultaneous DLP on `{G, φ(G)}`** —
   ECDLP-equivalent. Cheap from a candidate `d`, ECDLP-gated from the public point.
   **`[PROVED — reduction]`**, conditional on ECDLP-hardness (the project's standing residual).
   *This is a **placement**, not a closure: effort on per-point public readouts of the carry is
   effort on ECDLP itself.* Scope correction the same day (`REVIEW_eis_carry_framing_suppression_v1.md`):
   the equivalence is the **generic-`d`** statement; for range-restricted keys the gate sits at the
   *range* difficulty (kangaroo `≈2^{(k−1)/2}·√6`).
3. **CM-lattice unfolding `E(F_p) ≅ Z[ω]/(π_p−1)` — bounded null.**
   `RESULT_cm_lattice_unfolding_v1.md`: `I(Φ; (a,b) mod ℓ) < 9·10⁻⁴` bits for `ℓ∈{2,3,5,7}`, both
   mod-12 classes, `p≈1.3·10⁵`, `N≈2.2·10⁴` μ₆-transversal orbits; family-wise permutation
   `p=0.37 / 0.76`. Positive plant fires to `ε_min=1/32`; hard null 0/30. **`[EMPIRICAL — bounded
   null, powered, scoped]`.**
4. **The amicable second equation — REFUTED STRUCTURALLY, and this is the durable half.**
   `π_n − 1 = −π_p` (verified exact, 8 primes), so the "independent" partner ideal `(π_n−1)` **is**
   the primary ideal `(π_p)` up to a unit; `Ψ` is a deterministic function of `Φ`; conditional MI
   **exactly 0.00000** at every `ℓ`, every rung. **The second equation is the same equation.**
   `[VERIFIED-exact + STRUCTURAL]` — scale-independent, unlike the null in (3).

**Live continuation (not the original brick):** T2c, the public *range* route — the one channel that
does not pass through the reduction. Already advanced: `RESULT_t2c_range_carry_skew_exact_v1.md`
gives an **exact** range→carry skew law (`P₁₂₇=0`, `P₁₂₈=0.878`, `P₁₂₉=0.810`, oscillating to ½ by
`k≈145`), `[VERIFIED — exact integer counts]`; and `RESULT_t2c_carry_partition_kangaroo_bench_v1.md`
found **no interval-DLP advantage** from the carry composition. Honest applicability: **no exponent
movement at any live target** — exposed-pubkey targets sit in the equidistributed regime, and the
strong-skew `k` are address-only / hash-barred.

### Brick C — phase on the weight-1 eigenspace · **RUN 2026-08-21, three findings**
`RESULT_weight1_phase_ramp_v1.md`, executing frozen `PREREG_weight1_phase_ramp_v1.md`.
(a) **`[STRUCTURAL]` the literal Brick-C object has no public per-point realization** — the `A_new`
weight-1 eigenspace is a frequency-domain / cohomological object; (b) parity-restricted to `p≡3 mod 4`;
(c) a bounded null where it exists. *v3's framing — "read phase, not magnitude, escaping the forced-`l²`
no-go" — was correct as an escape and still landed on a structural wall one level down.*

### Brick D — exact identities that reach 2²⁵⁶ · **D1 PROVED (long before v3); D2 advanced 2026-09-01**
- **D1 — `(†) Σ_{s≤H} χ₂(s)·sgn(ρs mod p − s) = 3h(−p)`: PROVED 2026-07-24**,
  `RESULT_fld_dagger_proof_v1.md`, `[PROVED — pending independent adversarial review]`. **Not** via
  generalized Dedekind sums — source-first via Berndt–Evans / Goldstein–Razar and the classical
  `h = −(1/p)Σχ₂(a)a`. The change-of-variable lattice lemma is written
  (`PROOF_fld_changevar_lemma_v1.md`, 2026-08-08) and `|FLD| = 6h(−p)` is proved for all `p≡19 mod24`
  (`RESULT_fld_6h_theorem_assembly_v4.md`).
  > **Scope fact that must travel with this result:** `FLD = 0` at `p ≡ 7 mod 24` (**68/68**), and
  > `p_secp ≡ 7 mod 24`. The `|FLD| = 6h` theorem is therefore **vacuous at secp's own class.** Any
  > roadmap that lists D1 as a route to secp is mis-scoped.
- **D3 — citation-verifier / literature sweep. `[CARRIED FORWARD FROM v3 — still live]`**
  v3: *"10 claimed-original results unaudited (#★); reading the source dissolved an obstacle 4×;
  mandatory before any citation-strength grade move."* Partially advanced since: the L-mono citation
  gate was **discharged** 2026-08-24 (4 Katz/GKR theorems verified against primary sources; residual —
  ESDE 1.8.2 verified via the FKM reproduction, not the AM-124 original), and
  `RESULT_n31_purity_citation_resolved_v1.md` (2026-09-01) found the N31 citation **real but
  mis-stated** — the record quoted a *definition* as "théorème 3.2.3"; the actual hypothesis holds
  uniformly in `p`. The **sweep itself is not complete** and the standing rule is unchanged: mandatory
  before any citation-strength grade move.
- **D2 — CLOSED at `p ≡ 7 mod 12` (secp's class), 2026-09-01.**
  `RESULT_jacobi_sign_law_proved_secp_class_v1.md`: **`J(χ₃,χ₄) = −p` is PROVED** at secp's class.
  Rationality (`J = ±p`) by Hasse–Davenport — Frobenius `g(χ)=g(χ^p)` collapses the `m=2` product
  relation to `g(χ₃χ₄)² = θ(2)g(χ̄₃χ₂)g(χ₂)`, the `s=2` lifting relation evaluates all three
  (`g(χ₂)=p`, `g(χ₃)=−g_p(χ₃')²`, `g(χ̄₃χ₂)=−g_p(χ̄₃'χ₂')²`), and an `F_p`-side identity makes the
  ratio square to 1. The **sign is then free and regime-independent**: `ζ₃ ≡ 1` mod a prime `λ` above
  3 gives `J ≡ Σ_{u≠0,1}χ₄(u) = −1 (mod λ)`, and `J = εp` with `ε=±1` forces `ε=−1` at `p≡1 mod 3`,
  `ε=+1` at `p≡2 mod 3`. **`[PROVED]`, provisional on `citation-verifier` (unavailable) for the two
  standard HD relations only** — both are numerically witnessed in-script.
  **Consequence, corrected 2026-09-02:** the **closed form of the character sum `S`** at
  `p ≡ 7 mod 12` is a **theorem** (`S = −2p` on cubic residues, `+p` otherwise), and it is
  **scale-immune** — the same argument covers `p = 2²⁵⁶`. The **m-law proper** (`m = b₂/p` naming
  `A_new`'s eigenvalues) follows **modulo one empirical bridge**: `m = Re(S)/p` is a
  **firing control** in `RESULT_mu4_eigenvalue_individual_v1.md` (155/155 OOS + 30/30), not a
  derivation. ~~New open item: prove `m = Re(S)/p`~~ — **DONE 2026-09-02**,
  `RESULT_mlaw_theorem_secp_class_v1.md`: Lefschetz point counting on `C : w⁴ = x³+B` gives
  `a_new(2) = −2Re(S)`, and `#C(F_p) = #E(F_p)` at `p≡3 mod4` gives `b₁ = 0` (the "μ₄ argument",
  now derived rather than assumed); Newton then forces `b₂ = Re(S)`.
  > ### ⇒ **The m-law H2 is a THEOREM at `p ≡ 7 mod 12`: `m = −2` if `B` is a cubic residue, `+1`
  > ### otherwise.** Previously `[EMPIRICAL, 26 OOS primes]`. The proof is an identity in `p` —
  > ### **scale-immune, so it holds at `p = 2²⁵⁶`.** H1 (`p ≡ 11 mod 12`) stays empirical: §1–§3
  > ### apply there, but the Jacobi sign `J = +p` is unproved in that regime. v4's Brick D framing
  ("D2 protects A/C/E") is now discharged at secp's class.
  `p ≡ 11 mod 12` remains `[EMPIRICAL — 31/31 exact]`: §2's sign argument covers it, but the
  rationality half provably does not extend (`χ₃` is not a norm-lift there). Not secp's class.
- *(superseded, kept for the trail)* **D2 — the gap REDUCED earlier the same day.**
  `RESULT_jacobi_rationality_reduction_v1.md`. `RESULT_jacobi_closed_form_m_law_v4.md` §2 graded
  `J(χ₃,χ₄) = ∓p` as `[EMPIRICAL 12/12] … NOT proved here`. Now:
  · **`g(χ) = g_p(θ)·S(χ)`** for `θ = χ|_{F_p^*}` nontrivial, `S(χ) = Σ_{Tr x=1} χ(x)` (length `p`)
    — `[PROVED — elementary]`. Because `χ₄` is subfield-trivial, `χ₃` and `χ₃χ₄` share `θ`, so the
    irrational prefactor **cancels identically**. That is the structural reason `J` can be rational.
  · **`g(χ₄) = (2|p)·p`** — `[PROVED — derived]`. **This discharges a v4-of-the-m-law drill-rule bar**:
    that file recorded the sign rule as "fitted to three primes … may not be named or used in a proof
    until it is [retested]". Derived here, witnessed exactly 31/31 primes.
  · Residual as of that file: **(C2) `S(χ₃χ₄) = −(2|p)(−3|p)·S(χ₃)`** — **now CLOSED, same day**,
    see below.
    With **(C3) `S(χ₃) = −χ₃'(2)·J_p(χ₂',χ₃')`** tying it to the classical Jacobi sum over `F_p`.
  · Empirical base **12 → 31** primes, and **all four** character pairs `(χ₃^a, χ₄^b)` agree — a
    conjugate-choice control the m-law file did not have.
  · `p ≡ 11 mod 12` is **not** covered: `θ` is trivial there, so the cancellation argument is
    unavailable. Not secp's class.

### Brick E — degree of the cover-scramble polynomial `c(d)` · **INSTRUMENTS BUILT; RUNGS UNVERIFIED**
Per-rung **admissibility condition discovered** (2026-08-27): the `d`-polynomial degree statistic
needs a CRT factor `q > |Q|`, which makes `p=163` (67 < 69) and `p=211` (37 < 99) **ill-posed** — the
prereg ladder's powered rungs are `43`, `547`, `1051`. Control-iv **PASSED 15/15 at `p=43`**. Rung 547
launched 2026-08-27.
> **OWED — job status unverified.** `brick_e_rung_547.log`, `brick_e_control_iv_163.log`,
> `brick_e_control_iv_211.log` and `anew_sorder_sweep_v2.log` all stop at **Aug 31 08:00** carrying
> only setup lines (`[rung] p=547 … [domain] |Q|=273`) and no results. Treat as **stalled or killed,
> not completed**; re-launch or declare dead before any Brick E claim.

---

## 2. Threads v3 did not name, closed since

Recorded so the next review does not re-open them: `RESULT_semaev_structure_firstfall_vs_m_v2`
(prime-field first-fall degree is a **forced support invariant** — no first-fall lever),
`RESULT_semaev_cm_solving_degree_v1` (P2c: μ₆/μ₃ CM gives **no** solving-degree lever),
`RESULT_h5_cofactor_restoration_v2` (H-5: the Semaev CM relation-yield lever is a **cofactor /
subgroup-confinement artifact**, fully reproduced at matched `p` and index — v1's "residual" was an
index mismatch), `RESULT_cm_jointset_semaev_r5_v1` and `RESULT_cm_jointset_higherorder_v1` (scoped
nulls), `RESULT_n15_joint_multireadout_*` (scoped null on constructed secp keys),
`RESULT_n31_purity_citation_resolved_v1` (the citation is real but was mis-stated — a *definition*
quoted as "théorème 3.2.3"; the actual hypothesis holds uniformly in `p`).

---

## 3. The live frontier — what is actually open

1. **L-mono — and the route changed on 2026-09-01, hours before the stale review.**
   `RESULT_rho_branch_convention_v1.md` **retracted** `ρ_p` (a lex sorting convention composed with
   `χ₂(−1)`; global constancy is *forced* by `e₄ = p²`, not measured) and, auditing brick 2 for the
   same defect, **sharpened** it: T2's entire finite shadow is equivalent to the single identity
   > **`V₂ = V₁² − 2·leg·p`**  (converse verified symbolically; **312/312** cells, `p=43,61,67,79,97`,
   > both `leg` arms, under a second — against brick 2's 7 cells by degree-240–792 factorisations).
   `V₁, V₂` are explicit twisted character sums over `E(F_p)`, `E(F_{p²})`, and the identity has
   **Hasse–Davenport / Frobenius-square shape**. If it is formal in `(h₁,h₂)`, **T2's finite shadow
   becomes a theorem outright — no GKR, no sheaf isomorphism.**
   > **Cite it as M21.** The identity is **not new** — it is `POSITIVE_FINDINGS_MASTER_v12` **M21**
   > (1171 μ₆-orbit cells, 11 primes `43≤p≤1303`), and the mechanism question is **N8**, open since
   > v12. The 2026-09-01 (b) `RESEARCH.md` entry calls it a "New high-priority open item"; the RESULT
   > it derives from corrects itself on that word, and so does this line.
   > **ADVANCE 2026-09-01, `NOTE_n8_pointwise_convolution_v1.md`:** the identity is **pointwise**, not
   > merely Fourier — `h₂ = h₁⋆h₁ − 2·leg·p·δ₀`, i.e. `h₂ − h₁⋆h₁` vanishes at **every** `d ≠ 0` and
   > the whole discrepancy sits at the identity element. Exact at 11 primes, both `leg` arms,
   > **including 4 with composite `n`** — so it is not a cell artefact. Reformulated: both sides sum
   > the *same* weight `w(Q) = χ₂(y_Q·y_{R−Q})`, one over `Fix(Frob)`, the other over `Fix(φ∘Frob)`
   > with `φ(Q) = R−Q` — a twist/torsor comparison, finite and elementary, no `ℓ`-adic input.
   > **SCOPED 2026-09-02, `NOTE_n8_branch_confinement_v1.md`:** the identity holds **only on the
   > `m = +1` branch**. `m = −2` ⟹ `7` a cubic residue ⟹ `x³+7` splits ⟹ `E[2] ⊆ E(F_p)` ⟹
   > **non-cyclic** — and the `h₁/h₂` framework is dlog-indexed, so it *cannot* index a non-cyclic
   > group. **M21's 1171 cells and every later test are all in one branch.** Group-indexed testing
   > reaches the other branch for the first time and the identity **FAILS** there (4 primes, wide
   > spread, not a constant). N8 is not dead — it is correctly scoped, and **any proof must invoke
   > `#E(F_p)` ODD** (`= E(F_p)[2] trivial` = `x³+7` irreducible mod `p`); one that does not is wrong.
   > *(Sharpened later the same day: "not full 2-torsion" is NOT enough — the entire `p ≡ 11 mod 12`
   > arm has one rational 2-torsion point and FAILS. Conversely the condition is not tied to
   > `p ≡ 7 mod 12`: `p = 61, 97` at `≡1 mod 12` with `n` odd satisfy it.)* secp has prime order, so
   > `n` is odd and secp is inside the identity's domain.
   > **REDUCED 2026-09-02, `NOTE_n8_twist_reduction_v1.md`.** Branch condition sharpened to
   > **`#E(F_p)` ODD** (so mult-by-2 is an automorphism and every `R` has a UNIQUE rational half
   > `A₀`). Translating by `A₀` turns both sides into `χ₂`-sums of ONE even function
   > `G_R(C) = y_{A₀+C}y_{A₀−C}` — over `E(F_p)` and over its **quadratic twist** `E'(F_p)`
   > respectively (verified exactly, all `R`, 6 primes). **`R = O` is now PROVED** elementarily
   > (`−(n−1)` vs `+(n′−1)`, difference exactly `2p`). Since `G_R` is even it descends to the
   > x-line, and **`R ≠ O` ⟺ `W(R) := Σ_x χ₂(g_R(x)(x³+B)) = 0`** — verified exactly, all `R`,
   > 5 primes. **All of N8 is now that one `±1` sum on `P¹(F_p)`.**
   > **REFINED 2026-09-02, `NOTE_n8_mu3_structure_v1.md`:** the "fixed-point-free involution" reading
   > is **REFUTED** (exhaustive Möbius search: none). `D(x) = (x³+B)·M(x)·(x−a)` is degree 7 and
   > squarefree, so `u²=D` is genus 3 and `W(R) = −s₁`. Measured: **`s₁ = 0` AND `s₂ = 0`**, all `R`,
   > 2 primes, 108 cases — which by Newton + the functional equation forces
   > **`L(t) = t⁶ + a₃t³ + p³`, a polynomial in `t³`: the signature of a μ₃ / CM-by-`Z[ω]` Jacobian**,
   > the same μ₃ the campaign already runs on. `W(R)=0` is then a corollary. The μ₃ is **exact and
   > visible** when `x_{A₀}=0` (`D(βx) = βD(x)`, and `√β ∈ F_p` since `p≡7 mod 12`). **Remaining step:
   > exhibit it for general `R`.**
   > ### ⚠ SUPERSEDED — corrected 2026-09-04
   > **N8 was not open in the sense this section treats it.** `CLAIMS.md` **P19** already grades the
   > identity **`[PROVED — uniform]`** (elementary Galois descent on `E[2]`, scale-free, reaches
   > secp), and **M21** is regraded `[VERIFIED] → [PROVED] via P19`. Separately,
   > **`NOTE_n8_pencil_reduction_v1.md` (2026-09-01, 21:57)** had already reduced N8 to one lemma with
   > a proof outline *and a falsifier that was run and passed*: `E[2]` descends to a Klein four-group
   > of Möbius involutions of `P¹ = E/±`; `n` odd ⟺ `x³+Ax+B` irreducible ⟺ Frobenius 3-cycles them;
   > `Jac(C) ~ E₁×E₂×E₃` cyclically permuted ⇒ **trace 0**.
   > **The μ₃/CM reading above is REFUTED** — the lemma holds on **non-`j=0`** curves with no μ₃
   > automorphism; the ζ₃ is **Galois, not CM**. The test separating the two is `k=3` (nonzero over
   > `F_{p³}`, divisible by 3); my work stopped at `k=1,2`, where both stories agree.
   > **This is now the cheapest live route in the programme, and it displaces "finish route A or
   > route B" as the next L-mono action.** The sheaf construction remains the hard core *for the
   > uniformity the prize needs*; it is no longer the only way to bank the finite shadow. Note also
   > that route B is **promoted by elimination**: half of `Gal(K/Q(ζ_n))` swaps the planes, so no
   > `Q(ζ_n)`-rational labeling of `W` vs `W⊗ψ` exists — the labeling can only live in the sheaf.
2. ~~**Brick D2 (C2)**~~ — **CLOSED 2026-09-01**, `RESULT_jacobi_sign_law_proved_secp_class_v1.md`.
   The Hasse–Davenport route worked. What remains under D2 is only the `p ≡ 11 mod 12` rationality
   half, which is **not secp's class** and is low priority. Owed: `citation-verifier` on the two HD
   relations.
3. **LBE v2 — genuinely written and genuinely never run.** `PREREG_localized_bit_extraction_v2.md`,
   "**Status: PRE-DATA. Written before any measurement.**" Arm A deficit-frequency fingerprinting,
   Arm B coherent `ℓ¹` phase accumulation. Needs the `experiment-designer` gate before any data.
   *Standing risk recorded in the prereg itself: this is the direction most vulnerable to
   symmetry-mismatched nulls, and the programme's two prior false fires (#6, #15) were both
   LBE-shaped.*
4. **E3 chirality (`ODD = b−c`) — new, 2026-09-01 (b), ungraded.** See Brick A. Owed before any
   grade: an `experiment-designer` prereg for `|b−c|`; honest FWER over `{E2,E3,E6}×{EVEN,ODD}`; OOS;
   re-running the CM contrast (secp 125 vs non-CM `E′` 70) on the component that actually carries the
   effect. Owed on the document layer: a correction header on `RESULT_spectral_decomp_v1.md` (it
   states a false identity) and a qualifier in master v14 Part V §2 (its group-law-null reading does
   not test the reject's channel). Full `N=20000` confirm was in flight at the time of writing.
5. **Brick E rungs** — §1, Brick E: re-launch or declare dead.

### Not open, contrary to the 2026-09-01 review
**"D2 affine readability, prereg written but never run — the most striking gap in the programme"**
(`RESEARCH.md` 2026-08-07). It is PRE-RUN but **gated out, not neglected**:
`RESULT_D2_lang_rationality_gate_v1.md` (2026-08-09) shows the registered Lang-torsor realization is
**Frobenius-trivial** — both `P^±` are `F_p`-rational, so `(F−1)([P⁺−P⁻]) = 0` exactly, at 7 primes,
every liftable point. Its arms have identically-zero input. *Reporting that as an affinity null would
be incorrect; it is an object-level obstruction.* A successor needs one of three maps **specified
before measurement** (p-adic Hensel lift into a named formal-group kernel; a point over an explicit
extension with specified Frobenius action; an explicit crystalline/Dieudonné map with a coordinate
back to a point-local observable). The 2026-08-07 note should be read as **superseded two days later**.

---

## 4. Carried forward verbatim from v3 — working method and guardrails

*The first draft of this file dropped v3 §0(I), §2 and §3 entirely. They are restored here; a status
successor may not silently shed its predecessor's framing or guardrails. Where an item's premise has
since changed, the change is marked inline — the original text is not edited away.*

**Counter-prior (v3 §0(I)).** secp is **assumed to carry exploitable structure**; the task is to find
it or to bound it. "Not found" is not "absent." A null is reported with power and scope, and the
burden stays on any claim of closure.

**Working method (v3 §2).**
- **One brick, one loop:** pre-register (if empirical) → build → matched-null test → OOS → grade →
  fold the artifact into the ledgers with power + scope. **No grade moves up without its named
  artifact in the same edit.**
- **Trust-but-verify** every subagent artifact against the diff.
- *Dependency order (v3): B's N16 cross-check → A → C → E; D in parallel.* **Spent** — that order ran
  to completion between 08-18 and 08-21. The live ordering is §3.

**Guardrails (v3 §3, stated positively).**
- **Not** "collapse the search space" framings.
- **Not** treating a **work-invariant** (P19), **forced-magnitude** (M14 `l²`), or already-**bounded**
  channel as a lever — a revisit must use a channel the existing proof does not cover (phase for M14;
  `c(d)`-degree for P19; direct-read for N17). *Note: Brick C used the sanctioned phase channel and
  still hit a structural wall — the exception was legitimately taken and is now spent.*
- **Not** resurrecting the island **keyspace-pruning** apparatus (N18, scoped-closed). v3 carved out
  one exception — *"only the CM-lattice / amicable second-equation question (Brick B) is reopened."*
  > **That exception is now CLOSED** (Brick B(ii): `π_n−1 = −π_p`, the second equation is the same
  > equation, `[VERIFIED-exact + STRUCTURAL]`). **The N18 apparatus therefore has no live exception
  > at all.** This is a tightening, not a loss — record it as such.
- **Not** reading any uncorrected `p`, tested-scale magnitude, or dim-2 extrapolation (N2) as reaching
  secp; **form-level** structural claims may, with their own proof obligation.
- **PRNG boundary (decided 2026-08-18): generator/seed OUT; number-theoretic structure of the key IN**
  (the interval readout and the CM-lattice unfolding are properties of the number). *v3 owed a
  `memory-drafter` persist of this to `feedback_no_prng_generation_side`; still owed — that agent is
  not loaded in this session either.*
- **Not** converting a scoped null into a closure — burden stays on the closure.

---

## 5. Gate status and self-audit

> ### `[PROVISIONAL — compile-diff unavailable]`
>
> Per CLAUDE.md §2a this file is a **provisional** promotion. The gate was **UNAVAILABLE, not failed**:
> attempted 2026-09-01, `Agent type 'compile-diff' not found` — the project agents
> (`compile-diff`, `experiment-designer`, `citation-verifier`, `memory-drafter`) are not loaded in
> this session's harness. All four §2a conditions are met: this tag sits in the grade slot; the
> self-audit is below; the gate is recorded as owed; **no grade is promoted by this file.**

**What this file does and does not do to grades.** v4 **moves no grade.** Every grade shown is
transcribed from its cited artifact. The two new grades in Brick D2 (`[PROVED — elementary]` for the
coset identity, `[PROVED — derived]` for `g(χ₄)`) were established in
`RESULT_jacobi_rationality_reduction_v1.md`, a RESULT file, not by this promotion.

**Self-audit — what I checked myself, and what remains uncovered.** Per §2a, a self-audit discharges
the **mechanical** layer only; the **frame** layer needs context isolation and this audit does not
supply it.

| layer | item | covered? |
|---|---|---|
| mechanical | every v3 section header, brick and bullet present in v4 or explicitly discharged | **yes** — and the first draft **failed** it: v3's **D3**, **§0(I)**, **§2** and **§3** were all dropped, and are restored above. That is a real loss caught, not a formality |
| mechanical | v4's grade strings match the artifacts they cite | **yes**, spot-checked against each cited RESULT/NOTE/PROOF |
| mechanical | the §0 defect claims D-1/D-2/D-3 | **yes** — file mtimes, `grep -n "^## " RESEARCH.md`, `grep -cE "^## .*2026-08-1[7890]"` → 0, and greps of v17/v18 for "Brick" and the artifact filenames |
| **frame** | **is the §3 live frontier the *right* frontier**, or does it inherit this session's framing? | **NO — uncovered.** Nothing here rules out that a genuinely live thread sits outside §3 because I did not think to look for it |
| **frame** | **adequacy of the "closed" verdicts** — whether an artifact's scope really covers the question v3 asked | **NO — uncovered.** Brick C is the sharpest risk: v3 asked for a *phase* measurement and the artifact returns a *structural* no-go; whether that answers v3's question or sidesteps it is a frame judgement |
| **frame** | whether §2's "closed since" list deflates any of those threads | **NO — uncovered** |

**Owed (§2a ledger).** `compile-diff` — attempted 2026-09-01, unavailable (agent not loaded) — on
this file and on the `POSITIVE_FINDINGS_MASTER_v19` that §0 D-3 requires. `experiment-designer` —
required before the E3 chirality statistic (§3.4) or LBE v2 (§3.3) collects any data; also not loaded.
`memory-drafter` — the PRNG-boundary persist v3 owed. Until `compile-diff` clears, **no grade may be
promoted on the strength of this file**, and the frame rows above are open, not clean.

---

## 6. Standing scope

Unchanged from v3 and restated because status documents are where scope is lost: no item is scored on
opening the gate; a brick **stands or it does not**, and a null with power and scope is a brick. ECDLP
is assumed-not-proven and is the residual object of study — showing a route ECDLP-equivalent is a
**placement**, neither a closure nor a lever. Every empirical number here is scoped to its model
primes; `p = 2²⁵⁶` is ~236 binary orders from the powered rungs. **No leakage, keyspace or
extractability claim is made or reachable from anything in this file.**
