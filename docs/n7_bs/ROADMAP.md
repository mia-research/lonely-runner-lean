# n = 7 LRC — Barajas–Serra 2008 formalization ROADMAP

> ## ✅ COMPLETE — 2026-09-07
> 
> ```
> #print axioms intLRC_seven
> 'intLRC_seven' depends on axioms: [propext, Classical.choice, Quot.sound]
> ```
> 
> Zero `sorry` in the n=7 tree. No `native_decide`, `unsafe` or `admit`.
> `lake build LonelyRunner.LRC.SmallN.IntLRC_7` — 3368 jobs, exit 0.
> `intLRC_three` / `_five` / `_six` re-checked, no regression.
> 
> **Done-check: `scripts/n7/gate.sh`.** Run it before trusting any change here.
> Plain `lake build` will NOT catch a regression: `LonelyRunner.lean` imports only
> `LonelyRunner.Basic`, so the default target never enters `LRC/` and reports
> success without compiling this tree at all. Confirmed twice, independently.
> 
> ### What closed, and where the work actually was
> 
> | item | outcome |
> |---|---|
> | `case_65` (§6.5) | closed; nine branches. One sub-case uses an argument NOT from the paper — BS L727–732 is arithmetically unusable (see below) |
> | `case_66` (§6.6) | closed; needs no `7d₅` doubling-pin fallback |
> | `case_61` (§6.1) | closed; all three `ν(E)≠{m}` branches share ONE anchor lemma |
> | `five_avoid_m1` (§7) | **deleted, not proved** — the statement is false |
> 
> ### §7 (`m = 1`) — handled a level up, jointly with `d₆`
> 
> `five_avoid_m1` was false: three exceptional 5-sets over `ZMod 49` admit no unit
> multiplier, and `d₆` cannot help at `N = 49` (a level-1 element is already free
> there by `band_top`, so it only ever adds a constraint). BS resolve them at
> `N' = 98`, which is not a power of 7.
> 
> So the case moved into the §4 reduction, where all six elements are in scope.
> `bs_discrete_q` now returns a **general modulus `7·P`** rather than `∃ m` with
> `7^(m+1)`; `circDist_ge_of_band` generalizes `circDist_ge_of_residue` (whose
> proof never used that `N/7` is a power of 7). The `|S| = 5` branch splits:
> `m ≥ 2` → `five_band` (§6); `m = 1` → `five_band_m1` (§7), which may return
> `P = 14`.
> 
> Both of BS's §7 computer searches — asserted in the paper without the
> computation — are now carried out **in the Lean kernel**, no `native_decide`:
> 
> | theorem | content |
> |---|---|
> | `stage1_bad_count` | 20349 five-subsets, exactly 63 exceptional at `N = 49` |
> | `stage1_bad_are_dilates` | those 63 are exactly the dilates of BS's three sets |
> | `bad_subset_exc63` | the 63 pinned as literals |
> | `stage2_all_clean` | 23802 `gcd = 1` configs at `N' = 98`, all solvable |
> | `subs4_all_solvable` | every ≤4-subset solvable at `N = 49` |
> 
> Three stack obstacles were solved without touching `lakefile.toml`: one heavy
> `rfl` per module; the 63 sets pinned as literals so `bad`'s search is not nested
> inside another reduction; and `bad2Of` shown to distribute over append so the
> search chunks into four groups.
> 
> ### Findings about the source
> 
> **Confirmed defects.**
> - §6.6(a): BS print `q(λk·A₂) = (ẽ₂₄ − 2k, …)`, which does not reproduce their
>   own bad-pair list (16). Only `(2k − ẽ₂₄, …)` does — also the sign consistent
>   with `ẽ(d,d') = 2q(d) − q(d')` used throughout. `avoid_66a` uses the corrected
>   sign.
> - §6.5, L727–732: unusable, not merely misprinted. It reads "unless
>   `e₄₅ = 5N/2`" and `N = 7^(m+1)` is odd, so `N/2` is not a lattice point. The
>   natural repair to `5N/7` fails too: the same paragraph asserts `ℓ(2·A₄) = 1`,
>   needing `q(2e₄₅) ∈ {0,6}`, i.e. `e₄₅ ∈ {0, 3N/7}`; under `5N/7` one gets
>   `q(2e₄₅) = 3`. The paragraph is consistent only with the impossible reading.
>   **That branch is closed by an argument not in the paper** (doubled frame; the
>   obstruction set acquires empty self-overlap so Lemma 7(ii) applies) and is
>   flagged as such in the Lean.
> 
> **Two claims of ours that were RETRACTED — the paper was right both times.**
> - A claimed gap in §6.6(b) was our own invariant taken against the wrong
>   ratio-2 partner: `r(d₅) = 4 = 2·r(d₄)`, so `d₅` pairs with `d₄`, not `d₂`.
>   With `ẽ(d₄,d₅)` the bad set is `{2,4}`, `ℓ = 3 ≤ 4`, and Lemma 7(i) applies.
> - A claimed relaxation of `q(e₁₃) ∈ {0,5,6}` to include `1` dropped the carry in
>   the A₄ arc difference; `1` gives `ℓ(A₄) = 4`.
> 
> Anything below this box is the pre-completion working record, kept for
> provenance. Treat the box as current.

---

**Live status board for the n = 7 project.** Update the Status column as files
land. Ground truth for "done" is always `#print axioms` + build warnings, never
this table.

## What we are verifying

- **Conjecture target:** `intLRC 7` (6 moving runners + observer, gap `1/7`).
- **Source:** Barajas & Serra, *The Lonely Runner with Seven Runners*, EJC 15
  (2008) R48. On disk: `sources_barajas_serra_2008.txt` (830 lines, extracted).
  SHA-256 pinned in `docs/n7_bs/source_integrity.md`.
- **Method:** Prime Filtering with `p = 7` — a finite, number-theoretic,
  residue-chasing argument (7-adic valuation `ν`, position function `q`/`r`,
  multiplier sets `Λ_j`). **Structurally unrelated to the BHK 2001 geometry that
  closed n = 6** — the n = 6 BHK lemmas do not transfer.

## The single gap

`LonelyRunner/LonelyRunner/LRC/SmallN/IntLRC_7.lean` already wires the full
reduction. `intLRC_seven` splits into:
- **BSR** (`theorem61_BSR`, `V ≤ 6·v₁`) — done.
- **Large-SR** (`theorem71_LargeSR`, `6·v₅ < V`) — done.
- **Hard Case** `6·v₁ < V ≤ 6·v₅` — was the **single `sorry`**. Now discharged
  by `IntLRC7BS.barajas_serra_seven` (Barajas–Serra proves `intLRC 7`
  *unconditionally*; the hard-case bounds are not needed).

`H_seven` (the `m < 7` recursion) is complete and uses `intLRC_six`.

### Interface layers landed (2026-06-25) — all axiom-clean, build 2714

The single `sorry` has been pushed down two real, verified interface layers into
a purely arithmetic statement (`IntLRC_7_BS/Main.lean`, `IntLRC_7_BS/Defs.lean`):

1. **`bs_discrete_to_real`** (bridge, `Main`): integers `N>0, lam` with
   `circDist(lam·dᵢ/N) ≥ 1/7` ⟹ real witness `t = lam/N`. Removes all real
   analysis from remaining work.
2. **`circDist_ge_of_qval`** (q-correspondence, `Defs`): arc index
   `q(x) = ⌊(x mod N)/7^m⌋ ∉ {0,6}` ⟹ `circDist(x/N) ≥ 1/7` (`N = 7^(m+1)`).
   Lets the whole proof run in arc-index `q ∈ {1,…,5}` language.
3. **`bs_discrete`** (`Main`): packages 1+2 → `∃ N lam, circDist ≥ 1/7`.

**THE SINGLE REMAINING `sorry` = `IntLRC7BS.bs_discrete_q`** (`Main.lean:65`):
> `∃ (m : ℕ) (lam : ℤ), ∀ i, qval m (lam·dᵢ) ≠ 0 ∧ qval m (lam·dᵢ) ≠ 6`

i.e. Barajas–Serra eq (1): `q(λ·D) ∩ {0,6} = ∅`. In the paper `m = max ν₇(D)`.
This is the whole §2–§6 number-theoretic content. `Defs.lean` also has
`nu x = padicValNat 7 x` and `qval m x`.

## Module layout (`SmallN/IntLRC_7_BS/`)

Mirror of the `IntLRC_6_BHK_*` split. Files created with frozen-header stubs
during the `draft` step, then filled `prove → review → refactor → golf →
checkpoint`. Source line refs are into `sources_barajas_serra_2008.txt`.

| File | Content | Source lines | Status |
|---|---|---|---|
| `Defs.lean` | 7-adic apparatus: `ν`, `q`/`r`, `Λ_j`, `D₇(i)`, `A_s` residue classes, length `ℓ(X)`. Reuse `LRC/Defs.lean` (circDist, badSet, intLRC). | 40–128, 239–264 | **q-apparatus DONE (axiom-clean):** `qval`, `qz` (ZMod 7 arc idx), `qz_lambda` (**eq (3) engine**), `qz_eq_qval`, `band_of_qz_ne`, `circDist_ge_of_residue`/`_of_qval`. `nu` def'd. **NEW: `qz_add_carry` (carry lemma for §5)**. `r`/`Λ`/`D₇` level sets pending |
| `PrimeFiltering.lean` | **Lemma 2 (Prime Filtering)** + **Corollary 3** — the reduction engine, conceptual core. | 129–169 | **✅ DONE, ALL axiom-clean:** `single_level_avoid` (pigeonhole, ∑\|F\|≤6), `single_level_avoid_excl` (top level, ∑\|F\|≤5), **`prime_filtering` (Lemma 2, full general-`m` level induction)**, `band_top`, **`corollary3` (i₀=m form)** |
| `Reduction.lean` | §4 overview: `|D₇(i)| ≤ 3 ⟹ Cor 3`; hard branch dispatch. | 237–264 | **✅ SORRY-FREE.** Easy + j₀=0 (|S|=4 four_band, |S|=5 five_band) + j₀>0 all done; the two "5th-element" cases proven UNREACHABLE by cardinality. Only `five_avoid` remains (Case_A5). |
| `Case_A5.lean` | §6 `|A| = 5` master theorem + case analysis. | 507–830 | **`five_band` PROVEN modulo `five_avoid`** (normalize → band_of_qz_ne). `five_avoid` = the §6/§7 case analysis, **sole remaining sorry in n=7**. |
| `Section5c.lean` | §5 interior element handling (BS eq 8). | 269–273 | **✅ ALL AXIOM-CLEAN.** `interior_in_band`, `exists_pre_congr` (modular inverse + congruence). |
| `Lemmas.lean` | Supporting Lemmas 4–9 (multiplier existence / `ν`-coloring). | 364–505 | **Leaf layer DONE axiom-clean:** Lemma 5 (`lemma5*`), Lemma 6 (`lemma6_330/402/420/501/510`), Remark 8(ii) (`remark8_ii_core3`, `fitsInterval`). L4(ii) carry in Defs (`qz_2xsuby_carry`, `qz_subxy_carry`). **Lemmas 7, 9, Rmk8(i), L10–12 not started.** |
| `Case_A4.lean` | §5 `|A| = 4`: Case 1 `|A_s|=4` (L287), Case 2 `|A_s|=3` (L299), Case 3 `|A_s|=2` (L319). Finite mod-7 chase (eqns 7–12), candidates for `interval_cases`/`decide`/`omega`. | 267–363 | **ALL THREE §5 CASES PROVEN AXIOM-CLEAN.** |
| `Section5.lean` | §5 integer assembly: carry packaging, case assemblies, normalization. | 265–346 | **✅ ALL AXIOM-CLEAN, 0 sorry.** `case1/2/3_int_avoid`, `band_neg`, `normalize7`. |
| `Section5b.lean` | §5 dispatch: residue classification + `four_band` master theorem. | 265–346 | **✅ `four_band` PROVEN axiom-clean.** Fin 3 pigeonhole, (4,4) relabeling, sub-tuple dispatch. |
| `Case_A5.lean` | §6 `|A| = 5`: 6.1 `|A₁|=5` + Lemma 10 (L509); 6.2 `|A₁|=4` (L547); 6.3 `|A₁|=3,|A₂|=1,|A₄|=1` + Lemma 11 (L569); 6.4 `|A₁|=3,|A₂|=2` + Lemma 12 (L667); 6.5 `|A₁|=3,|A₄|=2` (L698); 6.6 `|A₁|=2` (L743). Likely splits further. | 507–830 | not started |
| `Main.lean` | Assemble into the Hard-Case lemma; rewrite the `sorry` in `IntLRC_7.lean`. | — | **bridge + `bs_discrete` + `barajas_serra_seven` done; wired into `IntLRC_7`. Holds the lone `sorry` `bs_discrete_q`** |

Keep each file ≤ ~300 lines; split greedily (n = 6 lesson — small files keep the
effective thinking budget high and lose less to compaction).

## Order of attack (source-first per file)

1. `Defs` + `PrimeFiltering` — nail `ν`/`q`/`Λ` against mathlib
   (`padicValNat`, `ZMod 7`) so finite residue arithmetic is `decide`-friendly.
2. `Reduction` — `|D₇(i)|≤3 ⟹ Cor 3`; pin to `|A| ∈ {4,5}`, `(A)₇ ⊂ {1,2,4}`.
3. `Lemmas` (4–9) as needed by the cases.
4. `Case_A4` — finite, explicit mod-7 chases.
5. `Case_A5` — the involved case (Lemmas 10–12, 6.1–6.6).
6. `Main` — assemble → rewrite `IntLRC_7.lean`'s `sorry` → confirm
   `#print axioms intLRC_seven` = `[propext, Classical.choice, Quot.sound]`.

## Hard branch — architecture (PDF re-read 2026-06-26, comprehension RESOLVED)

The lone `sorry` is `Reduction.bs_discrete_q` (hard branch). PDF
`barajas-serra-lonelyseven.pdf` pp.5–11 resolved the transcription:

- **§4 reduction** (p.6): `D' = {d/7^{i₀} : d ∈ D\D₇(0)}`, `N' = N/7^{i₀}`. Used
  ONLY for an **interior** big level (`i₁ = i₀`, `0 < i₁ < m`): there the config is
  `1/4/1` over levels `0/i₁/m`, so `D\D₇(0)` sits entirely at levels `≥ i₀` and
  `d/7^{i₀}` is integral. It maps to `|D'|=5, |D'₇(0)|=4` (= §5). Lift: any `λ'`
  solving `D'` lifts to `λ` with `(λ)_N = (λ')_{N'}`, good on levels `≥ i₀`; Cor 3
  finishes levels `< i₀`.
- **§5 (`|A|=4`)** = `|D₇(0)|=4`, `|D|=6`: `A=D₇(0)` (4) `+ d₅∈D₇(i₀)` (the one
  interior extra) `+` any `D₇(m)` elements, which are **preserved** (`|λd|_N≥N/7`,
  eq (8)) — so it covers the 6th element for free. Three subcases on `|A_s|`
  (most-popular mod-7 class) ∈ {4,3,2}, each a finite `q`-value chase via (9)/(10).
- **§6 (`|A|=5, m>1`)** = `|D₇(0)|=5`, `|D|=6` (1 extra at level `m`). LARGE:
  `e/ẽ` (13), Lemmas 4–9 (compression tools), then cases 6.1–6.6 (Lemmas 10–12).
  `|A|=5, m≤1` is a separate small case to locate.

**Case counts (`|D|=6, gcd=1`, hard = ∃ j<m |D₇(j)|≥4):** ≤1 big level (two ⟹ ≥8>6);
big level `i₁<m`; `i₁>0 ⟹ |D₇(i₁)|=4`, config `1/4/1`; `i₁=0 ⟹ |D₇(0)|∈{4,5}`.

**Current sorry chain (2026-07-02 updated) — 5 sorries, all in `Case_A5.lean`:**
`intLRC_seven` → `bs_discrete_q` (✅) → `five_band` (✅) → `five_avoid` → {
  `five_compress` (§6, m≥2) → `five_compress_repr` → **case sorries**
     `case_62b` (4,0,1): ✅ **ALL BRANCHES AXIOM-CLEAN**
     `case_64` (3,2,0): ✅ **AXIOM-CLEAN** (2026-07-02; fallback L693–696 closed via
        `fallback_64_choice` decide + Λ₁ doubling-carry pin; `lemma12_i`/`lemma12_ii`)
     `case_62a` (4,1,0): ✅ **AXIOM-CLEAN** (2026-07-02; 2-window/4-window/holed-window
        decides `avoid_62a_*`; branch (i)/h≠m ×2-antipode; (ii.2) h=m holed {0,1,2,4}
        + Lemma 7 `ẽ(d₁,d₅)∉{2,3}`, `qz(e)=3` carve-out via frame doubling)
     `case_61` (5,0,0): **OPEN** — `case_61_top` (ν(E)={m}) ✅ done; ν(E)≠{m} branch needs
        Lemma 10 on a 4-subset + 5th elt, `lemma9` compression, then `place_window5` /
        `dichotomy_core` endgame with the `3·`-remultiply (`rmk8_i_k3`) for `{p,q}={2,4}`.
     `case_63` (3,1,1): **OPEN** — endgame decides verified (ℓ≤2 free; ℓ=3 needs
        `ẽ34∉{2,3,4,5}` via Lemma 7 on (d₃,d₄), d₅ free). Blocker = composing Lemma 7
        ẽ-control with `lemma9_ii_j3` compression in the ratio-3 h<m branch (BS's
        ν(e₄₅)-vs-ν(e₁₃) dance); the ν(e34)=m fallback is a single-carry pin (verified).
     `case_65` (3,0,2): **OPEN** — (14)/(16) analysis, symmetric to 6.4.
     `case_66` (2,2,1): **OPEN** — self-contained; (a)/(b) q-tables, two-carry ẽ pin.
  `five_avoid_m1` (§7, m=1): **OPEN — statement needs redraft (d₆ + gcd=1)**
}
**Session 2026-07-02 (Fable 5):** closed `case_64` fallback + full `case_62a`. Build
green (2485 jobs). Endgame decides for `case_63` all verified numerically in
`experiments/` scratch; the remaining blocker is multiplier composition, not the
finite combinatorics.
**Lemma 12 (`Lemmas10_12.lean`, 2026-07-01):** `lemma12_i` (ℓ(A₁)≤3) and `lemma12_ii`
  (ℓ(A₁)=4 with ẽ∈{0,1,6}) both ✅ axiom-clean via `decide`. Used by case_64/65.
Compression toolkit (`Lemmas7_9.lean`): `lemma7_i`/`lemma7_ii`/`lemma9_i`/`lemma9_ii_j2`/`lemma9_ii_j3` ALL ✅ axiom-clean.
**ν=m edge RESOLVED** (`Lemmas.lean`, 2026-06-29): `lemma9_i_top` (exact 7^m shift via
  `qz_sub_mul_pow`, no carry) + `lemma9_i_dispatch` (unified dispatch: both<m / one=m /
  one>m all handled). `qz_eq_of_high_dvd` (Defs) for the q-equivalence trivialization.
  All ✅ axiom-clean. THIS WAS THE GATING BLOCKER — all §6 case ν(E)≠{m} branches now
  have the compression tool they need.
Labeling layer (`Lemmas10_12.lean`, NEW 2026-06-29): **`lemma11` (|A₁|=3) AND `lemma10`
  (|A₁|≥4) both ✅ axiom-clean** + helpers `exists_val7` (7-adic valuation extraction),
  `ultra_add` (ultrametric), `ratio_two_three`/`lemma10_select`/`cover_distinct` (finite
  decides), `res_eq`/`unit_res`. **Only L12 (|A₁|=3,|A₂|=2) still TODO in the labeling layer.**
Λ_m apparatus (`Lemmas10_12.lean`, 2026-06-29): **`qz_top_affine` + `qz_add_mul_pow`
  (engine) + `affine_place` (|A₁|=5 ν(E)={m} placement) all ✅ axiom-clean.** Composes
  with `qz_shift0`. (qz_* primitives to relocate to Defs.lean; file to split — debt.)
Case 6.1 progress (`Lemmas10_12.lean`, 2026-06-29): **`case_61_top` (ν(E)={m} branch)
  ✅ axiom-clean.** For ν(E)≠{m}: **`place_window5`** (residue-agnostic final placement),
  **`dichotomy_core`** ({0,6,p,q} fits ℓ≤5 unless {p,q}={2,4}), and **`rmk8_i_k3`
  (multiplicative Remark 8(i): ℓ(X)≤2 ⇒ ℓ(3X)≤4) ✅ axiom-clean** (via `qz_mem06_iff`
  bridge + `cluster3` + `rmk8_concl`) — the {2,4} 3·-sub-case engine. Remaining for
  the ν≠{m} close: **`lemma9_i` ν=m edge** (subtle exact-residue compression, SECTION6
  TODO — the gating blocker), the **Fin-5 labeling**, and the multi-multiplier
  composition. (Back-half dichotomy/3·/place ready; front-half compression gated on
  the ν=m edge. See `memory/lean_n7_bs_case61_wiring_2026_06_29.md`.)
Note: a stale `mul_ndvd` in `Case_A5.lean` used a non-existent `Int.prime_iff_natAbs_prime`;
fixed to `Nat.prime_iff_prime_int.mp (by decide)` (the tree-wide idiom) — Case_A5 now builds.

**§7 (m=1) architectural issue (2026-06-28):**
`five_avoid_m1` as stated is FALSE: three exceptional 5-element sets
`{1,4,11,39,43}`, `{1,4,18,22,29}`, `{1,4,18,44,46}` (ZMod 49, up to dilation)
have no unit multiplier. BS resolves them via the 6th element d₆ = 7k (the
level-1 element in the full 6-element speed set D) at N'=98: the remaining bad
(set, d₆) combinations all have `gcd(D) ≥ 2`, contradicting LRC's `gcd(D) = 1`.
**Required fix**: either (a) thread d₆ and gcd=1 into `five_avoid_m1`, or (b)
handle m=1 |A|=5 jointly at the `bs_discrete_q` dispatch level with all 6 elements.

**Next step — §6 (|A|=5, m≥2):**
`five_compress` needs Lemmas 10–12 (not yet in Lean) + Cases 6.1–6.6.
`lemma9_ii_j2` needs a two-target carry combinator in Defs.lean.
Dependency chain: Defs.lean (new combinator) → Lemmas7_9.lean → Lemmas.lean
(L10–12) → Case_A5.lean (`five_compress`).

Target interface:
```lean
theorem five_band (m : ℕ) (hm : 1 < m) (d : Fin 5 → ℤ)
    (hnotdvd : ∀ i, ¬ (7 : ℤ) ∣ d i) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      (7 ^ m : ℤ) ≤ (lam * d i) % 7 ^ (m + 1) ∧
      (lam * d i) % 7 ^ (m + 1) ≤ 6 * 7 ^ m
```
Plus `five_band_m1` for m=1 (§7 exhaustive search).

§6 source: lines 507–805 (~300 lines). Key building blocks:
- Lemma 5 (`ℓ(A₁)+ℓ(A₂)+ℓ(A₄) ≤ 5` → avoidance): Λ₀ pigeonhole
- Lemma 6 (stronger form with ẽ conditions): case analysis
- Lemma 7 (ẽ control via `ν(2d-d')` structure): key tool for subcases
- Lemma 9 (3-element compression via B=A₁): foundational
- Lemma 10 (|A₁|≥4 classification): coloring/numbering
- Lemma 11 (|A₁|=3 classification): coloring/numbering
- Lemma 12 (|A₁|=3, |A₂|=2 sufficient conditions): compression

## Verification bar (the `/goal`)

`cd LonelyRunner && lake build` exits 0 **and** `#print axioms intLRC_seven` =
`[propext, Classical.choice, Quot.sound]` with zero `sorry` — same bar that
certified n = 6. Per-lemma: confirm each open `sorry`'s *statement* matches the
source; adversarial fresh-subagent review before promoting draft → proved.

## Discipline (carried from n = 6)

- **Source-first.** Read Barajas–Serra's argument for the exact case (grep its
  Lemma/Case number in `sources_barajas_serra_2008.txt`) before any de-risk,
  sweep, or invention.
- **No editorializing.** State what the source says + what a build / script /
  `#print axioms` verified. No difficulty value-judgments.
- **"Proved" ≠ "closed."** A conditional lemma that drops required cases narrows,
  not closes. Audit via `#print axioms` on the TOP theorem, not grep.
- **Machine-generate** templated lemmas from verified param tuples (Python in
  `experiments/`) to kill transcription error.
