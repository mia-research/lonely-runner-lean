# n = 7 LRC — Barajas–Serra 2008 formalization ROADMAP

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
| `Reduction.lean` | §4 overview: `|D₇(i)| ≤ 3 ⟹ Cor 3`; hard branch dispatch. | 237–264 | **FULL DISPATCH WIRED.** Easy + j₀=0 + j₀>0 all done. **3 sorries** all = "5th level-0 element → §6". |
| `Section5c.lean` | §5 interior element handling (BS eq 8). | 269–273 | **✅ ALL AXIOM-CLEAN.** `interior_in_band`, `exists_pre_congr` (modular inverse + congruence). |
| `Lemmas.lean` | Supporting Lemmas 4–9 (multiplier existence / `ν`-coloring). | 364–505 | not started |
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

**Current sorry chain (2026-06-28):**
`intLRC_seven` → `bs_discrete_q` (Reduction) → 3 sub-sorries:
1. 5th level-0 element (`i ∈ S\T`): |D₇(0)|≥5 → §6 (Case_A5, not started) ×2
   (one each in the no-interior and interior branches of j₀=0)
2. ~~Interior element~~ **CLOSED.**
3. ~~j₀>0~~ **CLOSED** — §4 reduction: config 1/4/1, `four_band` at level
   m-j₀, `band_lift`, `single_level_avoid` + `qz_step` + `band_of_qz_ne` for
   level-0 element. One sub-sorry for 5th level-j₀ element (structurally
   unreachable in 1/4/1 config but needs §6 formally).

**What's proven:** The ENTIRE `bs_discrete_q` dispatch is wired except §6
(|A|=5, 5th level-0 element). Both j₀=0 and j₀>0 branches complete modulo §6.
When |D₇(0)|=4 (or |D₇(j₀)|=4 in the j₀>0 config): the proof is COMPLETE.

**Next step:**
1. §6 (Case_A5.lean, |A|=5): the big block (Lemmas 4–12, cases 6.1–6.6).

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
