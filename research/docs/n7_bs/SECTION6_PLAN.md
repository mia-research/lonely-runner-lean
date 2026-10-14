# §6 (|A|=5) Formalization Plan — n=7 Barajas–Serra

**Goal:** discharge the 3 remaining `sorry`s in `Reduction.lean`, all of which
need a `five_band` theorem (5 coprime-to-7 elements → unit multiplier landing all
in band `[7^m, 6·7^m]`).

## Architecture (settled)

```lean
theorem five_band (m : ℕ) (hm : 2 ≤ m) (d : Fin 5 → ℤ)
    (hnotdvd : ∀ i, ¬ (7 : ℤ) ∣ d i) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      (7 ^ m : ℤ) ≤ (lam * d i) % 7 ^ (m + 1) ∧
      (lam * d i) % 7 ^ (m + 1) ≤ 6 * 7 ^ m
```
Plus `five_band_m1` (m=1, §7 exhaustive search — RISK: plain `decide`, no
`native_decide`).

**Composition into Reduction.lean:** the level-m element is handled by `band_top`
UNCONDITIONALLY (any unit λ: `q(λd) ∈ {1..6}` ⊂ band, incl. `q=6` ↦ `6·7^m`).
So the j₀=0 branch dispatches on `|S|` (level-0 count): `|S|=4` ⇒ `four_band`
(done), `|S|=5` ⇒ `five_band`. `|S| ≤ 5` since `D₇(m) ≠ ∅` when `m ≥ 1`.

## Core definitions (BS §2 + eq 13), in Defs.lean

- `q(x) = qz m x : ZMod 7` — DONE (top 7-ary digit).
- `r(x)` = residue class of least nonzero 7-ary coeff = `(x / 7^ν(x)) mod 7`.
  For level-0 elements (§6 main case) this is just `x mod 7`.
- For a pair with a residue relation (`r(y)=2r(x)` / `r(x)=2r(y)` / `r(y)=r(x)`):
  - `e(x,y)` = `2x−y` / `2y−x` / `x−y`
  - `ẽ(x,y)` = `2q(x)−q(y)` / `2q(y)−q(x)` / `q(x)−q(y)`  (in ZMod 7)
- `ℓ(X)` = length of shortest difference-1 AP in Z₇ containing `q(X)`.
  Abstracted in Lemma 5 work as `intervalAvoids a ℓ s k`; may keep abstract.

## Lemma dependency chain (BS L364–L506, then L507–L782, then L786–L805)

| Lemma | Content | Method | Status |
|---|---|---|---|
| L5 | `ℓ₁+ℓ₂+ℓ₄ ≤ 5` ⇒ avoid {0,6} (exc. (3,1,1)+ẽ) | decide | **DONE** (`lemma5`, `lemma5_avoids`, `_311`) |
| L4(ii) | `\|ẽ−q(e)\|≤1` carry bound | int-floor | **DONE** (`qz_2xsuby_carry`, `qz_subxy_carry` in Defs) |
| L4(i) | ẽ invariance under Λ_h (all 3 eq-13 cases) | qz_lambda | **DONE** — general `qz_lin_invariant`; named instances `lemma4_i` (2,-1), `lemma4_i_half` (-1,2), `lemma4_i_eq` (1,-1) all axiom-clean |
| fitsInterval API | ℓ≤L monotone in L | — | **DONE** (`fitsInterval_mono`) |
| Rmk8(ii) | `⊂{0,1,5,6}` ⇒ ℓ(X)≤3 | decide (3-elt) | **DONE** (`remark8_ii_core3`, `fitsInterval`) |
| Rmk8(i) k=1 | `q(X−X)⊂{0,6}` ⇒ ℓ(X)≤2 | decide (3-elt) | **DONE** (`remark8_i_core3`) |
| Rmk8(i) k≥2 | ℓ(kX)≤k+1 | int-level (q(kX) multiples) | TODO |
| L6 | (5,0,1)/(5,1,0)/(4,*,*)/(3,3,0) endpoints w/ ẽ conds | decide | **DONE** (`lemma6_330/402/420/501/510`) |
| retarget | single-elt q→any target via Λ_h | qz_lambda + Fermat | **DONE** (`qz_retarget`, Defs) |
| retarget² | two elts (distinct levels) → targets, one unit λ | composition | **DONE** (`qz_retarget_two`, `qz_higher_inert`) |
| retarget_top | level-m elt → any NONZERO target via const mult | Fermat | **DONE** (`qz_retarget_top`) |
| retarget²_top | level-m + level-h<m → both targets, one unit λ | composition | **DONE** (`qz_retarget_two_top`) |
| Rmk8 int wrappers | q(B−B)⊂{0,6}/{0,1,5,6} on integer diffs ⇒ ℓ≤2/3 | qz_subxy_carry | **DONE** (`remark8_i_int`, `remark8_ii_int`, `qz_diff_mem_06/0156`) |
| L7 | ẽ control via Λ_h, `ν(2d−d')` structure (needs m>1) | carry lemmas | **DONE** (`lemma7_i` + `lemma7_ii` axiom-clean) |
| L9(i) | 3-elt compression, ν(x)≠ν(y), both <m ⇒ ℓ≤2 | retarget² + Rmk8(i) | **DONE** (`lemma9_i`) |
| L9(ii) | ν(x)=ν(y)=h<m, r(y)=jr(x) ⇒ q(λy)∈{0,5,6}, ℓ≤j | L4(i) + retarget + e(x,y) | **DONE** (`lemma9_ii_j2`, `lemma9_ii_j3`) |
| L9 ν=m edge | 9(i) with one valuation =m | exact 7^m shift + carry | **DONE** (`lemma9_i_top` + `lemma9_i_dispatch`, `Lemmas.lean`) |
| q-equiv | 7^(m+1)∣(a−b) ⇒ qz equal ∀λ | qz_sub_mul_pow | **DONE** (`qz_eq_of_high_dvd`, `Defs.lean`) |
| L10 | \|A₁\|≥4 numbering (ν-coloring of E) | connectivity cascade + decide | **DONE axiom-clean** (`lemma10` + `lemma10_select` + `cover_distinct`, `Lemmas10_12.lean`) |
| L11 | \|A₁\|=3 numbering | ultrametric + decide | **DONE axiom-clean** (`lemma11`, `Lemmas10_12.lean`) |
| L12 | \|A₁\|=3,\|A₂\|=2 sufficient conds | decide | **DONE axiom-clean** (`lemma12_i` + `lemma12_ii`, `Lemmas10_12.lean`, 2026-07-01) |
| 6.1–6.6 | case analysis by (\|A₁\|,\|A₂\|,\|A₄\|) | weave above | **IN PROGRESS** (agent af765f5358222d978) |
| §7 | m=1: 969 + 32×6 exhaustive search | decide (RISK) | TODO — needs d₆ + gcd=1 hyp |

**Next-session unit:** define `fitsInterval S a L` (representing `ℓ(S) ≤ L`),
prove its API, then **Remark 8** + **Lemma 9** (the first structural
multiplier-existence lemma). L4(ii) carry bounds + L5/L6 endpoints are the
leaf layer they consume.

## Execution order (this multi-session push)

1. **Lemma 6** — decide-based, mirrors Lemma 5. (immediate)
2. **Definitions** `r`, `e`, `ẽ` in Defs + **Lemma 4** + **Remark 8**. (foundational)
3. **Lemma 9** — first hard multiplier-existence lemma; uses Λ_h + carry. (stretch)
4. Lemmas 7, 10, 11, 12.
5. Cases 6.1, 6.2 (|A₁|∈{4,5}, simpler), then 6.3–6.6.
6. §7 (m=1).
7. Assemble `five_band` + `five_band_m1`, rewire Reduction.lean.

## Known risks
- **§7 m=1**: ~1000-case search over ZMod 49/98 with plain `decide` (native_decide
  forbidden). May need a hand-structured pigeonhole instead of brute decide.
- **Lemma 7 (ii)** explicitly requires m>1; the m=1 path MUST route to §7.
- `ẽ`/`e` only defined on residue-related pairs — partial functions; formalize as
  total functions with a residue-relation hypothesis where used.
- **`decide` over `∀ S : Finset (ZMod 7)` silently falls back to `sorryAx`**
  (max recursion depth) — a `lake build` "success" that is actually a sorry.
  ALWAYS `#print axioms` after a heavy `decide`. Use explicit-element forms
  (3-tuple, not arbitrary Finset) to keep `decide` tractable + honest.

## Leaf layer COMPLETE (as of this session)
`lemma5*`, `lemma6_*` (compression endpoints), `qz_2xsuby_carry`/`qz_subxy_carry`
(L4(ii) carry), `remark8_ii_core3` + `fitsInterval`. All axiom-clean.

## `five_band` WIRED (as of this session)
`Case_A5.lean`: `five_band` (5-elt analogue of `four_band`) PROVEN modulo
`five_avoid` (normalize → `band_of_qz_ne`). Reduction.lean's 3 sorries are CLOSED:
no-interior |S|=5 → `five_band`; interior + j₀>0 5th-element cases proven
UNREACHABLE by cardinality. **`five_avoid` is now the SOLE sorry in all of n=7.**

`five_avoid (m) (hm : 1 ≤ m) (d : Fin 5 → ℤ) (hndvd) (hres : dᵢ ∈ {1,2,4}) :`
`∃ lam, ¬7∣lam ∧ ∀ i, qz m (lam·dᵢ) ≠ 0 ∧ ≠ 6`. m≥1; split m=1 (§7) vs m≥2 (§6).

**Next:** prove `five_avoid`. Remark 8(i), Lemma 9 (structural — Λ_h construction
via Lemma 2 + L4 + Rmk8), L7, L10–12, cases 6.1–6.6, §7 (m=1).

### Lemma 9(ii) SUBTLETY (read BS L491–505 carefully before formalizing)
The j=2 construction: retarget `e=2x−y` to `q(λe)=0` (ν(e)>h since r(e)=0), get
`ẽ(λx,λy)∈{0,1,6}` via L4(ii), then λ'∈Λ_h sets `q(λ'λx)∈{0,6}`. For `ẽ=1` this
yields the MIXED pair `(q(λ'λx),q(λ'λy))=(0,6)`, and then `q(λ'λ(x−y))` is NOT
pinned to `{0,6}` by the ±1 carry bound alone (`0−6+c = {0,1}`, the `1` is bad).
BS must be using the PRECISE carry value, not the bound. Resolve by reading BS's
exact argument (the q-tables / Remark 8(i) application) — do NOT assume the carry
bound suffices. This is the load-bearing gap for L9(ii).

### Lemma 9(i) ν=m edge SUBTLETY
`qz_retarget_top` only reaches NONZERO targets, so the level-m difference can be
set to `q=1` (BS "λx=N/7"), NOT `0`. Then `v₁−v₃ = 1−c ∈ {1,2}` (c∈{0,6}) —
`2 ∉ {0,1,6}`, so `remark8_i_core3` does NOT directly apply. BS's `λx=N/7` likely
means the EXACT residue `7^m` (boundary), and the `q(λ(b₁−b₂))∈{0,6}` claim uses
that exact-residue structure, not just `q=1`. Read BS L487–489 carefully before
formalizing. Tool `qz_retarget_two_top` is ready; the ARGUMENT is the open part.
