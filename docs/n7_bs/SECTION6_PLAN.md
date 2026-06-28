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
| L4(i) | ẽ invariance under Λ_{≤j} | qz_lambda | TODO |
| Rmk8(ii) | `⊂{0,1,5,6}` ⇒ ℓ(X)≤3 | decide (3-elt) | **DONE** (`remark8_ii_core3`, `fitsInterval`) |
| Rmk8(i) | `q(X−X)⊂{0,6}` ⇒ ℓ(kX)≤k+1 | int-level (NOT pure ZMod 7) | TODO — needs q(kX) multiples reasoning |
| L6 | (5,0,1)/(5,1,0)/(4,*,*)/(3,3,0) endpoints w/ ẽ conds | decide | **DONE** (`lemma6_330/402/420/501/510`) |
| L7 | ẽ control via Λ_h, `ν(2d−d')` structure (needs m>1) | carry lemmas | TODO (hard) |
| L9 | 3-elt compression B=A₁, equal residues | Λ_h + L4 | TODO (hard) |
| L10 | \|A₁\|≥4 numbering (ν-coloring of E) | finite | TODO |
| L11 | \|A₁\|=3 numbering | finite | TODO |
| L12 | \|A₁\|=3,\|A₂\|=2 sufficient conds | L5-style | TODO |
| 6.1–6.6 | case analysis by (\|A₁\|,\|A₂\|,\|A₄\|) | weave above | TODO |
| §7 | m=1: 969 + 32×6 exhaustive search | decide (RISK) | TODO |

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
**Next:** Remark 8(i) (int-level multiples), then Lemma 9 (structural — needs
Λ_h multiplier construction via Lemma 2 + L4 + Rmk8), then L7, L10–12, cases.
