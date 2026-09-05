# `intLRC 5` Hard residual — Lean decomposition (Barajas–Serra §3, p = 5)

**Date:** 2026-05-29. **Source:** Barajas–Serra 2008, EJC 15 #R48, §2–§3
(`reports/investigations/n5_source/barajas_serra_2008.pdf`).

## Current state
`IntLRC_5.lean`: BSR/LR proved; Hard Case split on `5 ∣ vᵢ`. The
**no-speed-÷5 subcase is PROVED** (`t = 1/5`, `circDist_fifth_of_not_dvd`).
Residual sorry = Hard Case ∧ `∃ i, 5 ∣ vᵢ`.

## What B–S §3 actually proves
Convention match: their `‖t·d‖ ≥ 1/(|D|+1)`, `|D|=4`, gap `1/5` **= our
`circDist(d·t) ≥ 1/5`** exactly. They produce a **discrete multiplier**
`λ ∈ ℤ_N`, `N = 5^{m+1}`, `m = max ν₅(D)`, with `|λd|_N ≥ N/5` for all `d`;
then `t = λ/N` is the real witness.

### Reduction by 5-adic profile (`D₅(i) = {d : ν₅(d)=i}`)
`|D₅(0)| = #{speeds coprime to 5}`. Mapping to "# speeds divisible by 5":

| #÷5 | `|D₅(0)|` | B–S verdict | Lean route |
|----|-----------|-------------|------------|
| 0 | 4 (m=0, N=5) | Cor 3 (vacuous) | **DONE** (`t=1/5`) |
| 2 | 2 | Cor 3 (`|D₅(i)|≤2 ∀i<m`) | Prime Filtering (Lemma 2) |
| 3 | 1 | Cor 3 | Prime Filtering **or Path A** |
| 1 | 3 (`|D₅(m)|=1`) | explicit ℤ₅ argument | explicit (eqns 4–6) |

So the genuinely hard, "named" case is **exactly one speed divisible by 5**
(`|D₅(0)|=3, |D₅(m)|=1`); the 2-/3-÷5 cases fall to the general Prime
Filtering Lemma.

## Lean component breakdown (new file `IntLRC_5_BarajasSerra.lean`)

### (0) Discrete framework `ℤ_{5^{m+1}}`  (~180 lines)
- `nNorm N x := min (x % N) (N - x % N)`  (= `|x|_N`), `x : ℤ`, into `ℕ`/`ℝ`.
- `qmap m x := (x / 5^m) % 5 : ZMod 5`  (= `q(x)`; which `5^m`-arc).
- `ν₅` via `padicValNat 5` (Mathlib) or `multiplicity`.
- Multiplier sets `Λ j = {1 + 5^{m-j}·k : k < 5}` (j<m), `Λ m = {1,…,4}`.
- Eqn (2): `ν₅(λ·x) = ν₅(x)` for λ unit.
- Eqn (3): `q((1+k·5^{m-j})·x) = q(x) + k·r₅(x)` if `ν₅(x)=j`, else `q(x)`.

### (1) Discrete→real bridge  (~60 lines, clean)
- `circDist_mul_div : circDist ((d:ℝ)*(λ/N)) = (nNorm N (λ*d) : ℝ)/N`  (N>0).
- `q_notMem_0_4_imp_norm : qmap m (λ*d) ∉ ({0,4} : Finset (ZMod 5)) →
   nNorm N (λ*d) ≥ N/5`.
- `bridge : (∃ λ, ∀ d ∈ D, qmap m (λ*d) ∉ {0,4}) → ∃ t:ℝ, ∀ d∈D, circDist(d*t) ≥ 1/5`.
  Then specialise `D = {v₀,v₁,v₂,v₃}` ⇒ `intLRC 5` Hard residual.

### (2) Prime Filtering Lemma 2 + Corollary 3  (~200 lines, intricate)
- `Lemma2`: forbidden sets `F_d ⊂ ℤ₅`; if `Σ_{d∈D₅(j)}|F_d| ≤ 4` (`j<m`) and
  `Σ_{d∈D₅(m)}|F_d| ≤ 3`, then `∃ λ, ∀ d, q(λd) ∉ F_d`. Induction high→low levels.
- `Cor3`: `F_d = {0,4}`; gives the 2-/3-÷5 cases.
- **Optional shortcut:** Path A (pre-jump triple-drop, reuses n=4 machinery +
  generalised shift lemmas) closes **3-÷5** without Lemma 2 (the 3 ÷5 speeds
  share factor 5 ⇒ gcd-≥2 triple ⇒ drop the coprime one → `intLRC_4`). Does
  **not** cover 2-÷5.

### (3) Explicit `|D₅(0)|=3` argument  (~200 lines, finite ℤ₅)
- `A = {d₁,d₂,d₃}` (÷5-free), `d₄` at level m. WLOG `(A)₅ ⊂ {1,2}` (replace
  `d` by `−d`). `A_s` = most-popular class.
- eqn (5): `q((j+1)d) ∈ (j+1)q(d) + {0,…,j}`, `j ∈ {1,2,3}`.
- eqn (6): `ℓ(j·λ_k·A_s) ≤ |A_s|` for some `j,k` (`ℓ` = min length-1 AP in ℤ₅
  covering `q`). Two cases `|A_s|∈{2,3}`, each a finite check (`decide`-able
  once the `q`/`r₅` lemmas are in).
- Conclude `q(λ_k·A) ∩ {0,4} = ∅` for some `k`; `d₄` auto-safe (`|d₄|_N ≥ N/5`
  preserved by units). Feed `bridge`.

### (4) Assembly  (~60 lines)
Case on the `D₅`-profile (`exactly one ÷5` vs rest) → (3) or (2)/Path A → `bridge`.

## Effort estimate
~700 lines total, multi-session. The framework (0)+(1)+(2) is **reusable for
n=7** (same Lemma 2, same bridge, larger prime p=7). The Prime Filtering Lemma
(2) is the hardest single piece (level induction).

## Decision points
- **Lemma 2 vs ad-hoc:** the general Lemma 2 is cleaner & reused at n=7; an
  ad-hoc per-case multiplier construction for |D|=4 might save ~80 lines now but
  doesn't transfer.
- **Path A optimisation:** worth building? Closes 3-÷5 elementarily and is
  reusable, but 1-÷5 and 2-÷5 still need the framework, so it doesn't remove the
  big cost. Recommend **defer** unless we want the partial win.
- **Bienia alternative:** memory says "Bienia simpler"; not yet assessed. Could
  fetch the SFU preprint and compare before committing to the ℤ_N framework.

## Recommended phasing
1. **(0)+(1) foundation** — framework + bridge. Self-contained, unblocks all.
2. **(3) explicit 1-÷5** — the named hard case; finite ℤ₅, high confidence.
3. **(2) Lemma 2 + Cor 3** — for 2-/3-÷5. Hardest; or Path A for 3-÷5 + a
   targeted 2-÷5 multiplier.
4. **(4) assembly** → close the sorry; `#print axioms intLRC_five` clean.
