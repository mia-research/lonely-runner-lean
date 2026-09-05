# n=5: Bienia vs Barajas–Serra — assessment & recommendation

**Date:** 2026-05-29. Sources in `reports/investigations/n5_source/`:
`bienia_flows.pdf` (Bienia–Goddyn–Gvozdjak–Sebő–Tarsi 1997, §3–4),
`barajas_serra_2008.pdf` (§2–3).

## Bienia's k=4 proof (= our intLRC 5), structure

Works **entirely with real positions** `⟨x⟩ ∈ [0,1)` and **concrete times**
(`j/5`, `α/v₁`, doublings `2ⁱx`). No modular framework. `k+1 = 5` prime.

- **Partition of the circle:** `{0} ∪ C₁ ∪ C₂`, where `C₂ = (1/5,2/5)∪(2/5,3/5)∪
  (3/5,4/5)` (robust-distant interior) and `C₁` = everything else distant-or-near
  (incl. the fragile boundary pts `{1/5,2/5,3/5,4/5}`).
- **`D := {r : 5 ∣ vᵣ}`.** Partition runners `R₀(x)=D∪{r:xᵣ=0}`, `R₁=(R∖D)∩C₁`,
  `R₂=(R∖D)∩C₂`.
- **Lemma (3) [core pigeonhole]:** if `D` distant at `x` and `|R₂(x)|<|R₀(x)|`,
  then `R` distant at some `⟨x+(j/5)v⟩`, `j∈{1..4}`. Proof: prime ⇒ for `5∤vᵣ`,
  `{⟨(j/5)vᵣ⟩}=` all nonzero fifths; a runner in `Rₘ` is distant in exactly
  `4−m` of the 4 listed positions; total non-distant incidences `≤|R₁|+2|R₂|<4`
  ⇒ some position is all-distant.
- **Case |D|=0:** `t=1/5`. **(already DONE — `circDist_fifth_of_not_dvd`)**
- **Case |D|∈{2,3}:** induction (LRC for `|D|` runners = `intLRC_3`/`intLRC_4`,
  **we have both**) gives `x` with `D` distant; then `|R₂|≤3−|D|<|D|≤|R₀|` ⇒
  Lemma (3). Clean.
- **Case |D|=1** (the crux): WLOG runner 1 fastest, `D={2}`. Split on
  `gcd(v₁,v₃)`: if `>1`, reduce by **pre-jump (2)** (drop a runner → `intLRC_4`)
  or **Cor (4)** (a counting cor of Lemma 3); if `=1`, a **doubling argument**
  (`α v₃≡1 mod v₁`; iterate `⟨2ⁱx⟩` until runner 2 distant, runners 1,3 stay
  controlled) ⇒ Lemma (3).

## Comparison

| | Bienia | Barajas–Serra |
|---|---|---|
| Machinery | real circle geometry + pigeonhole | `ℤ_{5^{m+1}}` framework, `q`-map, Prime Filtering Lemma (level induction) |
| New infra | Lemma (3) + Cor (4) + doubling | `\|·\|_N`, `q`, `ν₅`, multipliers, **discrete→real bridge** |
| Reuses our code | `circDist`, **pre-jump** (have, generalised), **`intLRC_3`/`intLRC_4`** (induction base) | almost nothing |
| Hard sub-case | `\|D\|=1` doubling (~200 lines) | `\|D₅(0)\|=3` finite-ℤ₅ (~200 lines) |
| Est. total | ~450–550 lines, elementary | ~700 lines, abstract |
| n=7 reuse | none (Bienia stops at k≤4) | **yes** (same framework, p=7) |

## Recommendation: **Bienia for n=5.**
- More elementary ⇒ higher confidence, fewer places for a subtle framework bug.
- Reuses existing `circDist`, the (generalised) pre-jump, and `intLRC_3/4` as the
  induction base. The `|D|=0` case is *already done*.
- No need to build/verify the `ℤ_N`-to-ℝ bridge or `ZMod` valuation machinery.
- Caveat: n=7 will still need the B–S framework later, so B–S "reuse" only pays
  off if we commit to it for n=7 anyway — that decision can wait (n=6 Renault is
  next, a different technique).

## Proposed Bienia build order
1. **Generalised shift lemmas** (gap `g ≤ 1/4`): lift `exists_shift_distant` /
   `exists_step_distant` (currently hard-wired to `1/4`) to general gap. Reusable
   for the pre-jump at `1/5`.
2. **Lemma (3)** (pigeonhole over the 5 positions). The core.
3. **|D|∈{2,3}** via induction + Lemma (3).
4. **Cor (4)** + **|D|=1** doubling argument.
5. Assembly → close the residual sorry; `#print axioms` clean.
