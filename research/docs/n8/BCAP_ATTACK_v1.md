# BCAP: the `B ∩ I_A ≠ ∅` hypothesis of Theorem 5.2-P — attack record

2026-09-07. Target: the combinatorial claim behind Theorem 5.2-P of
`lrc_proof_allN_v11_8.md`. Scripts (exact integer/`Fraction` arithmetic, no floats), all
under `experiments/n8/`: `bcap_attack_v1.py` (the object) and
`bcap_{search,tightness,scope,njoint,closed_witness,disjoint,runnerdistinct}_v1.py`.

## 0. Outcome

**Reached (a) a complete PROVED reduction and (c) COUNTEREXAMPLES.** The claim as stated
is **false**: it is *equivalent* to a strict form of LRC for the merged speed set, and
fails on exactly the tight instances. Theorem 5.2's own conclusion is **not** damaged —
only its cell-level sufficient condition is.

## 1. The reduction (PROVED)

For finite `S`, `L = lcm(S)`, put `Λ(S) := { t ∈ [0,1) : {ut} ∈ [1/n, 1−1/n) ∀u ∈ S }`.

**Lemma 1 [PROVED].** `Λ(S) = ⋃_{m ∈ Good(S,L)} [m/(nL), (m+1)/(nL))`; equivalently
`Good(S,L)` is the set of `nL`-cells wholly inside `Λ(S)`.
*Proof.* Fix `u`, put `s := L/u ∈ Z⁺`. For `t = (m+θ)/(nL)`, `θ ∈ [0,1)`, write
`m = qs + r` with `0 ≤ r < s` and `ε := (r+θ)/s ∈ [0,1)`; then `ut = (q+ε)/n`, and with
`a := q mod n` we get `{ut} = (a+ε)/n`. So `{ut} ∈ [1/n, 1−1/n) ⟺ a + ε ∈ [1, n−1)`.
As `a ∈ Z` and `ε ∈ [0,1)`: `a ≤ n−2` forces `a+ε < n−1`, `a = n−1` forces `a+ε ≥ n−1`.
Hence the criterion is `a = ⌊m/(L/u)⌋ mod n ∈ [1,n−2]`, independent of `θ`. ∎

**Lemma 2 [PROVED].** With `T := S_G ∪ p·S_A`, `Λ(T) = Λ(S_G) ∩ {t : {pt} ∈ Λ(S_A)}`,
since `{pvt} = {v·{pt}}` for `v ∈ Z`. ∎
**Theorem A [PROVED].** For every `n ≥ 3`, all finite `S_G, S_A` and every `p ≥ 1`,
> `B ∩ I_A ≠ ∅  ⟺  Good(T, lcm T) ≠ ∅`,  where `T := S_G ∪ p·S_A`.

*Proof.* Put `N0 = n L_G L_A`, `W = L_A p`, so `N0/L_G = n L_A`. For `a ∈ I_G` let
`Arc(a) ⊆ Z/N0` be the reduction of `[aW, aW+W)`; by definition
`B = {⌊x/L_G⌋ : x ∈ Arc(a), a ∈ I_G}`. Identify `x ∈ Z/N0` with the grid point `x/N0` of
`R/Z`; then `⌊x/L_G⌋` indexes the `nL_A`-cell `D_β` containing it. Since
`aW/N0 = ap/(nL_G)` and `W/N0 = p/(nL_G)`, the real arc carrying `Arc(a)` is exactly the
image of the `G`-cell `C_a := [a/(nL_G), (a+1)/(nL_G))` under `t ↦ pt mod 1` (the whole
circle when `p ≥ nL_G`), and because `aW` and `W` are integers `Arc(a)` is precisely its
set of `1/N0`-grid points. `D_β` corresponds to the integer interval `[βL_G,(β+1)L_G)`.
Two cyclic intervals in `Z/N0` with integer endpoints and length `≥ 1` meet as real sets
iff they share an integer: their intersection is again a cyclic interval with integer
endpoints, and if non-empty it contains its left endpoint. Hence
`β ∈ B ⟺ ∃a ∈ I_G : D_β ∩ p·C_a ≠ ∅ ⟺ D_β ∩ p·Λ(S_G) ≠ ∅`, using
`Λ(S_G) = ⋃_{a∈I_G} C_a` (Lemma 1). Since also `Λ(S_A) = ⋃_{β∈I_A} D_β`,
`B ∩ I_A ≠ ∅ ⟺ p·Λ(S_G) ∩ Λ(S_A) ≠ ∅ ⟺ Λ(T) ≠ ∅` (Lemma 2) `⟺ Good(T) ≠ ∅`. ∎

`gcd(p, L_G) = 1` is **not used**. Cross-checked against the literal definition of `B`
and the arc simplification on 2830 non-vacuous configurations: 0 mismatches.
**Lemma 3 [PROVED].** With `g(T) := max_t min_{u∈T} ‖ut‖`:
`Good(T) ≠ ∅ ⟺ g(T) > 1/n ⟺ μ({t : ‖ut‖ ≥ 1/n ∀u ∈ T}) > 0`.
*Proof.* If `g(T) > 1/n` a maximiser lies in `Λ(T)`. Conversely `Good(T) ≠ ∅` yields an
interval on which `min_u ‖ut‖ ≥ 1/n`; that function is piecewise linear with every piece
of slope `±u ≠ 0`, hence non-constant on any interval, so it exceeds `1/n` somewhere. The
measure form follows as the good set is a finite union of closed intervals. ∎

**Corollary A1 [PROVED].** *The claim holds for `(n,S_G,S_A,p)` **iff**
`g(S_G ∪ p·S_A) > 1/n`.* So in the LRC-shape regime `|S_G|+|S_A| = n−1`, Theorem 5.2-P's
hypothesis is equivalent to the **strict** form of LRC for the merged speed set, and fails
exactly on the **tight** instances (`g = 1/n`, the floor LRC forces).

## 2. Counterexamples (PROVED by exact computation)

All satisfy every stated hypothesis (`n ≥ 3`, distinct speeds, `gcd(p,L_G) = 1`,
`I_G ≠ ∅`, `I_A ≠ ∅`), are **LRC-shape** (`δ = k_G + k_A − (n−1) = 0`), have `p < n L_G`
(hard regime), and are verified three ways: literal `B`, arc form, and `N_joint`
recomputed from scratch (`bcap_njoint_v1.py`).

| n | S_G | S_A | p | runners T = S_G ∪ pS_A | g(T) | \|I_G\| | \|I_A\| | \|B\| | nL_A | B ∩ I_A |
|---|---|---|---|---|---|---|---|---|---|---|
| 8 | {1,2,3,4,5,6} | {1} | 7 | {1,…,7} | 1/8 | 42 | 6 | 2 | 8 | **∅** |
| 8 | {1,2,3,4,6,7} | {1} | 5 | {1,…,7} | 1/8 | 90 | 6 | 2 | 8 | **∅** |
| 8 | {1,4,5,6,7,11} | {1} | 13 | {1,4,5,6,7,11,13} | 1/8 | 870 | 6 | 2 | 8 | **∅** |
| 8 | {1,2,3,4,5,12} | {1} | 7 | {1,2,3,4,5,7,12} | 1/8 | 50 | 6 | 2 | 8 | **∅** |
| 8 | {1,3,5,7} | {1,2,3} | 2 | {1,…,7} | 1/8 | 186 | 22 | 22 | 48 | **∅** |
| 5 | {1,3,7} | {2} | 2 | {1,3,4,7} | 1/5 | 21 | 6 | 4 | 10 | **∅** |
| 3 | {1} | {1} | 2 | {1,2} | 1/3 | 1 | 1 | 2 | 3 | **∅** |

Hand-checkable smallest instance: `n = 3`, `S_G = S_A = {1}`, `p = 2`, `L_G = L_A = 1`,
`I_G = I_A = {1}`, `N0 = 3`, `W = 2`; the single band `m ∈ {2,3}` reduces to
`m mod 3 ∈ {2,0}`, so `B = {0,2}` and `B ∩ {1} = ∅`.

Headline `n = 8`: `S_G = {1,…,6}`, `S_A = {1}`, `p = 7`. Runner speeds `{1,…,7}` are
distinct, `p·S_A ∩ S_G = ∅`, `gcd(7,60) = 1`, `7 < 480`. `B = {0,7}` — exactly the two
forbidden cells — against `I_A = {1,…,6}`; `N_joint = 0` over all `M = 3360` fine cells.

**Structure.** Every counterexample has `T` a *tight* instance (`g(T) = 1/n` exactly, by
exact max-min gap in `bcap_tightness_v1.py`). At `n = 8`, speeds `≤ 12`, `p ≤ 13`,
LRC-shape, runner speeds distinct: **10 counterexamples over 4 tight sets** — `{1,…,7}`,
`{1,2,3,4,5,7,12}`, `{1,4,5,6,7,11,13}`, `{2,4,6,8,10,12,14}`.

**Discrepancy to check — not a defect claim.** 24 LRC-shape counterexamples lie inside
the range Remark 5.2-P states it scanned (`n ≤ 7`, `|S_G| ≤ 3`, `|S_A| ≤ 2`, `p ≤ 19`
prime, hard regime; here speeds `≤ 12`, 127 386 inputs enumerated in
`bcap_njoint_v1.py`), e.g. `n = 5`, `S_G = {1,3}`, `S_A = {1,2}`, `p = 2`,
`N_joint = 0`. Remark 5.2-V's table records **0** counterexamples at `δ = 0`. The most
likely explanation is an unstated filter in the mining harness
(`LonelyRunner/scripts/phase5_residue_structure.py`); re-run it against these 24
configurations before amending either record.

## 3. What is NOT broken

**[PROVED]** At all 28 counterexamples in `bcap_closed_witness_v1.py`, Theorem 5.2's
actual conclusion `G ∩ {t : {pt} ∈ A} ≠ ∅` **still holds**, with an exact rational witness
`t*` attaining `min_u ‖u t*‖ = 1/n` (28/28; `t* = 1/8` in the headline case). Reason: for
`|T| ≤ n−1`, LRC (`n ≤ 7` verified in this project; `n = 8` Rosenfeld 2025 [CITED]) gives
`g(T) ≥ 1/n`, so `G_T ≠ ∅` even when `μ(G_T) = 0`.

The defect is localised: `I_G`/`I_A` keep only cells whose **open interior** lies in the
good set, and at a tight instance every witness is a **cell endpoint**. In the headline
case `t* = 1/8 = 60/480` is the left endpoint of `G`-cell 60 and indeed `60 ∈ I_G`; what
is lost is the `A`-side, since `{7t} > 7/8` for `t` just above `1/8`. Theorem 5.2-P is a
sufficient condition that cannot see measure-zero witnesses.

## 4. Special cases proved

**Theorem B [PROVED, unconditional].** Let `c` be the largest number of cyclically
consecutive integers in `I_G ⊆ Z/(nL_G)`. If `p·c ≥ n L_G` then `B = [0,nL_A)`, so the
claim holds. *Proof.* `Λ(S_G)` contains an interval of length `c/(nL_G)` (Lemma 1); its image under
`t ↦ pt mod 1` is an arc of length `p·c/(nL_G) ≥ 1`, i.e. all of `R/Z`. By the displayed
equivalence in Theorem A every `β` lies in `B`, and `I_A ≠ ∅` finishes. ∎
With `c ≥ 1` this recovers the manuscript's easy case `p ≥ n L_G`, and is strictly
sharper whenever `c ≥ 2`. It correctly fails to fire on every counterexample.

**Theorem C [PROVED, unconditional].** If `g(S_G ∪ p·S_A) > 1/n` the claim holds; by
Corollary A1 the condition is also necessary, so this is the sharpest possible sufficient
condition. **Corollary [PROVED conditional on LRC(n), unconditional for `n ≤ 8`]:** if
`|S_G| + |S_A| ≤ n−1` and `S_G ∪ p·S_A` is not a tight instance for `n` runners, the claim
holds.

## 5. Search scope (EMPIRICAL, exact ranges)

- Theorem A cross-checked on 2830 non-vacuous random configurations (`n ∈ {3,4,5,6,8}`,
  `|S_G| ≤ 3`, `|S_A| ≤ 2`, speeds `≤ 9`, `p ≤ 13`) and Lemma 3 on 735 sets: 0 mismatches.
- LRC-shape sweeps: `n = 3` (speeds `≤ 6`), `4` (`≤ 6`), `5` (`≤ 7`), `6` (`≤ 8`),
  `8` (`≤ 8, ≤ 10, ≤ 12`), `p ≤ 13`; plus the 127 386-input Remark-5.2-P-range sweep.
- Requiring `S_G`, `S_A` **and** `p·S_A` mutually disjoint at `n = 8`, speeds `≤ 14`:
  **0 counterexamples** — every `n = 8` counterexample found has `S_A ∩ S_G ≠ ∅`, harmless
  for the application (raw `A`-speeds are not runner speeds) but a real limit on the range
  searched. `n = 5`, `S_G = {1,3,7}`, `S_A = {2}`, `p = 2` is fully disjoint.

## 6. Consequence for the programme

By Corollary A1, `B ∩ I_A ≠ ∅` is equivalent to strict LRC for `S_G ∪ p·S_A`. In the
LRC-shape regime it therefore cannot be established without LRC(`n`)-strength input plus
a classification of tight instances; proving it as a step towards LRC(`n`) would be
circular, and it is false on the tight instances regardless. Two routes remain:
(i) Theorem B, unconditional and strictly extending the easy case; (ii) repairing the cell
convention so boundary witnesses survive — §3 shows the witness is always present, merely
invisible at the chosen resolution.
