# The `ρ₀ = 4` leaf, evaluated exactly: a reflection theorem, and (H″) bypassed

2026-09-09. Scripts `experiments/n8/ok_*.py`, all exact rational arithmetic, cells
evaluated at their **entry** point with an explicit entry-vs-exit audit (0 mismatches).
**Retracts the route proposed in `O_RESONANCE_v3.md` §5** — see §7.

---

## 1. The Reflection Theorem  `[PROVED]`

Write `bad(e,t) = { r ∈ ℤ/8 : er + t ≡ 0 or 7 (mod 8) }`, `t_e(x) = ⌊ex⌋`, and

    O = { x : ODD  ⊆ ⋃_e bad(e, t_e(x)) },     V = { x : EVEN ⊆ ⋃_e bad(e, t_e(x)) }.

> **Theorem R (reflection).** For every odd `e` and every `t`,
> `bad(e, e−1−t) = { 7 − r : r ∈ bad(e,t) }`.
> Consequently `V = 1 − O`, hence **`v = o`**, and **`U = O ∩ (1−O)`**.

*Proof.* Put `r' = 7 − r`. Then
`e r' + (e−1−t) = 8e − 1 − (er + t) ≡ −1 − (er+t) (mod 8)`.
If `er+t ≡ 0` this is `7`; if `er+t ≡ 7` this is `0`. So `r ∈ bad(e,t) ⟹ r' ∈ bad(e,e−1−t)`,
and `r ↦ 7−r` is an involution, so the two sets correspond bijectively.
For `x` not a breakpoint, `e(1−x) = e − ex` gives `t_e(1−x) = e − 1 − t_e(x)`. Therefore
`⋃_e bad(e, t_e(1−x)) = 7 − ⋃_e bad(e, t_e(x))`. Since `r ↦ 7−r` maps `ODD` onto `EVEN`
and back, `x ∈ O ⟺ 1−x ∈ V`. ∎

The shift `c = 7` is the **only** one that works: `bad(e,e−1−t) = {c−r}` holds for all
`e ∈ {1,3,5,7}` and all `t` at `c = 7` and at no other `c` (checked over all 32 pairs).
Geometrically confirmed: 0 mismatches between `V(x)` and `O(1−x)` over 194 cells on six
tuples, and `v = o` on all **1278** primitive tuples with speeds `≤ 48`.

## 2. The exact criterion, and the two relaxations it replaces  `[PROVED identity]`

`hp_apriori_v1` (*) is exact:

    |S^c| = |A_none ∩ U| + |A_even ∩ O| + |A_odd ∩ V|,

with `A_even = {t_m ∈ {0,7}}`, `A_odd = {t_m ∈ {3,4}}`, `A_none` the rest, for the
divisible speed `m ≡ 4 (mod 8)`. The leaf closes for `(E,m)` when `|S^c| < 1/2` (the
B-lemma supplies `|B_{m₁} ∪ B_{m₂}| < 1/2`).

`(H″)`'s threshold `o ≤ 1/3` is this identity seen through **two** relaxations —
`|S^c| ≤ o − β + min(1/4, o)`, then `β → o/4`. The second is a limit, not a bound.
**Evaluating the identity itself costs nothing and is far weaker.**

## 3. The `(H″)` exceptions are not exceptions to what `(H″)` is for  `[EMPIRICAL — exhaustive]`

Over **1278** primitive unit 4-tuples (speeds `≤ 48`) × **38** divisible speeds
`m = 4,12,…,300` — **48 564 pairs** — the pairs with `|S^c| ≥ 1/2` number exactly **one**:

| `E` | `m` | `|S^c|` | `o = v` | `u` |
|---|---|---|---|---|
| `(1,3,5,7)` | `4` | `9/14 = 0.642857` | `16/35` | `1/7` |

- **`(1,11,5,7)` is not an exception at all.** It has `o = 26/77 > 1/3`, so `(H″)` does not
  cover it — yet `max_m |S^c| = 5/11 = 0.4545 < 1/2`. It closes.
- **`(1,3,5,7)` fails at `m = 4` only**, and closes at all 37 other `m`.

Next largest: `(1,3,13,15)` at `m=4`, `|S^c| = 179/390 = 0.4590`. So the exact criterion
has an ~8% margin, against `(H″)`'s ~6% margin on a strictly stronger demand.

The single failing cell is the speed set `{1,3,4,5,7}`. There `|S| = 5/14 > 0`, so `S` is
**non-empty** — what fails is the B-lemma comparison, not the existence of a witness. That
one cell needs a direct witness, not a measure bound.

## 4. The limit case  `[PROVED reduction; the limit itself CONDITIONAL]`

*If* the three `A`-sets equidistribute against `(O,V,U)` as `m → ∞` — a Weyl statement,
**not proved here, and exactly the kind of claim that fails on resonance** — then
`|S^c| → (1/4)o + (1/4)v + (1/2)u`, and closure needs `o + v + 2u < 2`. By Theorem R,
`v = o` and `U ⊆ O` so `u ≤ o`; the condition becomes

    o + u < 1 ,   for which   o < 1/2   suffices.

Measured maximum of `o + u` over all 1278 tuples: `16/35 + 1/7 = 3/5`, at `(1,3,5,7)`.
**So the limit needs `o < 1/2`, where the old chain demanded `o ≤ 1/3`.** The gap `(H3u)`
— the resonance tail bound, the sole open item of `O_RESONANCE_v2/v3` — sat entirely
inside the difference between those two thresholds.

## 5. The Isolation Lemma  `[PROVED]`

> Refine `[0,1)` by `B = ⋃_ρ {2k/e_ρ}`, the breakpoints of `a_ρ = ⌊e_ρx/2⌋ mod 4`. Then no
> two adjacent cells are both in `O`, unless the breakpoint between them is shared by two
> or more speeds.

*Proof.* On `O` the four `ν_ρ` are distinct, hence exhaust `(ℤ/2)²`. Crossing a breakpoint
owned by a single `ρ` sends `a_ρ → a_ρ + 1 (mod 4)`, so `ν_ρ` moves to a **different**
value of `(ℤ/2)²` — which is already occupied by some `ν_σ`. Injectivity fails. ∎

Shared breakpoints are the multiples of `2/gcd(e_ρ,e_σ)`, so for pairwise-coprime speeds
`x = 0` is the only one. Verified: **0** adjacent `O`-pairs across single-speed breakpoints
over 1278 tuples; 32 across multi-speed breakpoints, exactly the allowed escape.

**What it gives and what it does not.** It bounds the `O`-cell **count** by about half.
It does **not** bound the measure — good cells are systematically long. Observed maximum
count fraction `2/7 = 0.2857` against measure `16/35 = 0.4571`, both at `(1,3,5,7)`. So
`o < 1/2` **in measure remains open**; the lemma is a start on it, not a proof of it.

## 6. Two routes closed  `[PROVED — counterexample]`

- **The 3-body relaxation fails.** `ν` injective on 4 indices implies it on every 3-subset,
  so `o ≤ min over the 4 triples`. That relaxation proves `o ≤ 1/3` for **5 of 614**
  non-exceptional tuples (0.8%); the 2-body version for **0**. Any proof of a bound on `o`
  must be genuinely 4-body.
- **No pairwise lower bound.** `p_{ρσ} = P(ν_ρ = ν_σ) ≥ 1/4` is **false**: the minimum is
  `1/7`, at `(1,3,5,7)`, pair `(e_1,e_7)`. Generic is `1/4`.

Recorded as a self-test: the exact Möbius identity over the partition lattice of
`{1,3,5,7}`, `o = 1 − Σ_6 p + 2Σ_4 T + Σ_3 Q − 6F`, holds on **616/616** tuples.

## 7. Retraction — `O_RESONANCE_v3.md` §5  `[RETRACTED]`

v3 §5 proposed bounding `|Δ| ≤ CAP · Σ 1/Π(p)` over the primitive rays. That is the
**ray-level absolute sum**, and it was already known not to work:
`reports/n8_tail_bound.md` §3 records it truncated at ray height 100 as

> `0.178387 = 2.14 ×` the whole `1/12` budget, at `e = (17,3,21,7)`

a truncation, hence a *lower* bound for the full absolute sum. No termwise bound of that
shape can prove `(H3u)`. I proposed a route my own corpus had already closed; §5's
single-ray half (`Δ = |Ray| ≤ 1/32`) is unaffected and stands.

The retraction costs little, because §4 above removes the need for `(H3u)` altogether.

## 8. Grades and what is open

| item | grade |
|---|---|
| Theorem R, `v = o`, `U = O ∩ (1−O)` | **PROVED** |
| Isolation Lemma | **PROVED** |
| 3-body and 2-body relaxations insufficient; `p ≥ 1/4` false | **PROVED — counterexample** |
| exactly one failing `(E,m)` pair | **EMPIRICAL**, exhaustive over speeds `≤ 48`, `m ≤ 300` |
| `m → ∞` limit `= (1/4)o+(1/4)v+(1/2)u` | **CONDITIONAL** — unproved equidistribution |
| `o < 1/2` in measure | **OPEN** — the isolation lemma gives the count, not the measure |
| the single cell `{1,3,4,5,7}` | **OPEN** — needs a direct witness; `|S| = 5/14 > 0` |

**Open, in order:** (i) `o < 1/2` in measure; (ii) the finite-`m` statement `|S^c| < 1/2`
uniformly, which is what the census supports and the limit argument does not reach;
(iii) the one cell `{1,3,4,5,7}`.
