# The n = 5 residue: pigeonhole audited, and a first map of the 27.4%

2026-09-21, version 1. Two things the owner asked for: whether the pigeonhole argument is
covering in disguise, and a first pass of patterns and clues over what is left.

Artefacts: `experiments/nN/pigeonhole_vs_covering_v1.{py,out}` · `n5_residue_map_v1.{py,out}` ·
`n5_residue_construct_v1.{py,out}` · `n5_residue_u_v1.{py,out}` · `prime_unified_v1.{py,out}`

---

## 1. Is the pigeonhole covering in disguise?  `[NO — but it is exactly tight]`

**The thresholds differ, so they cannot be the same argument.**

| | threshold on the diagonal | reached? |
|---|---|---|
| covering (manuscript §8.2) | `n > 2(n−1)` | **at no order** |
| pigeonhole (§5 of `ResonanceN.lean`) | `#non-flank ≤ n − 2` | **at every order** |

**The mechanisms differ.** Covering says each disparity blocks a *fraction* `2/n` of a continuum
and the fractions add; it dies because `(n−1)·(2/n) > 1`. The pigeonhole says each disparity
blocks **exactly one** element of a finite set of `n − 1` candidates, because `k ↦ d·k mod n` is
a **bijection** on `(ℤ/n)*`. The exactness comes from group structure, not from measure, and it
is what makes the count work where the measure does not.

**The caveat, stated because it is real.** The argument sits exactly on its threshold: `n − 1`
candidates against `n − 2` disparities, margin one. And it is genuinely binding, not slack —
at `n = 5`, **22,200 of 55,008 sets (40%) have precisely one good `k`**, the forbidden set being
full size. A subject with one extra disparity would break it.

| order | candidates | disparities | sets with exactly 1 good `k` |
|---|---|---|---|
| 5 | 4 | 3 | 22,200 / 55,008 |
| 7 | 6 | 5 | 7,596 / 51,066 |
| 11 | 10 | 9 | 5,120 / 167,960 |

---

## 2. The residue, mapped

Residue = some **non-flank** disparity divisible by 5, wide ratio, `d_max > 15`. **27.4%** of
order five (down from 57.3% before the prime work).

| feature | measurement (`[1,50]`, 56,967 sets) |
|---|---|
| exactly one non-flank 5-multiple | **46,809 (82.2%)** |
| two | 9,694 (17.0%) |
| three | 464 (0.8%) |
| flank itself **not** a multiple of 5 | 44,341 (77.8%) |
| minimum working openings | **2** |
| sets with ≤ 2 openings | 82, all with `d_max ≤ 33` |
| `gcd(m, e)` effect on mean openings | 8.16 – 9.29 — **no discrimination** |

So the dominant case is sharp: **one inner 5-multiple, flank coprime to 5**.

---

## 3. The structural clue: a mixed-modulus system

For `d = 5m` the factor cancels — `5m·a/(5e) = m·a/e` — so

| disparity | rule | modulus |
|---|---|---|
| non-multiple `d` | `d·a mod 5e ∈ [e, 4e]` | `5e` |
| multiple `5m` | `m·a mod e ∈ [e/5, 4e/5]` | **`e`** |

The residue is a system of conditions at **two different moduli**. That is exactly what the
prime construction cannot handle: its `a = e·s` sends `m·a mod e` to `0`, the worst possible
value, so the inner multiple is precisely what blocks at the opening the theorem names.

**A perturbed form.** Writing `a = e·s + t` with `e·s ≡ 1 (mod 5)` forces `t ≡ 0 (mod 5)`,
`t = 5u`, and then

* the multiple's condition becomes `m·t mod e ∈ [e/5, 4e/5]` — governed **entirely by `t`**;
* a non-multiple reads `e·q_d + d·t` with `q_d = d·e⁻¹ mod 5`, needing `q_d ∈ {1,2,3}`.

**`q_d ∈ {1,2,3}` is the same residue-miss condition as the `n ∣ e` case** (`GoodK`). The two
halves of the proved theorem and the residue all turn on `d·e⁻¹ mod n` avoiding `0` and `n−1`.
That is the thread worth pulling.

---

## 4. Why `u` is not the answer by itself  `[measured]`

`a = (e·s + 5u) mod 5e` parametrises every admissible `a`, so *some* `u` always works — the
question is whether the smallest one is bounded. **It is not:**

| range | `[1,30]` | `[1,40]` | `[1,50]` |
|---|---|---|---|
| max smallest-`u` | 20 | 26 | **33** |

Mean is small (≈ 4) and barely varies with `e mod 5` (4.10, 3.74, 4.06, 4.91 for residues
1,2,3,4), so there is no clean parity split here.

**The hard cases have a shape.** The extremes are `(6,15,21,28)`, `(1,4,35,37)`, `(1,4,45,47)` —
that is `(1, 4, 5m, 5m+2)`: the inner 5-multiple sitting **immediately below the flank**. When
`5m` is adjacent to `e`, `m·a mod e` moves nearly in step with `a`, and the two moduli fight.
That is the clue to chase.

*(An earlier run reported 93.5% coverage for this construction; it had truncated the `u` range
instead of reducing mod `5e`. Corrected here — the figure was a floor, not the reach.)*

---

## 5. Grades

| claim | grade |
|---|---|
| the pigeonhole is not the covering argument | `[PROVED — the thresholds differ; covering reaches no order on the diagonal, pigeonhole every one]` |
| it is exactly tight and genuinely binding | `[VERIFIED — 40% of `n = 5` sets have exactly one good `k`]` |
| residue is 27.4%, 82% with one inner multiple | `[VERIFIED — exhaustive to [1,50]]` |
| the mixed-modulus rule for 5-multiples | `[PROVED — the factor 5 cancels]` |
| smallest `u` is unbounded | `[VERIFIED — 20, 26, 33 over growing ranges]` |
| hard cases are `(…, 5m, 5m+2)` | `[EMPIRICAL — the observed extremes; not a characterisation]` |
| the residue itself | **not proved** |
