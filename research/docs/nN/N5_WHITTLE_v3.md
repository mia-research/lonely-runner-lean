# Whittling n = 5 to 99.13%, and every criterion in Lean

2026-09-21, version 3. Supersedes `N5_WHITTLE_v2.md` (80.9%). Owner's instruction: Lean P5 too,
then keep mapping the residue.

Artefacts: `LonelyRunner/LRC/Spec/{DoorsN,FlankFiniteN,ResonanceN,WindowN,SelfSimilarN,OtherFlankN}.lean` ·
`experiments/n8/full_audit_v2.{lean,out}` · `experiments/nN/n5_otherflank_v1`, `n5_p6_v1`,
`n5_p6_general_v1`, `n5_total_v2`, `n5_total_v3`, `n5_last_v1` (each `.py` + `.out`)

**No `intLRC` anywhere.** Every criterion is a framework theorem or an exact finite computation.

---

## 1. Where it stands

| | proved | residue |
|---|---|---|
| before this session | 42.4% | 57.6% |
| + prime theorem (`n ∤ e`) | 66.1% | 33.9% |
| + the `n ∣ e` half | 72.6% | 27.4% |
| + sharp window | 80.9% | 19.1% |
| + **P6 at a non-maximal flank** | 96.1% | 3.9% |
| + **the `t`-generalisation** | **99.13%** | **0.87%** |

Exhaustive over primitive card-4 sets to `[1,40]` (85,771); `[1,30]` agrees to 0.15%.

| criterion | coverage |
|---|---|
| P1′ no non-flank disparity divisible by 5 | 52.6% |
| P2 `d_max ≤ 4·d_min` | 43.0% |
| P3 `d_max ≤ 15` (`decide`) | 1.5% |
| P4 sharp window `W > 1/e` | 15.3% |
| P5 all non-flank divisible by 5 | 0.3% |
| **P6** `k`-construction at a 5-multiple flank, `t`-budget 4 | **~50%** |
| **union** | **99.13%** |

---

## 2. P6: the idea that moved it

`lonely_iff_exists_flank` permits **any** flank, not the largest. Every residue set contains a
disparity divisible by 5 — take **that** as the flank, even when it is not the maximum.

With `a = k·e + t` and `d = c·e + s` where `c = ⌊d·t/e⌋`, `s = d·t mod e`,

> `d·a = e·(d·k + c) + s`,  so  `d·a mod n·e = e·((d·k + c) mod n) + s`

which lies in `[e, (n−1)e]` exactly when `(d·k + ⌊d·t/e⌋) mod n ∈ {1,…,n−2}`, or `= n−1` with
`e ∣ d·t`. For `d < e` and `t = 1` the offset vanishes and this is `flankWorks_of_prime_dvd`;
**the offset is what makes a non-maximal flank usable.**

**The pigeonhole is weaker here, and that is why existence of a good `k` is a hypothesis rather
than free.** With `c = 0` each disparity forbids one `k`; with `c ≠ 0` it can forbid two (the
residues `0` and `n−1`).

**The `t`-budget saturates.** Allowing `t ∈ {1, 6, 11, 16}` lifts coverage of what P1′–P5 leave
from 79.0% to **94.4%**, and no further `t` helps — measured to a budget of 20. So the criterion
is genuinely bounded, not a disguised full search.

---

## 3. Every criterion is now in Lean  `[136 declarations, all axiom-clean]`

| file | decls | carries |
|---|---|---|
| `DoorsN` | 94 | the whole `n = 8` Spec layer at every `n`; `doors_agree` |
| `FlankFiniteN` | 15 | decidable predicate, bridge, P2, P3, scaling, gap criterion |
| `ResonanceN` | 16 | resonance, prime ⟺ divisibility, **P1′** both halves |
| `WindowN` | 5 | **P4**, with a worked residue instance |
| `SelfSimilarN` | 3 | **P5**, with the `(5,10,15,21)` instance |
| `OtherFlankN` | 3 | **P6** and its `t`-generalisation, with the `(1,2,10,16)` instance |

**136 of 136 axiom-clean. No `sorry`, no `native_decide`, no `admit`.**

Each new criterion carries a worked instance from the residue, so none is vacuous:
`(1,2,5,16)` for P4, `(5,10,15,21)` for P5 (the extreme case, `|L| = 0.10`, two openings),
`(1,2,10,16)` for P6 (flank **10**, not the largest 16).

---

## 4. The final 0.87%, characterised

749 sets to `[1,40]`. Sharply structured:

| | |
|---|---|
| sets with exactly **one** 5-multiple | **749 of 749 (100%)** |
| that multiple is **5 itself** | 650 (87%) |
| `d_min = 5` (the multiple is the smallest) | 528 (70%) |
| minimum openings | **3** |

**Why P6 misses them.** P6 uses the 5-multiple as the flank. When that multiple is `5`, the
flank has only five openings, and the other disparities are far larger, so the offsets
`⌊d·t/5⌋` scatter across all residues. A tiny flank has too little room.

So the stubborn family is exactly: *one small 5-multiple, everything else coprime to 5*. It is
not tight — three openings minimum — and it is the mirror of P6: the multiple wants to be
handled at a **non**-multiple flank, where the prime construction `a = e·s` sends it to residue
`0`. Closing it needs the two moduli reconciled, which is the same obstruction named in
`N5_RESIDUE_MECHANISM_v1.md` §3.

---

## 5. Grades

| claim | grade |
|---|---|
| all six files, 136 declarations | `[PROVED — full_audit_v2.out, axiom-clean, no `sorry`]` |
| P5 self-similar reduction | `[PROVED — flankWorks_of_multiples]` |
| P6 at a non-maximal flank | `[PROVED — flankWorks_of_shifted]` |
| P6 `t`-generalisation | `[PROVED — flankWorks_of_shifted_t]` |
| each criterion non-vacuous on a residue set | `[PROVED — three worked instances]` |
| union covers 99.13% | `[VERIFIED — exhaustive to [1,40]]` |
| `t`-budget saturates at 4 | `[VERIFIED — no gain to budget 20]` |
| the final 0.87% | **not proved** — characterised, minimum 3 openings |

**Scope.** Whole-number difference sets of card 4, exhaustive to `[1,40]`; by
`lonely_flank_smul_iff` this is every rational set of that shape. Irrational ratios are untouched.
P4 and P6 are *criteria* verified per set, in the way the census is; P1′, P2, P3, P5 are uniform
theorems.
