# The order-5 certificate, decomposed — and why the structure is not about five

2026-09-21, version 1. Follows `N5_CORRECTIONS_AND_LAP_TRUNCATION_v1.md`. Framework-only: no
`intLRC`, no import from the analytical small-`n` line.

Artefacts: `experiments/nN/order5_finallap_v1.{py,out}` · `order5_binding_v1.{py,out}` ·
`order5_lapstruct_v1.{py,out}` · `order5_growthgap_v1.{py,out}` ·
`experiments/n8/order5_certificate_S30_v3.out` (new)

---

## 0. Housekeeping

`LRC/Spec/FiveInt.lean` is **withdrawn** to `archive/lean_withdrawn/`, with
`README_FiveInt.md` recording why: it wired the analytical `intLRC_five` line into the cascade
framework, proved nothing new, and its integer-only import manufactured a "real-speeds gap" the
framework does not have. Nothing imported it; the tree builds unchanged.

**A defect in my own instrumentation, stated.** `order5_lapstruct_v1.py` and
`order5_finallap_v1.py` reset `sys.argv` before reading it, so a run invoked at `S = 26`
silently ran at `S = 18`. Every lap table below is therefore **`S = 18` data**, not `S = 26`.
The scripts are fixed; the tables are not re-run and are labelled honestly.

---

## 1. The certificate extends  `[PROVED]`

`experiments/n8/order5_certificate_v3.py 30`: 553,962 words tested, 9,798 realisable,
`sup R = 31/9` at the same word `(1,2),(2,1),(1,3),(3,1),(2,2),(1,6)` with the same margin
`τ = 132/4165`. **`PROVED for ratio ≤ 30`**, up from 26.

---

## 2. The certificate decomposes into two closed-form regimes  `[VERIFIED — S = 18]`

`R = (n·Q_f + 1)/u_{x_f}`, where `Q_f` is the **final setter's lap** and `u_{x_f}` its reading in
units of `d_min`. (My earlier lap table grouped by the word's *maximum* lap; that is the wrong
variable — a word can reach lap 10 and still finish at lap 2.)

The LP's **first-move constraint** reads `u_{x1}/n ∈ [Q₁ − 1/n, Q₁ + 1/n]`, i.e.

> `n·Q₁ − 1 ≤ u_{x1} ≤ n·Q₁ + 1`.

**Regime A — the final setter is the first setter.** Then that constraint applies to `u_{x_f}`
directly, and in **every** row of the `S = 18` table the LP minimum is *exactly* `n·Q₁ − 1` —
the first-move constraint is the binding one. So

> `R = (n·Q_f + 1)/(n·Q₁ − 1)`,  and  `R < n − 1`  iff  `Q_f < (n−1)·Q₁ − 1`.

| `Q_f` | 1 | 2 | 3 | 4 | 5 | **6** | 7 |
|---|---|---|---|---|---|---|---|
| best `R` | 1.500 | 2.750 | 1.778 | 2.333 | 2.889 | **3.444** | 2.571 |
| `u_{x_f}` | 4 | 4 | 9 | 9 | 9 | **9** | 14 |
| `Q₁` | 1 | 1 | 2 | 2 | 2 | **2** | 3 |

Every `u` is `5Q₁ − 1` on the nose. The maximum is `(Q₁,Q_f) = (2,6)`: `31/9`. Note `(2,7)` would
give `36/9 = 4` exactly — **it is realisability, and nothing else, that keeps `R` below 4.**

**Regime B — the final setter differs from the first.** The first-move constraint does not reach
`x_f`, and the bound comes from the chain. Best observed: `27/8 = 3.375` at `Q_f = 1`, word
`(1,1),(2,1),(3,1)`; it decays with `Q_f` (3.361, 2.667, 3.040, 2.979, 2.940, 2.842, 2.365,
2.875, 2.862). **`27/8 < 31/9`**, so Regime A is extremal.

---

## 3. What a proof for unbounded ratio now needs

Two statements, both finite in shape:

1. **Regime A:** bound the realisable `Q_f` for each `Q₁`. Observed: `Q₁=1 → Q_f ≤ 2`,
   `Q₁=2 → Q_f ≤ 6`, `Q₁=3 → Q_f ≤ 7`. The closed form then gives `R` immediately. The bound
   `Q_f ≤ (n−1)Q₁ − 2` would give `R ≤ (n²Q₁ − 2n + 1)/(nQ₁ − 1)`, which **tends to `n−1` from
   below as `Q₁ → ∞`** — so that bound alone is not uniform, and the cap on `Q_f` must be
   stronger than `(n−1)Q₁ − 2` for large `Q₁`. The data says it is: at `Q₁ = 3` the realisable
   `Q_f` is 7, far below `4·3 − 2 = 10`.
2. **Regime B:** show the chain constraints cap `R` at `27/8`.

**`move_growth` alone is not enough, and here is the margin** (`order5_growthgap_v1.out`).
`R < ∏ (nQ+1)/(nQ−1)` over the moves gives **4.106** on the extremal word whose true `R` is
`3.444`, and 4.125 on `(1,1),(2,1),(3,1),(1,2)` whose true `R` is `2.750`. The realisability
constraints supply the missing factor; a proof cannot be a product bound.

---

## 4. Why this is not about five — the payoff for `n = 8`

Nothing in §2 used `n = 5`. The first-move constraint is `u_{x1} ∈ [nQ₁ − 1, nQ₁ + 1]` at every
order, `R = (nQ_f + 1)/u_{x_f}` at every order, and the sufficient condition is `R < n − 1`. So
Regime A's closed form holds verbatim:

> `R = (n·Q_f + 1)/(n·Q₁ − 1)`,  below `n − 1` iff `Q_f < (n−1)·Q₁ − 1`.

At `n = 5` that reads `Q_f < 4Q₁ − 1`; at `n = 8`, `Q_f < 7Q₁ − 1`. The `n = 8` condition is
**weaker** — a longer run of laps is permitted before `R` reaches the threshold — which is the
quantitative form of the manuscript's "the local restrictions tighten as `n` grows" (§8.1) seen
from the cascade side rather than the zone side.

So the decomposition, the binding constraint and the two regimes are order-independent, and the
order-5 certificate is the smallest instance of a construction that applies at eight. What is
order-specific is only the arithmetic of which `(Q₁, Q_f)` pairs are realisable.

---

## 5. Grades

| claim | grade |
|---|---|
| order five holds for ratio `≤ 30` | `[PROVED — certificate re-run, output deposited]` |
| `R = (nQ_f+1)/u_{x_f}`; first-move constraint `u_{x1} ∈ [nQ₁−1, nQ₁+1]` | `[PROVED — read off the LP construction]` |
| Regime A: the LP minimum is exactly `nQ₁−1` in every row | `[VERIFIED — S = 18 table]` |
| Regime A closed form `R = (nQ_f+1)/(nQ₁−1)`, `< n−1` iff `Q_f < (n−1)Q₁−1` | `[PROVED — arithmetic]` |
| Regime B is capped at `27/8` | `[EMPIRICAL — S = 18; not proved]` |
| `move_growth` alone cannot prove `R < 4` | `[VERIFIED — 4.106 on the extremal word]` |
| the realisable `Q_f` cap for each `Q₁` | **not proved** — the remaining target |
| order five, unbounded ratio | **`[OPEN]`**, as the manuscript has it |

**Scope.** All tables are `S = 18` (lap bound `L = 14`), exact rational LP. The certificate
itself is `S ≤ 30`. Nothing here covers unbounded ratio.
