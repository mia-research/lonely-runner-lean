# The cascade as a map on the residue vector — non-termination is a cycle

*2026-09-22. Artefacts `experiments/nN/dilation_v1.py`, `residue_dynamics_v1.py`,
`residue_dynamics_v2.py`. Order 8. **Native**: no complement is formed, no set is shown empty,
and no firing rate is offered as a result.*

---

## 1. Why the dilation machinery runs the wrong way

`λ < 9/7`, `λ < 17/15` for `M ≥ 2`, and the self-slowing all say steps get **smaller**. Smaller
steps mean more of them, which makes an infinite run easier. §6.14 records this: the bound gives a
*lower* bound on the move count and *"no matching upper bound, because `λ → 1` as `M → ∞`"*. Read as
machinery against divergence it is the shape of an answer; the arithmetic runs the other way.

## 2. The move law, additively

With `R = d_min/D`, a blocker at lap `M` has next scale `d_i/(8M+1)`, so

> `R_{j+1} = max over blockers i of (8 M_i + 1)/s_i`,  `M_i` the unique lap with `|s_i R_j − 8M_i| < 1`.

`[VERIFIED — 400 profiles; every visited R of the form (8m+1)/s, 0 exceptions.]` From
`8M+1 ∈ (sR, sR+2)`: **every step is `< 2/s`** `[PROVED]`, hence `< 2`. Measured max step `0.3214`.

## 3. The step is a function of the residues alone

Write `r_i = s_i·R mod 8`. Runner `i` blocks iff `r_i ∈ [0,1) ∪ (7,8)`, with step `(1−r_i)/s_i` or
`(9−r_i)/s_i`. `R` itself never appears, and `r_i' = r_i + s_i·step (mod 8)`.

> **The residue vector evolves under a map determined entirely by itself.**

`[VERIFIED — 399 real cascade steps against the direct move law, 0 mismatches. Not vacuous.]`

## 4. Consequence: non-termination is a cycle

For rational readings, `R` stays in `(1/L)ℤ` with `L = lcm` of denominators, so each `r_i` ranges
over a finite set and the residue vector lives in a finite state space. A deterministic map on a
finite set is eventually periodic. Hence

> **The cascade either terminates or enters a cycle.** Non-termination is not an unstructured run to
> infinity; it is a finite repeating state.

**Cycle rigidity.** In a cycle the residues return, so `s_i·Δ ≡ 0 (mod 8)` for every `i`, where `Δ`
is the `R`-increase per period. With `s_1 = 1` this forces `Δ ∈ 8ℤ`, so **`Δ ≥ 8`**: a cycle crosses
at least one whole band. Since every step is `< 2` and the forbidden window `(8k+7, 8k+9)` has width
`2`, that window **cannot be jumped — only landed in**. `[PROVED — elementary]`

`[EMPIRICAL]` 8,000 profiles (integer and rational readings): 8,000 terminate, **0 cycles**.

## 5. What is NOT established, and a vacuous test recorded as such

Two further claims were formulated and **not tested**, because the samples never entered the regime
where they apply:

* *C1* — when `d_min` blocks with `r_1 ∈ (7,8)`, its step `9−r_1 ∈ (1,2)` beats any other blocker's
  `< 2/s ≤ 1`, so `d_min` wins and `R` lands exactly on `8k+9`.
* *C2* — at an integer `R ≡ 1 (mod 8)` the residues are `r_i = s_i mod 8`, identical to the state at
  `R₀ = 1`; revisiting it repeats the orbit, hence a cycle.

`d_min` blocked **0 times in 5,051 observed cascade steps** — the orbit never left band 0, where
`r_1 = R ∈ [1,7]`. So "0 counterexamples" for C1 and C2 is a **forced statistic**, not evidence.
Both are `[UNTESTED]`.

## 6. An unresolved conflict with the manuscript

No orbit in 8,000 profiles reached `R > 9`; in a separate run, none of 300,000 profiles with
readings in `[2,400]` left band 0. The manuscript's §11.2 reports `max R = 11.965675`, in band 1,
from 12.2 million profile evaluations, and also records that *no random cascade* reaches band 1.

These may be consistent — 8,000 against 12.2 million — or the implementation here may differ from
the manuscript's cascade. **Nothing built on band-crossing should be trusted until a manuscript deep
case is reproduced by this code.** That is the next check, and it comes before any further reasoning
about C1, C2 or cycles.

## 7. Status

No theorem. What is established: the additive move law, the step bound, the residue-map reduction,
and the cycle rigidity `Δ ≥ 8`. What that buys is a **restatement of the open question as a finite
object**: not "can `R` run to infinity", but

> **can a blocked cycle exist?**

with the constraint that any such cycle advances `R` by a multiple of 8 per period and must land
inside a width-2 window to do it.
