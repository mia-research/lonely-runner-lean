# Why the last mile resists: §7.4 is false

2026-09-14. Stepping back from the individual routes. Scripts:
`experiments/nN/both_families_hunt_v1.py`. **The manuscript has not been touched.**

---

## 1. The finding

> **Speeds `(1, 31, 75, 97, 128, 160, 176, 225)`** — eight distinct positive integers,
> gcd 1, no runner pinned. **The runner at speed 1 clears neither family of v7 §7.4.**

| | |
|---|---|
| its differences | `30, 74, 96, 127, 159, 175, 224`, `d_min = 30` from its neighbour `31` |
| `S = d_max/d_min` | `224/30 = 7.467` — just above `7`, so Thm 4.8 does not apply |
| **family A** (own-difference openings) | 22 candidates examined, **0 clear** |
| **family B** (cascade lattices) | 840 pairs `D ≤ 210`, `p ∈ {1,3,5,7}`, **0 clear** |
| the first window `[1/240, 7/240]` | 44 boundary points and 200,001 exact interior points, **0 lonely** |

**LRC(8) is untouched.** The runner *is* lonely, at `t = 9/40`, with distances
`1/4, 7/20, 2/5, 17/40, 9/40, 3/8, 2/5` — every one at or above `1/8`. That instant is
`u = 27/4`, **lap 6**. The other seven runners clear both families comfortably.

The cascade's ceiling is not the problem and cannot be lifted: for the difference `m` itself
the test gives `D ≤ mp ≤ 7m`, so **no `D > 7·d_min` can ever clear**, whatever bound is
nominated. All 210 are checked.

`[PROVED — exact, exhibited, checkable in one line]`

---

## 2. What it means, and why every route has died

**§7.4 is false.** Not hard — false. Every attempt to prove it was bound to fail, and the
succession of dead branches is what that looks like from the inside.

**The manuscript predicted this.** §1.3:

> This is **stronger than the conjecture requires.** LRC(8) asks only that a runner be lonely
> at some time, which in this coordinate is `u ∈ [k + 1/8, k + 7/8]` for *some* lap `k`. The
> first-window form is kept deliberately… **We record it as a choice, not as the target.**

The target and the claim came apart. §1.3 says the first-window form is not the target; §7.4
makes it the claim; and §7.3 proves §7.4 ⟹ LRC(8), so proving §7.4 would have meant proving
something **strictly stronger than an open analytic problem**. The skating was not a failure
of nerve. It was five routes bouncing off a false statement.

---

## 3. The structure, which is now clear and is worth keeping

**An exact dichotomy.** Normalise `d_min = 1` and let `S = d_max/d_min`.

- `S ≤ 7` → Theorem 4.8 settles the runner outright. `[PROVED]`
- `S > 7` → the top difference alone supplies `≥ 6` candidates, and the count grows like
  `3S/4` without bound.

**Family A's failures live in a narrow band just above `S = 7`.** Exhaustively, over all
54,264 difference multisets with `d_min = 1` and entries `≤ 16`, family A **never** fails;
family B fails 1,810 times. The counterexample sits at `S = 7.467`, and the earlier one at
`S = 7.667`. Random sampling finds none in 200,000 draws inside that band — they are
constructible, not typical.

**The two families cover opposite ends of one parameter.** Family B's reach is `7·d_min`,
so it dies when `d_min` is small. Family A's candidate count is `≈ 3S/4` per difference, so
it thrives when the spread is large. That is why the union works almost everywhere — and why
the exception has to be manufactured at `S` just above `7` with `d_min` large.

---

## 4. The three routes in the shared exchange, assessed

| route | verdict |
|---|---|
| **`2σ` participation count** | **A genuine negative result, verified.** `B_{2k+1} ⊂ C_k` for every `k`, so one reading participates in **every** clear interval of `σ`. Now in v7 §6.3 |
| **4.8/4.9 ⟹ 4.7 survival** | Right in conclusion — global reference machinery cannot finish a per-runner theorem — though I have not verified its irrational construction |
| **Prop 2.1 as the finishing mechanism** | **A restatement, as the exchange itself said.** And its concluding proposal — bound how many candidates one difference can block — has no bound to find: measured, a single difference blocks `0.17–0.35` of the candidates, near a quarter regardless of its value. Five such is `≈ 1.25 > 1`, so counting cannot decide it either |

The exchange's instinct was right and its instrument was not. **Pushing at §7.4 with better
tools was never going to work, because §7.4 is false.**

---

## 5. Where the moment actually was, and what that suggests

`t = 9/40 = 9/(8·5)`. So `a = 9`, `D = 5`.

- `a = 9` is `≡ 1 (mod 8)` but **not in `{1,3,5,7}`** — family B excludes it.
- `D = 5` is **not one of the runner's differences** — family A excludes it.
- `D = 5` is well inside the cascade's range `D ≤ 210`.

**Both restrictions are doing the excluding, and neither is load-bearing.** A family of the
shape `t = a/(8D)` with `a ≡ 1 (mod 8)` and `D` a free positive integer clears this runner at
`(D, a) = (5, 9)`.

That is a direction, not a repair. Coded naively it reaches `0.9979` where `A ∪ B` reaches
`1.0000`, so it is not a superset of what the framework already has, and the right statement
has to be designed rather than guessed. **The design is the owner's call** and the manuscript
stays frozen until then.

---

## 6. What is untouched

LRC(8). Soundness (§7.3) — a returned instant is still correct. §§1–6 and §9 in full. The
negative results. The entire Lean development: `Construction8` digest
`578022e0296ce565ec601655747d1e5cdc614a9efa2cced6540162e698f43b9d`, and `ConstructionN`,
which states part 7 nowhere.

What changes is the target. §7.4 as written is not it, and §1.3 already said so.
