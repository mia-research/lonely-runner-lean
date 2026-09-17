# Is `g ≤ 3` tight in `no_return_after_few_faster`? Yes, and it does not matter

2026-09-17. Answers the owner's question directly. **The `2g+2 ≤ n` hypothesis is tight as stated**, and
separately, **raising `g` would buy nothing**, because a different hypothesis of the same theorem is what
actually limits its reach. `EXISTENCE_MAP_v1.md` Link 5 direction 1 is therefore **closed** — by
measurement, not by opinion.

Artefacts: `experiments/n8/no_return_tightness_v1.py` / `.out`, `no_return_applicability_v1.py` / `.out`,
`no_return_headroom_v1.py` / `.out`. All exact rational arithmetic.

---

## 1. Where the hypothesis enters  `[read from the proof]`

`no_return_after_few_faster` (`LRC/Cascade/FourDifferences.lean:113`) contradicts a return by bounding
the instant from both sides. With `h = 1/n`, the runner `x` having set at its lap-`P` opening:

- **below** — `return_growth` (`SmallOrders.lean:487`): a return needs `t_m > ((P+1−h)/(P+h))·t_0`;
- **above** — `hbound` in the theorem: `t_m ≤ F^m·t_0` with `F = ((P+1)+h)/((P+1)−h)`, using
  `hlap : ∀ j < m, P+1 ≤ Q j` and `lap_factor_antitone`;
- **the clash** — `factor_pow_le_return` (`FourDifferences.lean:73`), and `2g+2 ≤ n` is used **only
  here**: `F^g ≤ (P+1−h)/(P+h)`.

So the theorem's real requirement is the sharp inequality `F^g ≤ (P+1−h)/(P+h)`, and `2g+2 ≤ n` is
whatever `factor_pow_le_return` manages to prove of it. That proof goes through Bernoulli —
`(1+y)^g ≤ 1/(1−gy)` with `y = 2h/(P+1−h)` — then demands `P+h ≤ (P+1−h)(1−gy)`, which reduces exactly
to `2h(g+1) ≤ 1`, i.e. `2g+2 ≤ n`.

## 2. Tightness  `[VERIFIED — exact]`

Largest `g` satisfying the sharp inequality at `n = 8`, against what the shipped proof delivers:

| `P` | 0 | 1 | 2 | 3 | 4 | … | 10⁴ |
|---|---|---|---|---|---|---|---|
| sharp | **7** | **4** | 3 | 3 | 3 | … | 3 |
| shipped proof | 3 | 3 | 3 | 3 | 3 | … | 3 |

> **As a `P`-uniform hypothesis — which is what the theorem states, since `P` is universally quantified
> under `0 ≤ P` — `2g+2 ≤ n` is TIGHT.** The sharp limit is exactly 3 at `n = 8`, approached as
> `P → ∞`: the condition tends to `g ≤ (1−2h)/(2h) = n/2 − 1`.

> **Per `P` it is NOT tight.** At `P = 0` the sharp bound allows `g ≤ 7`, at `P = 1` it allows `g ≤ 4`.
> The Bernoulli step is where that is lost — at `P = 0` its own hypothesis `g·y ≤ 1` already caps `g` at
> 3 on its own.

So a `P`-dependent restatement is available and would be a genuine strengthening of the lemma.

## 3. Why it would buy nothing  `[VERIFIED — 40,000 arrangements]`

The theorem's other hypothesis is `hlap`: **every** intervening setter at lap `≥ P+1`. Measured on the
stratum that actually moves (ratio in `(7, 8]`; at ratio `≤ 7` the subject is lonely at the opening
instant and there are no returns at all):

| | |
|---|---|
| arrangements sampled | 40,000 |
| returns observed | 2,885 |
| **returns satisfying `hlap`** | **7 — 0.2%** |
| of those, gap `≤ 3` (shipped theorem's range) | **0** |
| extra returns a sharp `P`-dependent `g` would exclude | **0** |

**99.8% of returns are outside this theorem at any `g`**, because some intervening setter sits at a lap
`≤ P`. Raising `g` from 3 to 7 is therefore not the binding constraint; `hlap` is.

**Consistency check, which the theorem passes:** of 2,885 returns none has `hlap` and gap `≤ 3`. The
theorem holds on every cascade seen, including both named extremal climbs.

## 4. And there is no headroom in the growth estimate either  `[VERIFIED]`

The strongest form this proof structure can take replaces the worst case `F^m` by the **exact** per-step
product `∏_j (Q_j + h)/(Q_j − h)`. For all 7 `hlap` returns:

| margin = exact growth ÷ return threshold | min | median | max | within 5% of the threshold |
|---|---|---|---|---|
| | 1.1695 | 1.2194 | 1.3255 | **0 of 7** |

Every margin exceeds 1 by 17–33%. So the exact-growth form **contradicts none of them**: for these
returns the conclusion is simply false, not merely unproven. No sharpening of the growth estimate —
`P`-dependent `g`, exact laps, or both — turns this lemma into a general bound on returns.

## 5. Verdict, and what it redirects to

> `no_return_after_few_faster` is tight as stated, cannot be usefully strengthened along `g`, and reaches
> 0.2% of returns. It is a correct lemma with a small domain, not a partial tool awaiting sharpening.

**Scope of the negative** (stated narrowly on purpose): `n = 8`, integer difference sets with entries
`≤ 300`, ratio in `(7, 8]`, 2,885 returns of which 7 meet `hlap`. It says this *proof structure* — growth
bounded above, return threshold below — cannot exclude the observed returns. It does not say returns
cannot be bounded by some other argument.

**Where the returns actually live.** The 99.8% that fail `hlap` have an intervening setter at lap `≤ P`
— a *slower* move in between. That is the object a general return bound would have to handle, and
nothing in the current machinery addresses it. `no_four_alternation` is the other return restriction and
is worth the same treatment before anything is invented: read it, then measure its reach.
