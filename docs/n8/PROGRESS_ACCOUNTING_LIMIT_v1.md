# Why progress accounting cannot close order 8

*Version 1, 2026-09-20. Companion to `CAP_DEFECT_v1.md`. This does not restate §8.2's `7/4`
identity, which the author already recorded on 2026-09-17. It reports what the cascade's measured
behaviour adds to it, and what that closes off.*

---

## 1. What §8.2 already says

`MANUSCRIPT_v17.md` §8.2: `n > 2k` is `k·(2/n) < 1`, the statement that `k` arcs of width `2/n`
cannot cover the circle; at `n = 8`, `k = 7` their total width is `7/4`, covering it 1.75 times over,
*"which is why this row reaches no order on the diagonal."* Recorded as a coincidence, with the
author's ruling that nothing else is built on it.

Everything below is downstream of that and is not a re-derivation of it.

## 2. The bound is not lossy — the cascade attains it

The `7/4` is the worst case of a **runner-additive** accounting: each of the seven runners is charged
separately for the laps it has passed. An additive argument is only capped at `7/4` if the seven
charges actually accumulate at the same rate. Measured on the two deepest cases on file:

| | 28-move case | second-lap case |
|---|---|---|
| moves | 28 | 23 |
| distinct runners setting | 7 of 7 | 7 of 7 |
| steps with exactly one runner in the way | 24 of 28 | 20 of 23 |
| max runners in the way at any step | 2 | 3 |
| gaps between one runner's consecutive settings | 3–12, mean 5.9 | 3–10, mean 5.9 |

**The cascade is a round-robin.** Every runner sets, roughly every seventh move, at a strictly
increasing lap, and at nearly every step exactly one runner blocks. So in `N` moves each runner
reaches lap `≈ N/7`, the cost of the run is `Σ_j log F(Q_j) ≈ (7/4)·log(N/7)`, and the additive
accounting is **achieved, not merely feared**. `[VERIFIED — exact rational arithmetic;
experiments/n8/cascade_interleaving_v1.{py,out}, cascade_setter_laps_v1.{py,out}]`

Two consequences:

- No constant-factor sharpening of `ManyDifferences` can reach `k = n − 1`. The exponent `2k/n` is
  the observed rate, not an artefact of the Bernoulli step.
- **The alternation lemmas do not escape it either.** `no_return_after_few_faster` needs `2g + 2 ≤ n`,
  so at `n = 8` it forbids a return across at most `g = 3` faster moves — and the measured minimum
  gap is exactly `3`. That lemma is already tight at the floor. Raising the *average* gap buys
  nothing, because seven runners at average gap `g` still give `N = 7 ·(laps each)`; the round-robin
  **is** the `7/4` structure, so constraining the rotation reproduces the same count.

## 3. What this closes off

Every engine in `LRC/Cascade/` measures **progress** — elapsed time, laps passed, the potential — and
progress is additive over runners. §8.2's identity caps runner-additive accounting at `7/4`, and §2
shows the cap is attained. So:

> **No runner-additive argument can close order 8, whatever it counts.**

This covers the potential, the zone-width count excised earlier (`AdvanceBudget`), the `F(Q_j)`
product of `nearest_reading_recurrence`, and any density or measure argument — all four are the same
count. That is why a density answer recurs whenever the obstruction is asked about: it is not a lazy
substitute for the order-8 question, it is the order-8 wall under another name. Naming it as the same
wall is useful; offering it as an answer is not.

## 4. What the obstruction actually is

At the arrival step nothing has run out. No budget is exhausted, no lap count is reached, no quantity
is driven to zero. The cascade stops because the seven readings `d_i·t mod 1` happen to land in
`[1/8, 7/8]` **simultaneously**. Termination is a joint condition on seven fractional parts; progress
accounting only ever sees the seven marginals, and the marginals are compatible with never stopping.

That is the gap, stated in the framework's own objects: there is no result in the tree about the
**joint** behaviour of the readings that is not either an equivalence to the target (`doors_agree`
and the rest — `CAP_DEFECT_v1.md` §3(a)) or conditioned on the ratio `S = d_max/d_min`
(`Certificate.lean` — §3(c)). The two non-additive assets that exist, `no_return_after_faster` and
`no_four_alternation`, constrain pairs, and §2 shows pair constraints reproduce the same count.

## 5. Where that leaves the question

The quantity that varies with depth is the denominator structure of the readings `u = d/d_min`
(`CAP_DEFECT_v1.md` §2: depth needs fine denominators; the `[1,22]` exhaustion could not see it
because capping the range caps the denominator). That is the rational-reading frontier §9's v13
correction already identifies as one problem with `R < 16`.

So the open statement is about **joint** rational structure at fine denominators, and it is not
reachable by counting how much each runner has advanced. Nothing here supplies it. What it removes is
the expectation that a sharper additive bound would.
