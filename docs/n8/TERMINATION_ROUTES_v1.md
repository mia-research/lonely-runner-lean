# Two work items for termination, and what the n=3 and n=4 proofs actually teach

2026-09-18. Artefacts: `experiments/n8/termination_routes_v1/`. Opened because termination is the
whole residue: `ExistenceAt8_cascade ↔ ExistenceAt8 ↔ CascadeCapped`, all proved equivalent in
`Spec/Target.lean`. Neither item below is a proof; both are directions with their obstruction named.

---

## 1. The finding that matters: the `2k < n` wall is a property of the method, not the problem

Every counting route dies at `2k < n` — potential `Ψ`, move counting, the union bound, withdrawn
Prop 6.11, and now the Long-Return circle, whose threshold `c_* > 1/4 − 3/(4k)` is non-positive
exactly when `k ≤ 3` (`LONG_RETURN_CIRCLE_v1` §4).

**But the two termination proofs the framework actually has both live outside that regime.**

| | `n` | `k` | `2k < n`? | proved? |
|---|---|---|---|---|
| `TerminationThree` | 3 | 2 | `4 < 3` **no** | **yes** |
| `TerminationFour` | 4 | 3 | `6 < 4` **no** | **yes** |

So `2k < n` is where *counting alone* suffices. It is not a boundary on what can be proved. Both
existing proofs are structural — window plus return lemma plus pigeonhole — not counting. This is
the strongest reason to expect a non-counting route at `n = 8` to be possible at all.

## 2. How the small-order proofs work, and which ingredient breaks at 8

From `SmallOrders.lean`. Three ingredients:

- **(a) a window invariant** — the nearest runner `a` stays inside its **first** clear window,
  `τ = a·t ∈ [1/n, (n−1)/n]`. At `n = 4` the proof bounds `τ < 5/12`, then `25/36`, then `3/4`.
- **(b) the return lemma** — `Q(n−2) < 2P + 1`, bounding when a setter may set again. At `n = 4`
  this is `Q ≤ P`.
- **(c) a pigeonhole over setters** — three at `n = 4`; a runner is never in the way at its own
  opening, so consecutive setters differ, and (b) closes the cycle.

**(b) gets stronger at `n = 8`**: `Q ≤ (2P+1)/6` rather than `Q ≤ P`. **The window in (a) gets
wider**: `[1/8, 7/8]` is 3/4 of the period against 1/2 at `n = 4`. Both favourable.

**(a) is what fails.** Measured on the two arrangements the manuscript already names:

| case | moves | max `τ = a·t` | window ends | distinct setters | repeats |
|---|---|---|---|---|---|
| §6.7 climb, subject 393 | 28 | **1.283** | 0.875 | 7 of 7 | 21 |
| §6.9 row, subject 1 | 23 | **1.289** | 0.875 | 7 of 7 | 16 |

The nearest runner completes more than one lap, so "stays in its first window" is false at `n = 8`.
This is `RETURN_CORRECTION_v3`'s result — *the cap is crossed, not approached* — reached from the
other direction.

**Why the repair is circular, and this is the obstruction to name.** The nearest runner re-enters a
clear window every lap, so the natural weakening of (a) is *"the nearest is in some clear window at
the terminal instant"*. But the force of (a) came from the window being an interval that cannot be
left; once laps are allowed, one must bound the number of laps — which is `CascadeCapped`. So the
`n = 4` mechanism, transported as-is, reduces to the thing it was meant to prove.

**A search warning, from two failures in one sitting.** Random sampling does **not** find these
cases. Difference sets drawn from `[1,40]` gave median **0** moves and 4,000/4,000 keeping the
invariant; a spread-biased sample of 60,000 gave **0/60,000** violations. The invariant looks
universal under sampling and is false. The named cases came from §6.7's exhaustive sweep. Any future
test of a window or cap invariant must be run against the named arrangements, not against a sampler.

## 3. Work item A — the dichotomy  `[to try]`

Suggested by the owner's observation that moving off an isolation time loses isolation. That premise
is **true, and true exactly for the extremal case**. Lonely set over one period:

| `ds` | lonely set |
|---|---|
| `{1,2,3,4,5,6,7}` (the AP) | **4 isolated points**, longest run 1 |
| every other set tested | intervals, 0.007–0.023 wide |

So the structure is a dichotomy: **tight** sets, whose lonely set is a finite set of points achieving
exactly `1/8`, and **loose** sets, whose lonely set has interior.

Tight census over primitive 7-subsets, exact arithmetic:

| bound | tight | loose | below `1/8` |
|---|---|---|---|
| `[1,10]` | 1 | 119 | 0 |
| `[1,12]` | 2 | 790 | 0 |
| `[1,14]` | **3** | 3,428 | 0 |

The three: `{1,2,3,4,5,6,7}`, `{1,2,3,4,5,7,12}`, `{1,4,5,6,7,11,13}` — the three tight instances the
project already had on record, recovered independently.

**The programme.** (i) classify the tight family and show the list complete over the reals, not only
small integers; (ii) name the instant in each — the AP gives `1/8, 3/8, 5/8, 7/8`; (iii) show every
loose configuration has slack, hence a lonely interval.

> **SUPERSEDED 2026-09-18 — step (ii) is done, and the framing of this item is wrong.**
> `Flanks.lonely_at_inv_of_not_dvd` **proves** that `t = 1/8` is lonely whenever no difference is
> divisible by 8. **All three tight configurations satisfy that**, so Existence at each is now a
> theorem, not a programme item. And the premise that the tight family is where the difficulty lies
> is **false**: they are settled at `k = 0` by the simplest rule there is, while the naming problem
> sits in the generic middle — `DOOR4_v1` §3, §7 and `RULE_TABLE_v1` §10c, §11c.

**Honest assessment.** (iii) is the whole difficulty and is not easier than LRC(8); (i) needs
completeness over ℝ. What makes it worth trying is §1: it is a structural route, and structural
routes are the only ones that have ever worked here.

**A methodological warning from building this section.** The first tight census reported *"tight
3431, loose 0"* — every set tight. It was searching flank openings only, where the flank runner sits
at exactly `1/8` by construction, forcing the minimum to `≤ 1/8`. The statistic was **forced**, not
measured. The corrected census carries a sanity check (`{1..7}` must come out exactly `1/8`) and any
successor must too.

## 4. Work item B — transport the return lemma without the window  `[to try]`

(b) is **stronger** at `n = 8` and does not depend on (a). At `n = 8` it reads `6Q < 2P + 1`, so a
setter at lap `P` cannot return at a lap above `(2P+1)/6`. The measured cascades use all 7 setters
with 16–21 repeats, so returns are the dominant event and the lemma applies to most steps.

**The question**: can (b) plus the setter pigeonhole bound the number of moves without (a)? That
would be the `n = 4` proof with its broken ingredient removed rather than repaired.

**Known obstruction**: `return_lemma` requires `hret`, that the returning runner is in the way **at
the next setter's opening** — so it governs immediate returns, `g = 0`, not returns after
intervening moves (`LONG_RETURN_LEMMA_v1` §5, row 4). A version for `g ≥ 1` is not in the tree. That
generalisation is the concrete first step, and it is a statement about the exhibited rule, so it is
in frame.
