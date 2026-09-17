# Is the existence question the right question — derived, not cited

2026-09-18. Artefacts: `experiments/n8/frame_check_v1/`. Written because the previous answer
pointed at `NAMING_VS_EXISTENCE_v1` and `Target.lean`, which is citation, not reasoning. This
derives the target from the conjecture and tests the two steps that could be wrong.

---

## 1. From the conjecture to the difference form

**LRC at 8.** Eight runners, distinct constant speeds `v_1 … v_8`, circle of circumference 1. For
**each** runner `k` there is a time `t` with `‖(v_i − v_k)·t‖ ≥ 1/8` for every `i ≠ k`.

Pass to runner `k`'s frame. The differences `δ_i = v_i − v_k` (`i ≠ k`) are seven in number and all
nonzero, by distinctness. Then:

- **Signs drop.** `circDist` is even, so `‖δ·t‖ = ‖|δ|·t‖`. Replace each `δ` by `|δ|`: all positive.
- **Duplicates collapse.** Two runners can have `|δ_i| = |δ_j|` — one ahead, one behind by the same
  amount. They impose the *identical* constraint, so a `Finset` is the right container.

giving exactly: `∃ t, ∀ d ∈ ds, ‖d·t‖ ≥ 1/8`, with `ds` a finite set of positive reals, `card ≤ 7`.

**`card ≤ 7` is required, not slack.** Over 3,200 (configuration, runner) pairs the difference-set
size was **7 in 2,793 cases, 6 in 393, 5 in 14**. A target written with `card = 7` would miss real
configurations.

**The two forms compute the same number.** Evaluating the conjecture directly against the formal
statement on the same 3,200 pairs: **0 disagreements** (`frame.out`).

## 2. Why `∀ ds`, and why it is safe

As `k` ranges over the eight runners we get eight different difference sets, so `∀ ds` covers every
runner of every configuration. It also covers sets that arise from no 8-runner configuration — which
is safe, because covering more implies the conjecture, and cannot make a true statement false.

Could it be *too* strong — false while LRC(8) is true? A set with `card = 7` always arises, from
`v = (0, d_1, …, d_7)`. A set with `card = k < 7` is the difference set of a `k+1`-runner
configuration, and LRC at `k+1` gives `≥ 1/(k+1) ≥ 1/8`. Those orders are settled. So the extra
cases carry no new risk.

**This is also why speed-rank is a convention.** Since the statement quantifies over `ds`, no fact
about which runner is slowest can add anything to it.

## 3. The details that are load-bearing

- **`0 < s`.** At `t = 0` every runner is together, so `t = 0` is never lonely: the restriction
  excludes nothing. And loneliness is even in `t`, so `∃ s ≠ 0` and `∃ s > 0` agree.
- **`≥ 1/8`, closed.** The extremal configurations achieve *exactly* `1/8`. With a strict `>` the
  statement would be **false**. `Lonely` uses `1/n ≤ circDist` and `inWay` uses `circDist < 1/n` —
  exact complements, which is what makes "no runner in the way" and "lonely" the *same* statement
  rather than merely related ones.
- **Real speeds.** `ds : Finset ℝ` is stronger than the integer form and true iff it is, so there is
  no risk of aiming at something false.
- **The cascade's start `1/(8m)`, `m = min ds`, is forced.** For `t < 1/(8m)`, `m·t < 1/8`, so the
  slowest runner is in the way — no lonely instant can lie below it. Measured: **0 lonely instants
  below the bound** across 3,000 difference sets, and `circDist(m · 1/(8m)) = 0.125` exactly in
  every one — the boundary. So the bound is the earliest candidate, not an arbitrary choice.

## 4. The one step that could have made the target wrong

`ExistenceAt8 ↔ ExistenceAt8_cascade` holds only if **`move` never steps over a lonely instant**. If
it could overshoot, the cascade form would be *strictly stronger* than existence, and the whole
programme would be aimed at the wrong target.

**Why it cannot.** `move` takes the **maximum**, over the runners blocking at `t`, of their next
opening. If `d` blocks at `t` it keeps blocking throughout `[t, nextOpening(d,t))`, so no instant
there is lonely. The furthest blocker therefore blocks the entire interval up to the maximum, and
the maximum is the largest provably-safe jump.

**Tested** (`overshoot.out`): 1,500 difference sets, all arriving, **1,390 move steps, 0 that skipped
a lonely instant.** Control — the same scan applied to jumps deliberately four times too far catches
**1,142**, so the scan is not blind.

## 5. Conclusion

The question is correctly posed. `ExistenceAt8` is the conjecture at `n = 8`, transported by
evenness and duplicate-collapse and nothing else; `ExistenceAt8_cascade` is the same statement about
the exhibited rule, and the equivalence rests on a non-overshoot property that holds for a stated
reason and survives a test with a firing control.

**What is open is unchanged**: that the cascade terminates. Neither this check nor the terminal-time
memo (`V9_6_REVISION_LIST_v1` §1) moves it.
