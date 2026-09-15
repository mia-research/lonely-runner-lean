# Targets after v8.2 — the proposals, thought through

Version 2, 2026-09-15 (v1 corrected in §1 and §3.1; §6 added: own proposals; order of work now §7). `MANUSCRIPT_v8_2.md` is frozen (v8.2). This document works through the three ideas and the four ranked
openings proposed after review, against the framework's proved statements and exact computations. Grades follow
`CLAIM_GRADES_v1.md`. Scripts: `experiments/n8/targets_premises_v1.py`, `targets_long_chains_v1.py`, `targets_length_vs_reading_v1.py` (outputs `.out`).

Notation: threshold `1/n`; `k` differences (the order-`n` diagonal is `k = n − 1`); nearest difference `a = d_min`;
`R_N = n·a·t_N`, the `N`-th step of the cascade in units of the bound; `F(Q) = (nQ + 1)/(nQ − 1)`;
`g(L) = F(1)·…·F(L)`; `S = d_max/d_min`.

---

## 1. What Existence reduces to  `[PROVED — one direction in Lean]`

**Existence for a runner ⟺ its `R_N` is bounded in `N`.** If `R_N ≤ U` for all `N`, the cascade is fixed at some step
(`ChainBounds.exists_fixed_of_capped`, in Lean). Conversely a fixed cascade is eventually constant, so its `R_N` is
bounded (immediate; not formalised). Since the steps strictly increase
until fixed, **a cascade that never stops has `R_N → ∞`**.

Two corrections to the proposal's wording:

- **`R` is set by the last step, not by a product of denominators.** A move resets the scale to `D′ = d/(8N + 1)`, so
  `R_final = d_min·(8N_last + 1)/d_last`. The product `∏ F(Q_j)` is an **upper bound** on `R_N`
  (`nearest_reading_recurrence`), not an identity; v7 list item 29 refuted the product formula (`1/81` against `7/9`).
- **The bound needed is per arrangement, and may depend on `S`.** A uniform constant (`R < 2n − 1`, say) is stronger than
  Existence. Any bound `R ≤ Φ(S)` suffices.

---

## 2. Idea 1 — collaborator exhaustion  `[AGREED, with a qualification]`

Appendix A.3 and A.2(iii) do rule out counting runners against clear intervals, or against "turns". The data make it
sharper. At order 5, four differences, a chain of **300 moves** has one runner setting **150 times**, up to lap 543
(`targets_long_chains_v1.out`).

**The qualification.** Counting runners *with their laps* is not dead; it is what proves every row of §8.2. A runner sets at
strictly increasing laps: after setting at lap `Q` it is clear until its lap-`Q + 1` zone. This held in every chain checked,
0 exceptions at `n = 5, 6, 8`. Section 3 shows how far that count reaches, and where it stops.

---

## 3. Idea 2 — a closed-form limit on the product, relative to `S`

### 3.1 It holds whenever `n > 2k`  `[DERIVED — not yet in Lean]`

Take any step `N`. Let `x` be a runner whose setting laps are `Q < Q′ < …`.

1. `R_N ≤ ∏_j F(Q_j)` (`nearest_reading_recurrence`).
2. A setter in the way at `t_j ≤ t_N` has lap `Q < x·t_N + 1/n = s_x·R_N/n + 1/n`. So `x`'s laps are distinct integers in
   `[1, L_x]`, with `L_x = ⌊s_x R_N/n + 1/n⌋ ≤ S·R_N`. Its factors therefore multiply to at most `g(L_x)` (`sorted_lap_prod`
   form).
3. `log F(r) ≤ 2/(nr − 1)`, and `Σ_{r=2}^{L} 2/(nr − 1) < (2/n)·H_{L−1} ≤ (2/n)(1 + ln L)`. So
   `g(L) ≤ e^{c_n}·L^{2/n}`, with `c_n = 2/(n − 1) + 2/n`.
4. Over the `k` runners: `R_N ≤ e^{k c_n}·(S·R_N)^{2k/n}`.

If `n > 2k`, then `R_N^{1 − 2k/n} ≤ e^{k c_n} S^{2k/n}`, so

    R_N ≤ ( e^{k c_n} · S^{2k/n} )^{n/(n − 2k)}   for every N,

and the cascade stops (§1). This is **Existence for every arrangement with `k` differences at every `n > 2k`**. It improves
§8.2's `n ≥ max(9, 2^(k−1))` for every `k ≥ 5`: for example `k = 5` at `n ≥ 11`, against 16.

**What is and is not in Lean.** The step factor bound (`nearest_reading_recurrence`) and the distinct-lap product
(`sorted_lap_prod`, which takes distinctness as a hypothesis) are in `Cascade`. **Per-runner lap distinctness is not a
standalone theorem**: it is proved only locally inside the order-4, `n ≥ 6` proof (`FourDifferences.lean`, a `have` limited
to seven moves), and checked in 0-exception computations. It follows from `inWay_until_opening`, but it has to be written.

**For the owner to rule.** This uses only the step factor, the setter's lap and per-runner lap distinctness. But it lands on **the same threshold, `n > 2k`, as the excised `AdvanceBudget`** (zone-width count, v7 list item
51). Whether this derivation is framework-native, or the same import reached another way, is your call. It is not formalised
and nothing is built on it.

### 3.2 It cannot reach the diagonal  `[DERIVED]`

At `k = n − 1` the exponent is `2(n − 1)/n ≥ 1` for every `n ≥ 2`, so step 4 gives nothing. **Lap bookkeeping alone cannot
prove Existence at any order on the diagonal.** The computations show which two losses are responsible, and they occur in
different regimes:

| order 5 | `R` | `∏ F(Q_j)` | lap-only bound `∏_x g(L_x)` | what is lost |
|---|---|---|---|---|
| resonant chain, 300 moves | 1.380 | 1.473 | 2,244 | **skipped laps**: runner d sets at 150 of its first 543 laps |
| near-bound chains, 5 moves | 3.087–3.190 | 5.042 | 5.042 | **handoff depth**: the true factor is `(nQ + 1)/(nQ − 1 + δ)`, not `F(Q)` |

(Earlier: `∏ F(Q_j) > 4` in 733 order-5 chains, max 5.04, while every true `R < 4`; status v6 §3.)

So the product route needs a lever that sees **skipped laps** (resonance) or **handoff depth** (near the bound). Proving
the diagonal needs both.

---

## 4. Idea 3 — the dead lattice as an escape valve  `[DOES NOT WORK AS STATED — three reasons]`

1. **The dead lattice is a statement about integer scales.** `dead_iff`, `dead_downward` and `exists_live` are over `ℕ`
   (dead means `8D | d`). The cascade's scales `d/(8N + 1)` were integers at 1,046 of 86,276 steps (order 8, all eight-subsets
   of `[1, 16]` plus 2,000 random sets to 200). "Divisors of dead steps are dead" relates integer scales by divisibility; the
   cascade's successive scales are not divisors of one another.
2. **The cascade moves away from the spread-live region.** Each move multiplies the scale by `s/(8N + 1) < 1`, so `D`
   strictly decreases from `d_min`. The live region is **large** `D`, `8D > spread`. After the first move it was reached at
   **0 of 86,276** steps.
3. **Live is not clear.** Liveness removes only exact slot-sharers, readings exactly on a multiple of 8 at that scale. Being
   in the way is the band `|s − 8N| < 1`, and live is not lonely: `(1, …, 7, 9)`, scale 2, runner at 2. `step_ceiling` at
   the cascade's own instant (`a = 1`) gives `D ≤ d_min`, which is automatic.

What survives is the first step: in integer arrangements the slot-sharer sets the first move (31,680 of 33,264; v7 list
item 28). The dead lattice describes where the cascade starts, not how deep it goes.

---

## 5. The ranked openings

### 5.1 Order 5, `R < 4`  `[AGREED as first target — premises corrected]`

- **Chains are not short.** 318 chains of 25+ moves, the longest 300, and in them `R ≤ 1.41`. A case analysis by the number
  of lap-1 steps is not finite.
- **"Every expensive step is cheap" does not close it by itself.** Lap-1-only gives `(3/2)³ = 27/8`. Three runners adding a
  lap-2 step each gives `27/8·(11/9)³ ≈ 6.16 > 4`. Lap bookkeeping at order 5 is §3.2's diagonal failure.
- **The regimes separate.** Large `R` comes from short near-bound chains (the loss is depth). Long chains come from
  resonance and keep `R` small (the loss is skipped laps). A proof could split on that: price depth when laps are small, and
  price skipped laps when readings are large.
- **Framing.** Five runners is already settled, and in Lean in this project. What order 5 would add is Existence of the
  cascade on the diagonal beyond order 4.

**First sub-target (recon, then lemma).** Over order-5 chains, measure per move (i) the depth `δ` against `F(Q)`, and (ii)
per runner, the laps skipped between settings. Then find which combination has a bound that forces `R < 4`. The candidate
lemma has the reviewer's shape: between two settings of one runner, the intervening moves' true factors multiply to at
least that runner's lap ratio `(Q′ − 1/n)/(Q + 1/n)` (`return_growth`), and a handoff at depth `δ` gives up `δ` of its
factor.

### 5.2 `R ≤ 2n − 1` as a stated conjecture  `[AGREED as a statement; EMPIRICAL]`

Largest `R` found: 3.44 (`n = 5`); 8.60, 9.04, 11.66, 10.66 (`n = 6–9`, annealing); 11.96 at `n = 8` (no `R ≥ 16` in one
round). A uniform cap implies Existence (§1).

**On the conditional form.** "Each runner sets at most `c` times" gives `R ≤ g(c)^k` directly. Its hypothesis fails at order 5
(150 settings), and a "no return after `g` faster moves" hypothesis fails the same way. A useful conditional has to be stated
in skipped laps or depth (§3.2), not in counts.

### 5.3 A two-return lemma  `[AGREED as the tool for 5.1]`

Returns are abundant in resonant chains (runner d returns about 150 times), so the lemma must **price** returns, not forbid
them. The pricing that `return_growth` already gives is the lap ratio. What is missing is the depth accounting of the
intervening handoffs (§5.1).

### 5.4 The residue rule as an exclusion engine  `[NOT FOR EXISTENCE]`

Proposition 6.7 decides loneliness at own AP instants, where `R` is an integer. Cascades almost never end there: the final
`R` was an integer in 1 of 3,740 order-5 chains with a move (0 of 817 at `n = 6`, 0 of 829 at `n = 8`). `R ∈ {1, 2, 3}` is
not the set to exclude; `R ∈ (3, 4)` is where order-5 cascades end (max ≈ 31/9). Formalising 6.7 is worth doing for the
manuscript, not for Existence.

### 5.5 What not to do  `[AGREED]`

Order 8 head-on; any route through zone-overlap ratios (Appendix A.2); the near-divisibility step of Appendix A.4 before a
return lemma exists.

---

## 6. Own proposals

### 6.1 First exceedance plus an exact finite certificate, for bounded spread  `[PROPOSED — mechanism checked on paper]`

**The mechanism.** Fix order 5 and a spread bound `S ≤ s₀`. Suppose some cascade reaches `R ≥ 4`, and let `N` be the first
step with `R_N ≥ 4`. Every step before `N` has `R < 4`, so:

- every setter's lap is `Q < s_x·4/5 + 1/5 ≤ 4s₀/5 + 1/5`, so `Q ≤ q₀ = ⌈4s₀/5 + 1/5⌉ − 1`;
- each runner sets at strictly increasing laps (§2), so it sets at most `q₀` times;
- the nearest runner (reading 1) has laps `< 1`, so it sets no move before `N`.

The prefix up to `N` is therefore a **word of bounded length with bounded laps**: at most `3·q₀ + 1` moves over
the three other runners. There are finitely many such words. For each, the chain's constraints are linear in the lap periods
once the word and laps are fixed (v7 list item 44), so the largest `R_N` the word allows is a linear program. **If the exact
optimum is below 4 for every word, no cascade with `S ≤ s₀` reaches `R = 4`.** That proves the order-5 cap on that range, and
Existence there with it.

**What makes it rigorous, and the two places it can go wrong.**

1. **Exact arithmetic with a certificate.** The earlier linear programs were floating-point (item 49). A proof needs a
   rational optimum and a dual certificate per word.
2. **Strict inequalities.** "In the way" is strict. With closed inequalities one order-5 word reached 4.125 at an
   all-boundary chain that BSM counts clear (status v6 §3), so boundary treatment matters. The handling:
   - per word, first decide whether the strict system is feasible, by maximising a common slack `τ` in exact arithmetic;
   - only if it is, use the closed optimum, because a nonempty open polyhedron is dense in its closure;
   - if `τ = 0`, the word is not realisable and is discarded.

**Size.** At `s₀ = 6`, `q₀ = 4`: laps are at most 4 and a prefix has at most 13 moves. Words are interleavings of three runners, each
setting at increasing laps, pruned by W1 and W2 and by prefix infeasibility. That is a small branch-and-bound, not a sweep.

**Why the split is right** (`targets_length_vs_reading_v1.out`, order 5, longest chain by largest reading):

| largest reading | longest chain found | its `R` |
|---|---|---|
| ≤ 3 | 0 (Theorem 4.8) | — |
| 3–6 | 5 | 2.89 |
| 6–10 | 7 | 2.12 |
| 10–20 | 8 | 1.93 |
| 20–50 | 10 | 1.48 |
| 50–200 | 30 | 1.32 |
| 200–1000 | 191 | 1.51 |

Long chains need large readings, and large readings keep `R` small, in these searches `[EMPIRICAL]`. The certificate handles
the regime where `R` is largest; what remains is the large-spread regime, where there is the most room below 4.

**What remains after it.** An analytic lemma for `S > s₀`: `R < 4` when some reading exceeds `s₀`. It must cover mixed
arrangements (one large reading, others small), which these searches did not isolate. The per-runner bound of §3.1 hints at
its shape: a runner with a large reading contributes at most about `R^{2/5}` over all its settings, because its laps start near
`s/5`. What is still missing is a bound on the small-reading runners that does not grow with `R`.

**For the owner.** This is a finite verification, but it runs over words of the cascade — setters, laps, handoffs — not over
arrangements, and it is exact. Whether it fits the framework is your call; it was not started.

### 6.2 Per-runner lap distinctness as a standalone Lean theorem  `[PROPOSED — infrastructure]`

"A runner sets at strictly increasing laps" is used by §3.1, §6.1 and any two-return lemma (5.3), and is currently only a
local `have`. Stating it once, for every `n` and every pair of setting moves, is independent of the T2 ruling.

---

## 7. Proposed order of work

| # | target | status | first action |
|---|---|---|---|
| T0 | Per-runner lap distinctness in Lean (6.2) | proposed | state and prove once, every `n` |
| T1a | Order 5, `R < 4` for `S ≤ s₀` by first exceedance plus exact word certificate (6.1) | proposed | **owner ruling on fit**; then exact strict-feasibility LP per word at `s₀ = 6` |
| T1b | Order 5, `R < 4` for `S > s₀` (6.1, 5.1, 5.3) | open | recon: per-move depth and per-runner skipped laps, mixed arrangements included |
| T2 | `n > 2k` Existence (3.1) | derived | **owner ruling** on nativeness; then Lean from `nearest_reading_recurrence`, per-runner lap distinctness and the log bound |
| T3 | State `R ≤ 2n − 1` (5.2) | empirical | record as a conjecture in the framework's quantity, graded, in the v8 list |
| — | Dead-lattice escape valve (4) | dropped | reasons in §4 |
| — | Residue rule for Existence (5.4) | dropped for this purpose | — |
