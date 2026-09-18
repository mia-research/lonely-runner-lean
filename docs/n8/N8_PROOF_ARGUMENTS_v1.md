# The n = 8 Framework — How the Main Results Are Proved

**T. Palelei.** Documentation file, v1, 2026-09-18. Companion to `N8_PROOF_v9_3_DOC_v1.md`, which
states the results; this file gives the arguments.

**Scope.** Every argument below is for a `[PROVED]` result and is machine-checked in Lean under
`[propext, Classical.choice, Quot.sound]`. **Existence at order 8 is not among them** — §9 says
precisely what an argument for it would have to do, and why the reduction is not a weakening.

**Fidelity.** These are the arguments as the manuscript and the Lean source give them, compressed.
Where a step is arithmetic the arithmetic is shown; where a step is a Lean tactic the shape of the
induction is given, not the tactic script. Declaration names are the machine-checked statements.

---

## 1. The clearing test (Proposition 2.1, `coord_iff`)

**Claim.** For `t = a/q` and a relative speed `d`, all naturals: `‖d·a/q‖ ≥ 1/n` **iff**
`q ≤ n·z` and `n·z + q ≤ n·q`, where `z = (d·a) mod q`.

**Argument.** `d·a/q` differs from `z/q` by an integer, so `‖d·a/q‖ = ‖z/q‖ = min(z/q, 1 − z/q)`
with `0 ≤ z < q`. Then `z/q ≥ 1/n ⟺ n·z ≥ q`, and `1 − z/q ≥ 1/n ⟺ n·q − n·z ≥ q ⟺ n·z + q ≤ n·q`.

**Why it is stated this way.** Both conditions live in `ℕ`, so the threshold case is inside the
statement rather than handled by a separate real comparison. This is what makes the census
decidable: each family closes by `decide`.

---

## 2. The band identity (`inWay_at_scale_iff`) — the real-valued form

**Claim.** At the instant `1/(8D)`, a runner of reading `s = d/D` is in the way **iff** `s` is
within 1 of a multiple of 8. Every real `D > 0`.

**Argument.** The runner's position is `d/(8D) = s/8` laps. Its circle distance is `‖s/8‖`, which is
below `1/8` exactly when `s/8` is within `1/8` of an integer `N`, that is when `|s − 8N| < 1`.

**Why it matters.** This is the whole clearing test with no rationality anywhere in it. The integer
form of §1 is its representation when readings happen to be rational, which is why irrational speeds
need no separate treatment and `√2` is never approximated.

**The companion.** `nextOpening_at_scale`: the runner's next opening is the first spine point of the
progression of gap `d/(8N + 1)`. Together these two make the cascade a recursion on the scale:

    D_0 = d_min,   D_{j+1} = D_j · min{ s/(8N + 1) : |s − 8N| < 1 }.

**A consequence read straight off the factor.** Every factor `s/(8N + 1)` is below 1, since
`|s − 8N| < 1` gives `s < 8N + 1`. So the scales **decrease** from `d_min` and never enter
`d_min < D ≤ 7·d_min`. That single observation is what makes the cascade disjoint from the
"enlarged tier" of earlier sketches, which stepped upward under a ceiling.

---

## 3. A step is one dilation

**Claim.** Passing from `D` to `D′` multiplies every reading by the same factor
`λ = D/D′ = (8N + 1)/s_x > 1`, where `x` is the setter.

**Argument.** Readings are `d_j/D`; replacing `D` by `D′` scales all of them by `D/D′`. The setter's
new reading is `s_x · (8N + 1)/s_x = 8N + 1` exactly.

**Two corollaries used repeatedly.**

- The setter lands on **slot `≡ 1`, deviation 0**, and an odd reading `8N + 1` is never within 1 of a
  multiple of 8 at odd `r`, so the setter is clear at every spine instant of the new scale. The
  runner that caused the move is the one guaranteed clear after it.
- Every other reading moves by `(λ − 1)·s_y = g·(d_y/d_x)`, where `g = 8N + 1 − s_x ∈ (0, 2)` is how
  far the setter sat below `8N + 1`. The ratios `d_y/d_x` are fixed by the speeds, so the whole step
  is determined — this is what "no search" means concretely.

---

## 4. Construction (Theorem 6.2)

Four parts. Let `T` be a fixed point of the move reached from the bound.

### (a) `T` is lonely — `lonely_of_fixed`

The move leaves `t` fixed exactly when no runner is in the way at `t`. "No runner in the way" is the
definition of lonely. The content is in the definition of `move`, which returns `t` unchanged
precisely on the empty in-the-way set.

### (b) No positive instant before `T` is lonely — `first_isolation_of_fixed`

Two facts compose:

- **The bound is a floor** (`bound_le_of_lonely`). Below `1/(8m)` the nearest runner at disparity
  `m` has not yet left the subject's zone: `m·t < 1/8`, so it is in the way. Proved by
  contradiction from `before_floor`.
- **No move passes a lonely instant** (`move_le_of_lonely`). If the subject is lonely at `s` and the
  cascade is at `t ≤ s`, every runner in the way at `t` is clear at `s`, so its next opening after
  `t` is at or before `s`. The move takes the largest of those, which is therefore at most `s`.

By induction every iterate is at most any lonely `s`, and the iterates start at the bound. So a
fixed point is a lower bound for every positive lonely instant, and by (a) it is one.

### (c) `T` ends the run of lap-completion zones from the bound — `first_isolation_as_zone_run`

Runner `d` completes relative lap `N` at `N/d` and is in the way on the open zone
`((N − 1/8)/d, (N + 1/8)/d)`. A **run** from `b` is a list of such zones, each containing the end of
the one before, beginning with one containing `b`; its end is the right end of the last zone.

The move from `t` lands on the right end of the zone the setter is currently inside. So the
cascade's iterates *are* the successive zone ends of a run from the bound, and conversely a run's
steps satisfy the move's defining property. The claim is then `le_antisymm` of two inequalities: the
run's end is at least the fixed point (by (b), since the run ends at a lonely instant), and at most
it (`first_isolation_of_run`).

**What this buys.** The first isolation instant is characterised with **no iteration in the
statement** — purely as a property of the lap-completion zones. `Run.covers` is the supporting fact
that a run's zones follow on from its start to its end.

### (d) Some runner sits at exactly one eighth — `flank_at_first_isolation`

At `T` the last move landed on an opening `(k + 1/8)/e` of the setter `e`, so `e·T = k + 1/8` and
that runner is at circle distance exactly `1/8` — as the nearest ahead or the nearest behind. This
is what makes "flank" the right word and is the hinge into §6.

---

## 5. Localisation (Theorem 6.3) — the finiteness argument

**Claim (d), the substantive part.** If the subject is lonely at some `s > 0`, the cascade reaches a
fixed point.

**Argument.** Two steps.

1. **Every iterate below `s` lies in a finite set** (`iterate_mem_openings`). By induction: each move
   lands on an opening `(k + 1/8)/d` of some disparity `d`, and by §4(b) every iterate is at most
   `s`, so `(k + 1/8)/d ≤ s` forces `k ≤ ⌈d·s⌉`. Hence every iterate lies in

       {bound} ∪ { (k + 1/8)/d : d ∈ ds, 0 ≤ k ≤ ⌈d·s⌉ },

   a finite set (seven disparities, each with finitely many admissible `k`).
2. **A strictly increasing sequence cannot stay in a finite set.** If the cascade never reached a
   fixed point, every move would strictly increase `t` (`lt_nextOpening`), giving infinitely many
   distinct values in a finite set.

**This is where pigeonhole enters, and it is native.** The author's ruling of 2026-09-15 —
pigeonhole and residue counts are admissible **as tools** — is exactly what licenses it, and the
2026-09-17 withdrawal of Propositions 6.10–6.11 turned on a different test (§9).

### Corollary 6.4 — the four equivalent statements

Combining §4 and §5: for every subject, *the subject is lonely at some positive instant* ⟺ *the
cascade reaches a fixed point* ⟺ *a run of lap-completion zones from the bound ends at a lonely
instant* ⟺ *some flank has a lonely opening*.

**This is the hinge of the whole framework.** It is what makes "Existence" and "the conjecture at
eight runners, per runner" the same statement, and it is why closing any one door closes the target.

---

## 6. Every lonely instant is matched by an opening (Proposition 6.1)

**Claim.** If the subject is lonely at `t`, it is lonely at an opening `(⌊e·t⌋ + 1/8)/e` of one of
its own disparities `e`, no later than `t`.

**Argument.** Walk back from `t`. Each runner `d` is clear at `t`, so `d·t` sits at phase in
`[1/8, 7/8]`; the last instant at or before `t` at which some runner sat exactly on the threshold on
its way *out* is an opening. Take the latest such opening `t₀ ≤ t`. Between `t₀` and `t` no runner
enters a zone (any entry would have to cross the threshold, producing a later boundary instant), so
the subject is lonely throughout `[t₀, t]`, in particular at `t₀`.

**The scope, stated because it is easy to over-read.** This is a statement about the **earliest**
lonely instant, not about every lonely instant — those fill intervals. Applied at the earliest
instant, the opening it supplies is positive and no later, so it *is* that instant.

---

## 7. Flanks

### 7.1 Only ratios enter (Theorem 6.8, `position_at_flank`)

At flank `e`'s `k`-th opening `t = (k + 1/8)/e`, runner `j` sits at `d_j·t = ρ_j·(k + 1/8)` laps,
`ρ_j = d_j/e`. The speeds have disappeared; only the seven ratios to the flank remain. Two cases:

- **Integer ratio `A`.** `A·(k + 1/8) = Ak + A/8`, and `Ak` is a whole lap, so the circle distance is
  `‖A/8‖` — the **same at every opening**. Clear iff `8 ∤ A`, in the way at every opening if `8 | A`.
- **Non-integer ratio.** Writing `ρ = ⌊ρ⌋ + f`, the position is `k·f + ρ/8` modulo an integer
  (`fractional_ratio_circDist`). **Only the fractional part moves from opening to opening.**

### 7.2 One fractional ratio (Theorem 6.9) — the nearest-integer walk

**Claim.** A flank at which exactly one ratio is non-integer, with every integer ratio not a
multiple of 8, has a lonely opening.

**Argument** (`exists_clear_step`, eighty-four lines, **no non-local identifier at all**). Follow
the nearest integer to `k·f + c` as `k` increases by 1. The step size is `f ∈ (0, 1)`, so:

- if `f < 2/n`, the nearest integer **stays fixed** for at least one step, and the point drifts
  through the clear band;
- if `f > 1 − 2/n`, the nearest integer **advances by one** each step, and again the point passes
  through the clear band;
- a middle step cannot be followed at all — the nearest integer can neither stay nor advance by
  exactly one, which is a contradiction.

So some opening is clear. **No count, no density, no equidistribution.** The index is bounded by
roughly `1/min(f, 1 − f)`, which is why this argument survives the firewall test of §9 while the
withdrawn propositions did not.

### 7.3 The mixed pair (Proposition 6.10)

For a live flank with exactly two non-integer ratios, one on the `c`-lattice and one off it: the
lattice runner's verdict repeats with its denominator (`circDist_periodic_of_lattice`), so it is
clear on a whole **residue class** of openings. Restricting to that class, the second ratio faces
the situation of §7.2, and `class_killer_int` says a runner that shadows every opening of such a
class must itself lie on the lattice. The second does not. So an opening is clear.

Part (b) follows by symmetry: if both lie on lattices and shadow the flank between them, each must
lie on the other's lattice, so their reduced denominators divide each other and `c₁ = c₂`. **No
count is used in either part.**

**Why (a) is stronger than what it replaced.** The earlier statement needed "one rational and one
irrational". This needs only **off the lattice**, which a rational ratio whose denominator does not
divide `P` also satisfies.

### 7.4 The flank calculus — finiteness for a free disparity

When a shadowing set pins all but one disparity, the free one ranges over the reals and the flank
must be shown free for **every** value. Three facts do it, all about openings and denominators:

1. a disparity whose ratio to the flank has **denominator dividing `P`** has the same verdict at
   openings `k` and `k + jP`, so the **clear openings** — those at which every pinned disparity is
   clear — repeat with period `P`;
2. a disparity that shadows **every** opening of one such class must itself have denominator
   dividing `P` (`class_killer_int`, from `exists_clear_step`, covering rational and irrational
   ratios in one case with no rationality input);
3. therefore the **shadowing values** of the free disparity form a **finite set**, and if none of
   them shadows every clear opening, the flank is free for every real value.

The eighth-family theorem is the worked case: flank 7, period 7, clear openings `{1, 3}`, no
shadowing values — and it is re-derived from the general statement by supplying only that data.

### 7.5 The residue route — the verdict as a congruence

At a **whole-number** flank `b`, the real test `1/n ≤ circDist(a·t)` is equivalent to a condition on
one integer residue (`clear_at_int_flank_iff_emod`): the residue of `a·(n·k + 1)` modulo `n·b` lies
in the closed band `[b, (n−1)·b]`. The threshold has become a band of integers, the opening index
enters only through `n·k + 1`, and **no real number survives in the statement**.

Combined with `circDist_periodic_of_int_flank` — the verdict at an integer flank repeats with period
`e`, so openings `0 … e−1` carry every verdict — the search over `k` is **finite**. That is what
makes each census family decidable.

**What this does and does not give.** It decides each difference set. It discharges no universal:
the required `k` across difference sets is unbounded, reaching 369 in a directed search.

---

## 8. The `n > 2k` potential

**Claim.** With `k` disparities at threshold `1/n`, the cascade from the bound stops whenever
`2k < n`.

**Argument.** Define `lapsPassed n x t` as the number of openings of `x` at or before `t`, and the
potential `Ψ(t)` as the product over runners of the lap factors `(r + 1/n)/(r − 1/n)` of the laps
each has passed.

- **`potential_step`.** A move set by `x` at lap `Q` raises `Ψ` by at least lap `Q`'s factor: before
  the move `x` had passed at most `Q − 1` laps, after it `Q`.
- **`move_growth`.** The same move multiplies the instant by **less** than that factor.
- Composing, `t_N · Ψ(t_0) ≤ t_0 · Ψ(t_N)` along the cascade (`time_le_potential`).
- A Bernoulli bound in integer powers gives `Ψ(t)^n ≤ C^k·(∏_x (x + 1/t_0))²·t^{2k}`.

So when `2k < n` the instants are capped, and `exists_fixed_of_capped` turns a cap into arrival.

**No zone width or interval length enters.** The proof reaches the same threshold as a covering
count would, and the coincidence is exact — `n > 2k` is `k·(2/n) < 1`, which says `k` arcs of width
`2/n` cannot cover the circle — but the route uses no covering. That is why the row is kept.

**Why it reaches no order on the diagonal.** At `n = 8` the order-8 case is `k = 7`, and
`7·(2/8) = 7/4 > 1`.

---

## 9. Existence — what is proved *about* it, and what an argument would have to do

### 9.1 The reduction

Composing the formalised links leaves one statement:

| link | declaration |
|---|---|
| relocation is a change of scale | `move_eq_self_or_opening`, `nextOpening_at_scale` |
| `N` relocations move the nearest reading by at most a product of lap factors | `nearest_reading_recurrence` |
| a cascade whose instants are capped arrives | `exists_fixed_of_capped` |
| what it arrives at is the first isolation | `first_isolation_as_zone_run` |
| arriving ⟺ lonely somewhere | `lonely_iff_run_ends` |

> **Existence is exactly: the cascade's instants are uniformly capped.**
> `existence_of_capped` and `capped_of_existence`, **both directions**.

**The converse is stated deliberately.** A cap is no easier than Existence. The reduction's worth is
that what remains is one statement in the framework's own objects with every other link proved — not
that the obligation got smaller.

The same holds for Finite Active Membership (`FAM_iff_existence`, both directions) and for the four
doors on arrangements (`doors_agree`). **None of them is a weaker thing to aim at**, and that is
machine-checked rather than asserted.

### 9.2 What failure would require

A cascade that never stops lands every step on an opening lying strictly inside another runner's
zone, for ever. Each such step is arithmetic: if a runner at disparity `e` is in the way at an
opening `t = a/(8d)` at or after the bound, then `|e·a − 8w·d| < d` for some integer `w`; and since
`a ≥ d/d_min`,

    | e − (8w/a)·d | < d_min.

**A runner in the way at an opening lies within less than one `d_min` of a specific rational multiple
of the disparity whose opening it is.** Failure needs such a relation at every step, for ever.

### 9.3 The test an argument must pass

The firewall's operative ban is *no covering or emptiness language*: the construction runs a cascade
to a named instant. But the test is **not** the shape of the statement. Every result kept concludes
with an unbounded `∃` in Lean — Theorem 6.9 and Proposition 6.10 both end
`∃ k, Lonely n ds (flankOpening n e k)`.

**The test is whether the argument bounds where the instant is.** Theorem 6.9's witness comes from
`exists_clear_step`, whose index is bounded by `~1/min(f, 1−f)`, and `clear_in_class_of_not_int`
passes that bound through. The withdrawn Propositions 6.10–6.11 had no such bound anywhere — one had
`q = q′L` with `q′ ≤ Q^m` and `Q → ∞`, and the other named an opening with `k = 1, 5, 45, 442, 4420`
as a parameter tended to zero.

**It is the index bound, not the tool.** `exists_clear_step` argues by contradiction and is native;
`exists_fixed_of_lonely` uses pigeonhole and is native.

### 9.4 The obligation is per runner

Not per arrangement. A runner outside the proved families needs its own instant whether or not
another runner of the same arrangement is inside them. This is why a per-flank criterion cannot
discharge it: individual flanks are shadowed routinely — 2.6% of live ones — while no runner has
been found with **every** flank shadowed.

---

## 10. The order-5 certificate — a finite enumeration done soundly

Worth reading as a model, because three of its four qualifications were misread once each.

**Claim.** `sup R = 31/9` for every arrangement of ratio `S = d_max/d_min ≤ 26`, attained at the
word `(1,2), (2,1), (1,3), (3,1), (2,2), (1,6)` with margin `τ = 132/4165`. Since `31/9 < 4`,
Existence holds for every such arrangement.

**Why the enumeration is finite.** At ratio bound `S` no setter sets beyond lap
`L = ⌊(4S − 1)/5⌋`, because `R < 4` at the step before the exceedance forces `Q < (4S + 1)/5`, and a
runner's setting laps strictly increase. So words run to at most `3L` moves — `L = 20` and 60 moves
at `S = 26`.

**Why the relaxation is sound.** The word programs impose only that each setter is in the way just
before it sets and that the instant advances, **dropping** that the setter has the latest opening and
that the others are clear. So the optimum bounds the true supremum from **above**, and
`sup R < 4` over the relaxation proves it for the cascade.

**The four qualifications.** The value is **computed**, not recognised — exact rational arithmetic,
not the optimum of floating-point programs. The bound is on the **ratio** `S`, not the spread `W`.
The enumeration is a **relaxation in the sound direction**. And the sweep is **flat, not closed** —
`31/9` holds at every ratio bound from 10 through 26 with the same word and margin, but flatness over
a range is not a proof beyond it, and unbounded ratio stays open.

---

## 11. Which arguments carry which results

| result | argument | section |
|---|---|---|
| Prop 2.1 | residue arithmetic on `ℕ` | §1 |
| band identity | position is `s/8` laps | §2 |
| the scale recursion | `nextOpening_at_scale` plus the factor `s/(8N+1) < 1` | §2 |
| Thm 6.2(a) | definition of `move` | §4 |
| Thm 6.2(b) | `before_floor` plus "no move passes a lonely instant" | §4 |
| Thm 6.2(c) | iterates are zone ends; `le_antisymm` of two runs | §4 |
| Thm 6.2(d) | the last move lands on an opening | §4 |
| Thm 6.3(d) | finite opening set plus strict increase (pigeonhole) | §5 |
| Cor 6.4 | composition of §4 and §5 | §5 |
| Prop 6.1 | walk back to the latest boundary instant | §6 |
| Thm 6.8 | `ρ·(k + 1/8)`, split by integrality of `ρ` | §7.1 |
| Thm 6.9 | the nearest-integer walk | §7.2 |
| Prop 6.10 | lattice periodicity plus `class_killer_int` | §7.3 |
| the flank calculus | periodicity, `class_killer_int`, finite shadowing values | §7.4 |
| Thm 6.13, 6.14 | period `e` at an integer flank; the residue congruence | §7.5 |
| `n > 2k` | the lap-factor potential plus Bernoulli | §8 |
| the reduction | composition of five proved links | §9.1 |
| order 5, `S ≤ 26` | bounded words plus exact rational linear programs | §10 |
