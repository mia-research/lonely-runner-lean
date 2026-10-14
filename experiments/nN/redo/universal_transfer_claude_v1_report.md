# Universal AP/grid isolation transfer — findings (Claude, reasoning-only pass)

Scope: read in full `IncomingWindowN.lean`, `PinchReflectionN.lean`,
`FiniteWindowContinuationN.lean`, `PathRouteN.lean`, `PathWindowN.lean`,
`SegmentWindowN.lean`, `TrainCollapseN.lean`, `DeformationN.lean`, and
(for context) `ClusterTransferN.lean`; and `docs/n8/RUNNING_LOG_order8_v1.md`
sections E100–E155, E269–E322, E378–E381 (the AP/grid displacement
programme and its most recent corrections). No Lean written, no build run,
no search beyond reading. Conclusion first: **the transfer is NOT
established.** One precise analytic gap remains, named below, and it is the
same gap in both avenues 1 and 2.

## (a) Strongest actual deduction, with line references

`PathWindowN.lonelyRunnerAt8_of_window` (`PathWindowN.lean:189`) reduces
`LonelyRunnerAt8` to one hypothesis, `WindowBound` (`PathWindowN.lean:32-35`,
registered OWED, confirmed at `RUNNING_LOG:10542`: *"One hypothesis is open:
`hbound`/`WindowBound`... It is used only in closedness
(`lonelyAt_of_limit`)"*). `WindowBound` is used only inside
`DeformationN.lonely_along_path`'s `hbound` argument
(`DeformationN.lean:83-84`, used via `lonelyAt_of_limit`, `DeformationN.lean:59-76`).

The deformation theorem (`DeformationN.lean:78-100`) needs two things at
every `s`: **openness** (a margin at the current witness propagates to
nearby `s`, `lonelyAt_of_close`/`eventually_lonely_of_margin`,
`DeformationN.lean:39-55,104-118`) and **a witness in a fixed `[c,T]`**
(`hbound`). The whole AP/grid programme (E296–E321) is an attempt to supply
`hbound` constructively along a one-runner-at-a-time path. It does not
succeed; what it supplies, precisely:

- `PinchReflectionN` + `IncomingWindowN`: at a single *rational* pinch
  (`d : ι → ℚ`, `t : ℚ`), a replacement label and a **local, one-sided**
  right-neighbourhood `[0,e]` on which the window persists
  (`PinchReflectionN.rational_pinch_transport`, lines 236-253, composed in
  `IncomingWindow.replacement_of_incoming`, lines 49-73). The file's own
  header is explicit: *"This is LOCAL transport. It does not bound
  successive reflections or rule out accumulation of parameter boundaries"*
  (`PinchReflectionN.lean:11-13`).
- `FiniteWindowContinuationN`: **if** a parameter path is covered by
  finitely many fixed integer labels `Q` up to an endpoint, the endpoint is
  covered by one of the same labels (`endpoint_of_finite_coverage`, lines
  51-61; `endpoint_lap_window`, lines 65-111), and a uniform bound `D·T` on
  reading×time turns into exactly such a finite `Q`
  (`endpoint_of_bounded_witnesses`, lines 115-153). This is a correct but
  **conditional** closure lemma: its hypothesis (`hcover`/finite `Q`, or
  `hN : D*T ≤ N`) is the content of `WindowBound` restated, not a route
  around it. The file's own header says so: *"This is the accumulation part
  of the AP-deformation programme, not the replacement theorem... No
  assertion supplies coverage before or after it"* (lines 4-9).
- `SegmentWindowN.lonely_window_of_one_free` (lines 79-124): for a one-mover
  segment with the other six readings of common period `P`, every point off
  the lattice is lonely with `t ≤ t₇ + P·(1/(4·circDist(x·P)) + 1)`. As the
  mover approaches a lattice point, `circDist(x·P) → 0` and this **specific**
  bound diverges. Header: *"The bound is sharp in kind: `T → ∞` as `a → 0`,
  so the window is not uniform at a lattice point... Nothing here says
  anything at a lattice point"* (`SegmentWindowN.lean:11-13`).
- `TrainCollapseN.lonely_of_train_collapse` (lines 60-139): a *different*
  mechanism — a compact train `{N+e : e∈E}` sent to large magnitude `N`
  collapses to order 7 on its offsets, witness in `[2τ, 2τ+1/N)`, `τ`
  independent of `N`. This does not diverge as `N→∞`; it is unrelated to the
  resonance (denominator-growth) problem of avenues 1–2 (see (b)).

`RUNNING_LOG` confirms the owner has explicitly and repeatedly rejected the
one framing most likely to be mistaken for a fix: a finite-label/move-budget
counting argument (`E380`, line: *"a proposed existence strategy by counting
the zones available below R and the number of moves the blocking chain would
need... is 'WRONG'"*), and the multi-pinch/"tight arrangement" question
(statement (T): a tight whole-number arrangement has only simple pinches) is
recorded OWED, checked only for readings `≤ 24` (`E280`, `E381`).

## (b) Complete proof: not found. The precise unresolved statement

**The gap is the same quantity in avenues 1 and 2**, read two ways:

> Does there exist, for the specific straight-line deformation from the AP to
> a given target, a **uniform** `e₀ > 0` such that every pinch produced along
> the path by `PinchReflectionN.rational_pinch_transport` has right-
> neighbourhood radius `≥ e₀` (equivalently: the pinch parameters `s₁ < s₂ <
> …` in `[0,1)` are `e₀`-separated)?

If yes, finiteness of the pinch set on `[0,1]` is immediate (an `e₀`-
separated subset of a bounded interval is finite — this half is not hard),
`FiniteWindowContinuationN.endpoint_of_finite_coverage` applies, and
`WindowBound` is discharged for this path. If no uniform `e₀` exists, the
pinch parameters can accumulate at some `s* ≤ 1` with `s* < 1` possibly
irrational, and nothing in the tree says what happens at `s*` or beyond.

**Avenue 1 — why no shortcut closes this.** `affine_right`
(`PinchReflectionN.lean:22-44`) manufactures its radius as `r_i =
C_i/(|B_i|+1)` (or `1`) and takes the **inf over the current finite index
set** — a quantity computed *at* each pinch from *that* pinch's data, with
no claimed lower bound across pinches. `rational_reflection_data`
(`PinchReflectionN.lean:218-231`) sets the reflection multiplier `lam = 8N-1`
where `N` is the **product of denominators** (`rational_common_multiplier`,
lines 197-214) of `8·d_i·t` over the current index set. Nothing bounds how
these denominators evolve from one pinch's witness time to the next witness
time — the new witness time is itself derived (via
`IncomingWindow.rational_window_time`) from the *new* integer labels `p i =
P_i - q_i - 1`, which are themselves unbounded integers produced by the
previous reflection. A rational pinch at every step does **not** exclude an
irrational accumulation point of the pinch parameters; compactness of
`[0,1]` gives a finite subcover only of an *open cover already known to
cover every point*, which is exactly `hcover`/`WindowBound` again — it does
not manufacture such a cover from one-at-a-time local replacements. (This is
stated explicitly in the task framing and confirmed structurally by reading
`affine_right`.) **No existing theorem bounds denominator growth across
reflections; this is new mathematical content, not yet attempted.**

**Avenue 2 — the construction's divergence is real but not evidence that the
true witness diverges, and one existing theorem partly outflanks it.**
`SegmentWindowN`'s bound comes from `exists_clear_step_bounded`
(`SegmentWindowN.lean:63-73`), a crude multiplicative search
(`exists_far_multiple_bounded`, lines 30-60) with no claim of optimality. The
project's own `IntegerGridN`/`IntegerDisplacementN` work (`RUNNING_LOG`
E297–E301, not required reading but referenced there) shows that **at** many
integer/lattice arrangements the true witness is small and explicit (e.g.
`lonely_of_displacement`'s `O(1/(8c))` instant), so `T→∞` as `a→0` is a
property of *this* search procedure, not of the conjecture. More usefully:
`DeformationN.lonelyAt_of_close` (`DeformationN.lean:39-55`) gives, for a
lattice point with a **positive margin** `ε` at its own witness `t₀`, a
*fixed* (not shrinking with `a`) neighbourhood radius `η ≤ ε/(2|t₀|)` on
which every nearby arrangement is lonely **at the same `t₀`** — no window
search needed at all for non-tight lattice points. So resonance is only a
genuine obstacle at **tight** lattice points (margin exactly `1/8`
everywhere, only pinches) — exactly statement (T)'s domain, which is OWED
(`E280`, `E381`) and reduces back to avenue 1's accumulation problem via
`PinchOpenN`/`PinchReflectionN`. **What is needed at resonance and does not
exist**: either (i) a proof that every lattice point reached by an AP-to-
rational-target path is non-tight (margin `>0`), making `lonelyAt_of_close`
sufficient throughout with no diverging window, or (ii) statement (T) plus a
resolution of avenue 1's uniform-gap question for the tight case. Neither
exists.

**Avenue 3 — TrainCollapseN does not absorb the gap; wrong variable.**
`TrainCollapseN`'s `N` is a reading's **magnitude** (speed), and its
boundedness mechanism (`N ≥ 56m`, lines 60-66) converts "send one cluster to
large speed" into "bounded witness," because the *margin* `1/7 - 1/8 = 1/56`
is a fixed combinatorial slack independent of `N`. Avenues 1–2's divergent
quantity is a **time-denominator / parameter-accumulation** growth at
*bounded* reading magnitudes — a different variable entirely. There is no
map from one to the other in the file, and attempting to build one (treating
`56m` as a "move budget" bound on reflections) is exactly the move-budget
termination strategy the brief and the owner (`E380`) rule out.
`ClusterTransferN` (sibling file, not in the required list but present in
the tree) is a coordinate change only and says so of itself: *"none asserts
existence of a cluster stopping point or a finite universal catalogue"*
(`ClusterTransferN.lean:8-9`).

## (c) Suggested Lean theorem statements (not proved; targets only)

```lean
/-- Easy half (standard analysis, NOT the open content): a uniformly
separated subset of a bounded interval is finite. -/
theorem finite_of_uniform_gap {e0 : ℝ} (he0 : 0 < e0) (P : Set ℝ)
    (hP : P ⊆ Set.Icc (0:ℝ) 1)
    (hgap : ∀ s1 ∈ P, ∀ s2 ∈ P, s1 ≠ s2 → e0 ≤ |s1 - s2|) : P.Finite

/-- The open content (avenue 1): does a uniform e0 exist for the pinch
sequence `PinchReflectionN.rational_pinch_transport` manufactures along a
fixed straight-line rational-direction path? Everything downstream
(finiteness, FiniteWindowContinuationN, WindowBound for this path) follows
from this hypothesis; nothing in the tree currently proves or refutes it. -/
theorem uniform_reflection_gap_along_path (S : Finset ι) (hS : S.Nonempty)
    (d0 dT : ι → ℚ) (hd0 : ∀ i ∈ S, 0 < (d0 i : ℝ)) :
    ∃ e0 : ℝ, 0 < e0 ∧
      ∀ s : ℚ, 0 ≤ (s:ℝ) → (s:ℝ) < 1 →
      ∀ (t : ℚ) (q p : ι → ℤ), -- t a rational pinch witness at parameter s
        True → -- (replace with the actual pinch-feasibility hypothesis)
        e0 ≤ (the e produced by rational_pinch_transport at this pinch) :=
  sorry -- NOT attempted; this is the highest-value next action, see (d)

/-- Avenue 2's outflanking route, made explicit: non-tightness of every
lattice point on the path removes the need for a window there. -/
theorem no_tight_lattice_point_on_path (a target : ι → ℝ) :
    ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ q : ι → ℤ,
      (-- (1-s)*a + s*target is the integer arrangement labelled q) →
      ∃ t ε : ℝ, 0 < t ∧ 0 < ε ∧ -- a witness WITH positive margin
        True := sorry -- equivalent in difficulty to statement (T), E280/E381
```

## (d) Highest-value next action

Attack `uniform_reflection_gap_along_path` directly as a Diophantine
estimate: bound `affine_right`'s radius `r_i = C_i/(|B_i|+1)` from below in
terms of the **bounded denominator of the straight-line path's rational
direction only** (not of the accumulating integer labels `P_i`), for a
*fixed* finite reading set `S`. This is the one new piece of mathematics
that, if it holds, discharges both avenue 1 and the tight-point residue of
avenue 2 via the two lemmas above; if it fails, it will fail for a
nameable reason (the task's own standard: "state precisely which axiom
breaks"), most likely because `C_i`/`B_i` scale with the *lap count*, which
is unbounded along the path — in which case the correct next question is
whether lap count itself can be bounded independently of the parameter
(a genuinely different, and currently unexplored, finiteness claim). Do not
attempt this via search, counting, or an assumed move budget — the owner
has rejected that frame for exactly this problem (`E380`), and the brief
rules it out independently.

No claim of universality is made. The limit quantifier (accumulation of
pinch parameters in `[0,1)`) and the target quantifier (arbitrary rational,
let alone real, target direction) are both explicitly open.
