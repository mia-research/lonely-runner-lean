# The deformation picture: where the barrier must be answered

2026-09-17, at the owner's instruction to reason from the framework for clues, given that we know why
any set of speeds produces an isolation time for each runner — deformation of the ideal global isolation
pushing each individual isolation event.

**The framework already has this calculus, in §4.2–4.4, and I had not used any of it.** Every route I
took this session was in the readings-and-scales picture. This document works in the other one, and the
difference is structural, not stylistic.

Artefacts: `experiments/n8/gap_structure_v1.py`, `deformation_descent_v1.py`, and the checks below.

---

## 1. What the framework already proves about deformation

- **§4.1, Theorem 4.1.** Runner `i` is lonely **iff** both gaps flanking it on the track are `≥ 1/8`.
- **§4.2, Theorem 4.2.** All eight lonely **iff** every gap is exactly `1/8`. *"Perfect isolation has no
  slack"* — at the ideal both flanks sit exactly on the threshold, so any deviation toward the subject
  puts a runner in the way. That is why a near-ideal arrangement cannot borrow the ideal's instant.
- **§4.3, Theorem 4.5.** Writing the speeds as `A + e` against a progression `A_k = v₀ + k·d`, and fixing
  `t = r/(n·d)` with `gcd(r,n) = 1`, the progression part places the `n` runners on the `n` distinct
  `n`-ths, one each, **for every runner simultaneously**.
- **§4.3, Theorem 4.6.** The deviation displaces runner `k` by exactly **`e_k·r/d` eighths**.
- **§4.4, Theorem 4.7.** The instant survives iff every displacement is a whole number of eighths and
  `k ↦ kr + e_k·r/d (mod n)` is a bijection.

So at a reference instant runner `k` sits at slot `k·r mod n`, displaced by `δ_k = e_k·r/d` eighths.
**That is the deformation, exactly, as an object.**

## 2. What loneliness becomes there  `[VERIFIED — exact]`

Consecutive slots are `1/n` apart in the ideal, so the gap after the runner in slot `j` is
`(1 + δ_{j+1} − δ_j)/n`. Theorem 4.1's condition `gap ≥ 1/n` is therefore

> **`δ_{j+1} ≥ δ_j`** — a pure **order** condition on the displacement sequence.

Hence a runner is lonely exactly when it sits at a **non-descent** of the cyclic displacement sequence:
`δ_{j−1} ≤ δ_j ≤ δ_{j+1}`.

**Exact, with its hypothesis measured.** Slot order is track order only while no displacement crosses a
slot boundary, i.e. while every step `δ_{j+1} − δ_j > −1`:

| regime | agreement with the definition |
|---|---|
| no crossing (every step `> −1`) | **1258 / 1258 = 100%** |
| crossing present | 655 / 3242 = 20% |

Corollary 4.4 checked against the definition on the same data: simultaneous counts
`{0,1,2,3,4,5,6,8}` — **7 never occurs**, in 4,000 samples.

## 3. Two facts the readings picture does not have

**(a) A conservation law.** The steps telescope around the cycle, so `Σ_j (δ_{j+1} − δ_j) = 0` exactly, at
every reference instant — equivalently `Σ_j (g_j − 1/8) = 0`, verified 200/200. **Deformation is
conservative**: it cannot create a deficit without creating an equal surplus. A gap below `1/8` blocks
exactly the two runners adjacent to it, so `m` deficient gaps block at most `2m` runners and at least
`8 − 2m` are lonely — 0 violations in 1,037 samples, and instants with nobody lonely occur only at
`m ≥ 4`, as that predicts.

**(b) The magnitude drops out.**  `[VERIFIED — 11,892 / 11,892]`  `δ_k = e_k·r/d` scales linearly in `r`,
and the condition is a set of *comparisons* between `δ`s, which a positive scaling preserves. So the
lonely set at a reference instant depends on `r` **only through the slot permutation `k ↦ kr mod n`** —
never through the size of the displacement.

> At a reference instant the question is **purely combinatorial**: a permutation of the deviation vector,
> and which runners sit at non-descents of it. `r`'s magnitude enters only through whether the
> deformation still preserves cyclic order.

## 4. Why this is where the barrier must be answered  `[reasoning, marked]`

**The readings picture discards the framework's own constraint.** Working in differences and scales,
seven ratios and a scale float freely — there is no conserved quantity among them. That is why every
route taken there had to reach outside for something to constrain them, and why each thing reached for
was an import: a covering bound, a union bound, a density, a window. The constraint `Σ g_j = 1` is a fact
about the **track**, and the change to difference coordinates throws it away. I was not importing because
I was careless; I was importing because I had chosen coordinates in which the native constraint is
invisible.

**And this picture's coordinates are the output object.** Register §0: the candidates are `t = p/(8D)`
and the output is the pair `(D, a)`. §4.3 fixes `t = r/(n·d)`. These are the same thing: **`D = d`, the
progression step, and `a = r`.** So a proof conducted here cannot fail R5 — it ends in `(D, a)` because
that is what a reference instant *is*.

## 5. The barrier, stated in this picture

`φ(8) = 4` reference instants per progression (`r = 1, 3, 5, 7`), each giving a permutation of the same
ordered deviation vector. A runner is lonely at `r` iff its cyclic neighbours under `k ↦ kr` bracket it
in `e`-value. When no `r` works, the cascade changes the scale (§4.6) — a new progression, hence a new
deviation vector and a new combinatorial datum.

> **The barrier: does the family of progressions the cascade reaches always present each runner as a
> bracketed element?**

Two things this makes visible that the readings picture did not:

- **it names the runner.** The non-descent condition is per-slot, so it says *which* runner is lonely,
  not that some runner is. Existence is per runner, and every counting statement I reached for gave only
  "some";
- **the no-crossing hypothesis is what the cascade's own move restores.** Crossing happens when
  `(r/d)|e_{j+1} − e_j| ≥ 1`, i.e. when the progression fits the arrangement badly. §4.6 moves scale
  exactly then. So the framework's own repair is the thing that returns the problem to the regime where
  §2's characterisation is exact. `[inference — not tested here]`

## 6. What is not established

- §2's characterisation is exact **only** in the no-crossing regime, and in my sampling that regime was
  the minority (1,258 of 4,500). Whether the cascade's rescaling reliably restores it is §5's inference
  and is untested.
- Nothing here proves Existence, or narrows it. It relocates it to a combinatorial statement about
  permutations acting on a deviation vector — which is a change of instrument, not a result.
- The framework's §4.5 families (Theorem 4.8, 4.9) already live in this picture. Whether the open cases
  are also expressible here has not been checked.
