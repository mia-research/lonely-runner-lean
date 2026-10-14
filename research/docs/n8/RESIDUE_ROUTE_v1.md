# The residue route: bounding the search with periodicity

2026-09-18. Artefacts: `experiments/n8/residue_route_v1/`. Lean:
`LRC/Cascade/Flanks.lean`, both new theorems axiom-clean
(`[propext, Classical.choice, Quot.sound]`), `lake build` 2443 jobs, exit 0.

Taken up because every counting route is closed — see `LONG_RETURN_CIRCLE_v1.md`: both sides of
the growth circle count the number of moves, so no contradiction can come out of it. Residues are
not a count of moves.

---

## 1. What was already there

`lonely_iff_bounded_search` (earlier work): over whole-number differences the unbounded `∃ k`
collapses to `k < e`, because the verdict at an integer flank repeats with period `e`. That bounds
the search **in the opening index**. It leaves the criterion real-valued — a minimum of fractional
parts, which supports inequalities and nothing else.

## 2. What is new  `[PROVED]`

**`Flanks.clear_at_int_flank_iff_emod`.** A whole-number runner `a` is clear at the `k`-th opening
of the whole-number flank `b` exactly when

    b  ≤  a·(n·k + 1)  mod  n·b  ≤  (n−1)·b

The real threshold `1/n` has become a band of integers; the opening index enters only through
`n·k + 1`; no real number survives.

**`Flanks.lonely_iff_emod_search`.** Composing the two: for whole-number differences,

    (∃ s > 0, Lonely n ds s)  ↔  ∃ b ∈ ds, ∃ k < b, ∀ a ∈ ds,
                                  b ≤ a·(n·k+1) mod n·b ≤ (n−1)·b

A finite integer computation, `Σ_{b ∈ ds} b` residue tests.

**Checked against the definition before formalising**: 60,000 cases against real-valued `circDist`,
**0 disagreements**; the finite search against a wide real search on 4,000 sets, **0
disagreements** (`residue.out`).

## 3. Periodicity also bounds the *difference set*, not only the opening  `[PROVED + VERIFIED]`

Visible in the criterion: the verdict for `a` depends on `a` only through `a mod n·b`. So at a
**fixed** flank `b` the whole question is a finite check over `(ℤ/n·b)^{|ds|}` — finiteness in the
`ds` direction, which no earlier statement gave.

Measured with a firing control (`resfinite.out`, 40,000 trials each):

| | verdict unchanged | changed |
|---|---|---|
| shift every runner by a multiple of `n·b` | **40,000** | 0 |
| control: shift by a non-multiple | 1,168 | **38,832** |

The control fires, so the invariance is the residue structure and not a degenerate test.

## 4. What this does **not** do

**It does not prove `ExistenceAt8`.** That quantifies over infinitely many difference sets; §3
gives a finite problem *for each* flank value `b`, indexed by an unbounded `b`. A family of finite
problems is not a finite problem. `(8b)^6` tuples is 262,144 at `b = 1` and 16.7M at `b = 2`.

**The union-bound wall reappears unchanged.** Each runner blocks `2b−1` of the `n·b` residues, a
fraction tending to `2/n = 1/4`. Seven runners give `7/4 > 1`: vacuous, exactly as in the real
form.

**What the congruence buys, precisely** (`rescover.out`, 20,000 flanks). Restricting to
`u = n·k+1`, i.e. `u ≡ 1 (mod n)`, is not cosmetic — it neutralises the flank runner itself, which
sits exactly on the boundary (`circDist = 1/n` exactly, `circDist_flank_self`) and so never blocks:

| | free opening exists | mean fraction free |
|---|---|---|
| `u ≡ 1 (mod n)` — the real openings | 0.951 | **0.1976** |
| all residues mod `n·b` | 0.975 | 0.1709 |

So the effective count is **six** blockers, not seven — and `6 × 1/4 = 1.5` is still `> 1`. The
wall moves; it does not fall.

## 5. Measurements, and what they are not evidence for

`residue.out`, `resfinite.out`: 200,000 whole-number difference sets in `[1,120]`, **0 with no
lonely opening**. Search cost: median `Σ_b b = 420` openings, max 727. Lonely openings found per
set: min 14, 1st percentile 39, median 76 — never exactly one.

**This is not evidence for LRC at `n = 8`.** The per-flank failure rate is about 4.9%; if flanks
behaved independently a set would fail with probability ≈ `0.049^7 ≈ 7e-10`, so zero failures in
200,000 sets is what the criterion predicts either way. The measurement confirms that the
criterion is the right criterion. It says nothing about whether it always succeeds.

## 6. The question, stated in the new object

At flank `b`, runner `a` blocks the openings `u` with `a·u mod n·b ∈ [0, b) ∪ ((n−1)b, n·b)` — a
Bohr set in `ℤ/n·bℤ`. LRC at `n = 8` over whole numbers is:

> seven such Bohr sets, one per runner, never cover the arithmetic progression `u ≡ 1 (mod 8)` in
> `ℤ/8bℤ`, for at least one choice of flank `b ∈ ds`.

That is the handover point. It is a covering statement about Bohr sets restricted to a progression
— congruences, CRT and counting in `ZMod` all apply to it, and none of them apply to `circDist`.

**The known obstruction to the obvious next move**: the band `[b, (n−1)b]` is an interval, and
intervals do not factor under CRT. Splitting `n·b` into prime parts does not split the condition.
Recording it here so it is not rediscovered as a surprise.
