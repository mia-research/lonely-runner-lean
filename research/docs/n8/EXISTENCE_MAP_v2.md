# Map of Existence at Order 8 — v2

Corrects the owner's working map. Changes are marked **[CHANGED]** with the reason.

| Profile / class | Status | Mechanism / bound |
|---|---|---|
| Ratio bound `S ≤ 7` | `[PROVED]` | Clears at `R=1` (`u=1/8`), all orders (`S ≤ n−1`) |
| Integer readings, no collision (`8 ∤ sⱼ`) | `[PROVED]` | Clears at `R=1` via `spine_all_or_nothing`; arbitrary magnitudes |
| Integer readings, with collisions (`8 \| sⱼ`) | **[CHANGED]** `[EXHAUSTIVE, two ranges]` | see below |
| Flanks with ≤ 1 fractional ratio | `[PROVED]` | Nearest-integer walk (`TwoWalker.lean`) |
| Flanks with off-lattice ratio pairs | `[PROVED]` | Lattice-crossing criteria (`TwoWalker.lean`) |
| All integer arrangements `v₈ ≤ 40` | `[VERIFIED]` | 148.5M runner instances, 100% lonely, `R ≤ 44856/3749 = 11.964791` |
| General rational & irrational profiles | `[OPEN]` | Needs `R < 12` / `R < 16`, or non-shadowing across all 7 flanks |
| **Witness form, all orders** | **[NEW]** `[PROVED]` + `[VERIFIED-INSTANCE]` | see below |

## [CHANGED] Integer readings with collisions

The map read: *"Clears at `R ≤ 7` with clear measure `≥ 53/924` (swept to `s₇ ≤ 200`)."* Two
corrections.

**The `53/924` floor is retracted** (2026-09-19). `GapRule.gap_ge` proves the smallest possible gap
for readings `≤ H` is `1/H²`, so the minimum decays; a gap of `1/3080` exists at readings `55, 56`.
`53/462` (half `53/924`) is exact and exhaustive **for readings ≤ 40** and is not a bound past that.
It was never a bound.

**"Swept to `s₇ ≤ 200`" is not backed by a completed run.** The on-disk record
(`INTEGER_CASE_v2.md`) says readings **≤ 40**, 1,917,719 profiles. The ≤200 sweep is
`experiments/n8/branchB_v2.py`; it was started as a background job on 2026-09-19 and stopped, having
written zero bytes. Standing precedent: a run that did not complete is a run that did not happen.

**What is actually established, in two ranges:**

- readings `≤ 40`, all 6 free readings: exhaustive, 1,917,719 profiles — `[VERIFIED — exhaustive, exact]`
- readings `[2,30]`, all 6 free readings: exhaustive, 244,790 profiles, **0 failures** in the
  two-integer form below — narrower range, but complete, and stated in the right category

**The branch is now a statement about two integers.** For every profile `S`, is there `s ∈ S` and
`A ≡ 1 (mod 8)` with `s ≤ A ≤ 7s` such that `s'A mod 8s ∈ [s,7s]` for every `s' ∈ S`. No reals, no
intervals, no measure.

**Known dead ends for this branch, so they are not re-attempted:** generic counting (each reading
kills ~1/4 of candidates, seven give `7/4 > 1` — the classical `10.5` against `6`); Hunter–Kounias on
the overlaps (measured best spanning tree `3.10` against `4.5` needed); `s = s*` (18,809
counterexamples); largest reading (794).

## [NEW] Witness form, all orders

`ReachRule.witness_normalised` `[PROVED]`, axiom-clean: if covering fails, the witness is the start
or `(n·m+1)/s`. On the LRC bad sets this reads: **a lonely point exists of the form `t = A/(n·s)`,
`s` a speed, `A ≡ 1 (mod n)`.** `[VERIFIED-INSTANCE]` at orders 4–9, 0 mismatches in 12 arms; the
`n ≤ 7` arms test the reduction rather than the conjecture.

**No novelty claim.** Witness-denominator normal forms are an active area and at least one other
exists (sine-crossing ⟹ denominator = sum or difference of two velocities). Relationship unchecked —
see `WITNESS_NORMALISATION_v2.md` §1.

Cross-cutting, not a row in the old sense: it constrains the witness for **every** class above.
