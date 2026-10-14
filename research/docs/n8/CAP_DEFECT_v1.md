# The cap, and why the last step keeps moving

*Version 1, 2026-09-20. Findings from a structural audit of `LRC/Cascade/` and `LRC/Spec/` against
`MANUSCRIPT_v17.md` and `PROOF_SPINE_v1.md`. Every claim below is backed by a named artefact under
`experiments/n8/`. Nothing here is a judgment about difficulty.*

---

## 0. What is sound

`LRC/Cascade/` and `LRC/Spec/` contain no `sorry`, no `admit`, no `native_decide`. `doors_agree` is
proved as stated, both directions, on injectivity alone. No false theorem is derived anywhere in the
audit's scope. The simulator used below reproduces the framework exactly on every case where the two
can be compared: the recorded arrival `t = 49/1872` for `(27,70,107,137,159,188,344,393)` subject
`393`, the recorded `u = 165/128` for `(1,31,75,97,128,160,176,225)` subject `1`, the recorded
`33/56` at `(2,6,8,9,11,14,15)`, the recorded count `170,213`, and per-runner lap monotonicity
(`Certificate.laps_strictly_increase`). `[VERIFIED — exact rational arithmetic;
experiments/n8/doorfirstlap_refutation_v1.out, doorfirstlap_cap_growth_v1.out,
cascade_setter_laps_v1.out]`

## 1. `DoorFirstLap` is false

`LRC/Spec/Doors.lean:298` states

```lean
def DoorFirstLap (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∀ N : ℕ, (move 8 (diffSet v k))^[N] (firstReading v k) ≤ 1 / leastDisp v k
```

which asserts `τ = d_min · t ≤ 1` — the cascade arrives inside the nearest runner's first lap.

**Refuted** by the arrangement `MANUSCRIPT_v17.md` §6.7 names four paragraphs earlier as its own
28-move adversarial case: `(27, 70, 107, 137, 159, 188, 344, 393)`, subject `393`, disparities
`{49, 205, 234, 256, 286, 323, 366}`. The cascade arrives at `t = 49/1872` — the value the manuscript
records — and

```
τ = 49 · 49/1872 = 2401/1872 = 1.28259 > 1
```

The arrival is lonely (every `circDist(d·t) ≥ 1/8`, one reading exactly `1/8`), and no opening at or
before it is lonely, so it is the first isolation instant. A second witness is §6.7's own second-lap
case `(1, 31, 75, 97, 128, 160, 176, 225)` subject `1`, at `τ = 165/128 = 1.28906`, which §6.7
describes in words as *"in its second lap"*.

`[REFUTED — experiments/n8/doorfirstlap_refutation_v1.{py,out}]`

**Not load-bearing.** `DoorFirstLap` appears only as the hypothesis of
`doorCapped_of_doorFirstLap` and `lonelyRunnerAt8_of_doorFirstLap`. Both remain true; they are now
vacuous. No proved result is affected. What is affected is **direction**: this is the only place in
the tree where the cap is written down, and it is the wrong cap.

## 2. The measurement was right; the extrapolation was not

`DOORS_ON_ARRANGEMENTS_v2.md` records max `τ = 33/56` over primitive 7-subsets of `[1,18]`, `[1,20]`
and `[1,22]`, and infers *"the same constant all three times ... unchanged as the range grows"*.

The three figures reproduce exactly. The stability does not survive the next range:

| H | primitive 7-subsets of `[1,H]` | max τ | argmax |
|---|---|---|---|
| 18 | 31,788 | `33/56` = 0.58929 | `(2,6,8,9,11,14,15)` |
| 20 | 77,400 | `33/56` | `(2,6,8,9,11,14,15)` |
| 22 | 170,213 | `33/56` | `(2,6,8,9,11,14,15)` |
| **24** | 345,304 | **`17/24` = 0.70833** | `(3,9,11,14,15,19,24)` |
| 26 | 656,076 | `17/24` | `(3,9,11,14,15,19,24)` |
| 28 | 1,180,572 | `17/24` | `(3,9,11,14,15,19,24)` |
| **30** | 2,029,245 | **`17/22` = 0.77273** | `(4,11,14,17,19,24,30)` |
| 32 | 3,354,296 | `17/22` | `(4,11,14,17,19,24,30)` |

The cap breaks at the first range past where the measurement stopped. **It is shown not constant, not shown unbounded** — a maximum over a nested family is non-decreasing by construction, so three rising values evidence only that `33/56` is not a bound; `sup τ` is unmeasured. `[VERIFIED
— exhaustive, exact rational arithmetic; statistic fixed before the run;
experiments/n8/doorfirstlap_cap_growth_v1.{py,out}]`

Why `[1,22]` could not see it: depth needs **fine denominators** in the readings `u = d/d_min`. The
28-move case has `u = 1, 4.18, 4.78, 5.22, 5.84, 6.59, 7.47` — denominators of 49. Capping the
difference range caps the denominator, so the range parameter is not the axis depth varies along.
`S = d_max/d_min ≈ 7.47` on that case, inside `[1,22]`'s own range of `S`, so `S` is not the
discriminator either. This is the rational-reading frontier §9's v13 correction already identifies as
one problem with `R < 16`.

## 3. Why the last step keeps moving

Three separate facts, each checkable, that together say the tree currently has no mechanism that
could close the conjecture — not that it is one lemma short.

**(a) Everything proved in `Spec/` is an `↔` to the target.** `doors_agree` (four doors),
`target_forms_agree`, `existence_of_capped` / `capped_of_existence`,
`lonelyRunnerAt8_iff_existenceOnArrangements`, `existenceOnArrangements_iff_isolated`. An
equivalence is deductively free and can never be a last step. §6.7 says this of `doorCapped_iff`
itself: *"being an `↔` means either would have been the conjecture itself."* Each candidate for "the
last thing" that gets restated as an equivalence stops being a candidate at that moment. That is the
mechanism behind the repetition, and it is structural rather than a matter of care.

**(b) The only unconditional termination theorem cannot apply to LRC at any order.**
`ManyDifferences.stops_when_twice_card_lt` needs `2k < n` for `k` differences. A subject at order `n`
has `n − 1` differences, and `2(n−1) < n` fails at every `n ≥ 2`. The exponent is not slack to be
sharpened: `lapProd n L ~ L^{2/n}` is the true growth rate of that potential, so `Ψ(t) ~ t^{2k/n}`
and `t ≤ b·Ψ(t)` is vacuous whenever `2k ≥ n`. No constant improves it. The loss is that the
potential charges **every** runner at **every** lap it has passed, while only the setter's lap drives
the instant.

**(c) The only finite-certificate route is conditional on the two things that are unbounded.**
`Certificate.lean`'s word list is finite given a cap `C` **and** a ratio bound `S = d_max/d_min`
(`lap_mem_Icc`), with per-runner setting count `⌊(C·S−1)/n⌋`. Further, `nearest_never_sets` requires
`C ≤ n + 1 = 9`. On the 28-move case `R = 8·d_min·t = 10.26 > 9`, and the nearest runner **does** set
a move (at lap 1) — so that module's premise fails on the deep cases, and §6.7's own largest measured
`R ≈ 11.96` is likewise above 9. The apparatus is a small-`C`, small-`S` apparatus. Theorem 4.8 is
the `S ≤ 7` rule, which is where §6.7's 39% coverage figure comes from ("essentially all of it
Theorem 4.8").

## 4. One repair route closed

The natural reading of `nearest_reading_recurrence` —
`d_min·t_N ≤ (1/8)·∏_{j<N} F(Q_j)` with `F(Q) = (Q + 1/8)/(Q − 1/8)` — suggests bounding the product
by showing the setter laps `Q_j` grow, since `log F(Q) ≈ 1/(4Q)`.

**They do not grow.** The global setter-lap sequence for the 28-move case is

```
1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 4, 3, 4, 3, 5, 4, 3, 4, 6, 4, 5, 1, 6, 5, 8, 6
```

It returns to lap 1 at step 23. `Σ 1/Q_j = 12.14` and `∏ F(Q_j) = 20.98`. Per-runner the laps are
strictly increasing (consistent with `Certificate.laps_strictly_increase`), but seven interleaved
increasing sequences do not make the global one increase, and the laps stay small throughout.

So the cascade does not arrive because its lap factors decay. Any argument whose only handle is the
`F(Q_j)` product is bounding a quantity that stays near `1` for the whole run, and cannot see the
reason for arrival. `[VERIFIED — experiments/n8/cascade_setter_laps_v1.{py,out}]`

`lap_factor_le_first` gives `F(Q) ≤ 9/7` uniformly, so the product bound is `(9/7)^N` — increasing.
§9 already records that this direction yields a lower bound on the move count and no upper bound.

## 5. What is owed

1. `DoorFirstLap` should be marked `[REFUTED]` in `Spec/Doors.lean`, with the witness named in the
   docstring, and the surrounding prose block (lines 280–293) corrected — it currently asserts the
   cap as fact before grading it `[EMPIRICAL]`.
2. `DOORS_ON_ARRANGEMENTS_v2.md` lines 76–84: the stability inference is withdrawn; the table in §2
   above replaces it.
3. `PROOF_SPINE_v1.md` §9 and `MANUSCRIPT_v17.md` §7 name the two `DoorFirstLap` declarations as
   uncovered by the axiom check. That remains accurate, but the reason should now say they are
   vacuous rather than merely off the path.
4. No grade elsewhere moves. Nothing proved rests on any of this.

## 6. Where a real cap would have to come from

Not from `S`, not from the difference range, and not from the `F(Q_j)` product. The quantity that
actually varies with depth is the denominator structure of the readings `u = d/d_min` — the
rational-reading frontier. A statement of the right shape is one-directional, quantitative, and
strictly stronger than the target; `DoorFirstLap` had that shape and was false. Its replacement needs
a cap that survives §2's table, which the named cases put at `τ > 1.28` already.
