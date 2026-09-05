# CT.1 Selection Rule: `min-e`

Date: 2026-04-12
Status: targeted computational result; partially superseded later the same day

## Correction note

This note captured an important first signal, but the raw `min-e` rule is **not** the final selection rule.

A later larger-speed prime sample produced a counterexample to the universal `min-e` claim. The corrected follow-up is:

- [ct1_selection_proof_attempt_v1_2026-04-12.md](/Users/trentpalelei/Desktop/Math%20Ex/reports/ct1_selection_proof_attempt_v1_2026-04-12.md)

What survives from the present note is the broader conclusion that the prime branch should be attacked by a **selection theorem** rather than by a universal statement over all thin residues.

## 1. Question

After the `CT.1` pivot, the real question became:

> if the prime dropped-unit base fibre `b_0=L/n` is fully covered, is there a **canonical choice** of multiplicity-1 residue that tends to produce the simple chain?

The strongest current answer is:

> choose the multiplicity-1 residue whose sole-cover runner has the **smallest actual speed**.

I will call this the `min-e` rule.

## 2. Tooling

New scan script:

- [ct1_prime_selection_rule_scan.py](/Users/trentpalelei/Desktop/Math%20Ex/tools/ct1_prime_selection_rule_scan.py)

This script:

- enumerates or samples prime dropped-unit tuples,
- restricts to the full-cover base-fibre regime,
- selects a thin residue by a chosen rule,
- and checks whether the selected start is **good**:
  - depth `0`, or
  - depth `1` with no sustaining companion re-add before the first safe fibre.

## 3. Main result

Among simple lexicographic rules on the thin-residue features, the rule

> `pick the thin residue with minimal sole-cover runner e`

is already perfect on the exhaustive small-prime data.

### Exhaustive checks

- `n=5`, speeds `<= 15`:
  - full-cover cases: `147`
  - `min-e` successes: `147/147`
  - depth profile under `min-e`: `147` depth `0`, `0` depth `1`

- `n=7`, speeds `<= 14`:
  - full-cover cases: `420`
  - `min-e` successes: `420/420`
  - depth profile under `min-e`: `416` depth `0`, `4` depth `1`

So on the exhaustive prime regime currently available, `min-e` has **zero failures**.

## 4. Stronger random support in the hard regime

I also sampled directly **conditioned on full-cover cases**.

Results:

- `n=11`, max speed `132`, `200` full-cover samples:
  - `min-e` good in `200/200`
  - depth profile: `199` depth `0`, `1` depth `1`

- `n=13`, max speed `156`, `100` full-cover samples:
  - `min-e` good in `100/100`
  - depth profile: `99` depth `0`, `1` depth `1`

- `n=17`, max speed `204`, `50` full-cover samples:
  - `min-e` good in `50/50`
  - depth profile: `50` depth `0`, `0` depth `1`

So the current support is not merely “some start works.” It is:

> the very simple start rule `min-e` works in every tested full-cover prime case.

## 5. Structural effect on the hard `n=7` family

The four exhaustive hard tuples at `n=7` were:

- `(2,6,7,8,9,10)`
- `(2,6,7,8,10,11)`
- `(2,6,8,9,10,14)`
- `(2,6,8,10,11,14)`

Under the `min-e` rule, all four collapse to the same chosen start profile:

- sole-cover runner `e^* = 6`,
- chosen residue `r^* = 1`,
- depth `1`,
- first safe residue later becomes `6` or `5` depending on the decoration.

So the hard family becomes much more uniform after selection.

## 6. What this suggests analytically

This is the cleanest theorem target currently on the table:

> **CT.1-S (selection version, candidate).**
> In the prime dropped-unit branch with fully covered base fibre, let `r^*` be a multiplicity-1 residue whose sole-cover runner has minimal actual speed among all multiplicity-1 residues. Then the chain starting from `r^*` reaches a safe fibre without a sustaining repair chain.

This is much narrower than the earlier universal `CT.1`, and computationally it is far better supported.

## 7. Important caveat

This does **not** yet prove the rule.

It also does **not** show that every start chosen by small `q`, or by HIGH/LOW position, or by canonical missing residue, behaves well. The good news is that we no longer need that.

The current evidence says that the right analytic proof should be a **selection theorem**, and `min-e` is the best concrete selection rule found so far.

## 8. Recommended next move

The next proof pass should try to explain why `min-e` is privileged.

The most promising line is:

1. take the selected thin residue carried by the smallest sole-cover runner;
2. analyze how any transfer to a larger runner can occur;
3. show that this larger-runner handoff cannot sustain a repair chain before a safe fibre appears.

That would convert the current experimental rule into the first real analytic closure candidate for the prime dropped-unit branch.
