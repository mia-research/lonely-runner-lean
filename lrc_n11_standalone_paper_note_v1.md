# `n = 11` Standalone Paper Note

## Purpose

This note is the staging document for a short standalone paper proving the Lonely Runner Conjecture for `n = 11` (ten runners).

The point is not to touch the main `n = all` preprint. The point is to isolate the `n = 11` case as:

- a self-contained case study of the current analytic framework,
- the next natural finite prime target for a standalone paper,
- and a useful companion to existing finite certification work for teams pursuing computational approaches.

The intended output is a short paper, not another omnibus draft.

## Scope

For `n = 11`, the standalone paper should prove:

> For every gcd-1 tuple of `10` distinct positive integer speeds, there exists a lonely time for the stationary runner.

The paper should also record a stronger quantitative statement on the prime one-divisible branch:

> `x_0 >= phi(11) = 10`.

This stronger statement is already the natural output of the prime counting bridge.

## Why `n = 11` Is a Good Standalone Target

The case `n = 11` is structurally different from the recent low-composite cases `n = 8, 9, 10`.

- `n = 8, 9, 10` are low-`n` composite interval-deficit cases.
- `n = 11` is prime, so the hard branch is the one-divisible prime branch.
- The mechanism is not ad hoc chamber surgery; it is the lower-band counting bridge already present in the general framework.

So `n = 11` is a good case study because it showcases the analytic mechanism in a cleaner setting than the low-composite papers.

## Clean Normalization for the Standalone `n = 11` Paper

The standalone paper should avoid the notation drift that appears in some older working notes.

For the one-divisible prime branch at `n = 11`:

- there are `10` total runners;
- one runner is divisible by `11`;
- the remaining `9` runners are non-divisible.

The right normalization is:

1. Select one non-divisible runner as the free runner `M`.
2. Let `F` be the remaining `8` retained non-divisible residues in `{1, ..., 10}`.
3. Set
   - `L_0 = lcm(F)`,
   - `L = L_0 M`,
   - `gcd(M, 11 L_0) = 1`.

So the one-divisible `n = 11` branch is organized by the choice of the `8`-element fixed set `F`.

There are exactly

- `C(10,8) = 45`

such templates.

This is the correct template count behind the existing computational certificate.

## Branch Structure for `n = 11`

The standalone paper can be organized into three branches.

### Branch 1: No runner divisible by `11`

This is the prime Case-1 branch. The direct witness set `{jL : gcd(j,11)=1}` gives the result.

This branch is short and should be dispatched immediately.

### Branch 2: At least two runners divisible by `11`

This is the prime multiple-divisible branch. The divisible runners are transparent on the lower band except at the extreme floor states, and the general prime argument closes the branch analytically.

This branch is also short.

### Branch 3: Exactly one runner divisible by `11`

This is the only branch that needs real work in the standalone paper.

The right framework is the prime counting bridge:

- floor-0 miss set,
- safe fibres in `Period_1`,
- threshold `M_0`,
- and reflection.

This is where the analytic closure should be written cleanly.

## The Key Analytic `n = 11` Reduction

The finite prime Route-B search at `n = 11` is almost vacuous.

For the prime bridge, the threshold is

`M_0 = ceil(n^2 (n-1) / (L_0 (n-2)))`.

At `n = 11`, this becomes

`M_0 = ceil(1210 / (9 L_0))`.

So the problem is to understand the smallest possible `L_0` over all `8`-element fixed sets

`F subset {1, ..., 10}`.

### Exact minimizer for `L_0`

The minimum is

`L_0,min = 120`,

attained by

`F = {1,2,3,4,5,6,8,10}`.

This is sharp and has a clean proof.

### Proof sketch of `L_0,min = 120`

Any `8`-subset of `{1, ..., 10}` omits exactly two residues.

- If `7 in F`, then `lcm(F)` is divisible by `2`, `3`, `5`, and `7`, so `lcm(F) >= 210 > 120`.
- If `9 in F` and `7 notin F`, then only one other residue is omitted, so `F` still contains a multiple of `4` and a multiple of `5`; hence `lcm(F)` is divisible by `4`, `5`, and `9`, so `lcm(F) >= 180 > 120`.

Therefore any minimizer must omit both `7` and `9`, forcing

`F = {1,2,3,4,5,6,8,10}`.

Its lcm is

`lcm(1,2,3,4,5,6,8,10) = 120`.

So the exact minimum is `120`.

## Consequence for the Threshold

With `L_0 >= 120`, one gets

`M_0 = ceil(1210 / (9 L_0)) <= ceil(1210 / 1080) = 2`.

So Route B contains only the single value

- `M = 1`.

That is the correct analytic reduction for `n = 11`.

This is much better than a full template-by-template brute-force treatment.

## Closing the Residual Case `M = 1`

The lower-band estimate gives, in `Period_1`,

`safe(Period_1) >= L_0 (n-2)/n^2 - 2`.

At `n = 11`, `L_0 >= 120`, so

`safe(Period_1) >= 120 * 9 / 121 - 2 > 6`.

Hence `Period_1` contains at least

- `7` safe fibres.

By the reflection involution

- `k -> N-k`,

safe fibres in `Period_1` reflect to safe fibres in `Period_9`, giving another disjoint set of at least `7` safe fibres.

Therefore

- `x_0 >= 14 > phi(11) = 10`.

So the entire one-divisible branch at `n = 11` closes analytically.

## Companion Computational Certificate

Although the standalone paper should be analytic-first, the computation already in hand is valuable and should be packaged as a companion certificate.

Current exact finite certification:

- `45` all-distinct one-divisible templates at `n = 11`,
- `2115` finite checks,
- `0` violations.

Artifacts already exist in:

- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_d3_batch_summary_n7n11_v2.md`
- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_d3_batch_rows_n7n11_v2.csv`
- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_d3_batch_checks_n7n11_v2.csv`

This companion certificate should be framed as:

- an exact independent check of the normalized template family,
- not the primary proof.

That gives the paper two strengths:

- a clean analytic proof,
- and a reproducible exact computational backstop useful to others working on finite verification.

## Recommended Paper Shape

The standalone paper should be short.

### Section plan

1. Introduction and statement for `n = 11`
2. Arithmetic normalization
3. Prime branch without divisible runners
4. Prime branch with multiple divisible runners
5. Prime branch with exactly one divisible runner
6. Exact `n = 11` threshold reduction (`L_0,min = 120`, hence `M_0 <= 2`)
7. Closure of the residual `M = 1` case by `Period_1 + reflection`
8. Companion computational certificate summary

## Writing Principles

- Keep the paper independent of the `n = all` preprint.
- Do not import the full machinery unless it is actually needed.
- Make the normalization explicit from the start.
- Treat the computational material as certification, not as the proof engine.
- Emphasize the mechanism: at `n = 11`, the lower-band capacity already overwhelms the finite threshold.

## Immediate Next Step

Draft the standalone paper directly from this note, with the one-divisible branch as the centerpiece and the other prime branches kept short.
