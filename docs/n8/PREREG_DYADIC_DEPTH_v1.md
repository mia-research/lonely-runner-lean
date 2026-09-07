# Pre-registration — is the 2-adic depth of the n=8 witness bounded?

**Status: PRE-REGISTRATION. Written before any depth datum beyond `V = 26` is seen.
Not a result.** 2026-09-07.

**`[PROVISIONAL — experiment-designer gate not run]`.** CLAUDE.md §2 makes
`experiment-designer` mandatory before a sweep. This session runs under a standing
directive not to spawn agents unless asked, so the gate did not run and this
specification is self-written. Per §2a the run may proceed provisionally under all
four conditions; conditions 1, 3 and 4 are discharged by this file and the result
tag. Condition 2 — the self-audit — is §6 below, and §6 names what a self-audit
cannot cover here.

## 1. The object

`T` = a set of 7 distinct positive integers, `gcd(T) = 1`.
`v = 2^e u` with `u` odd. Witness family: `t = a/2^k`, `a` odd, `k ≥ 3`.

**Depth** `κ(T)` := the least `k ≥ 3` for which some odd `a` gives
`‖v·a/2^k‖ ≥ 1/8` for every `v ∈ T`; `κ(T) = ∞` if no such `k` exists.

**Residual hard case** `R` := sets containing a multiple of 5, of 6, of 7 and of 8.
(Sets outside `R` are settled by `t = 1/q` for a missing level `q ≤ 7`, or by
`t = 1/8` when no speed is divisible by 8 — both one-line and already proved.)

## 2. The datum already seen, and therefore not evidence for this test

Exhaustive over `V ≤ 26`: `|R| = 133 612`, `κ` finite for all, distribution
`κ = 4: 79 774; 5: 49 101; 6: 4 606; 7: 131`; `max κ = 7`.
`experiments/n8/two_adic_witness_v1.py`. **This run is the hypothesis-generating
sample. It cannot also be its test.**

## 3. Hypothesis under test

**H1 (bounded depth).** `κ(T) ≤ K` for an absolute constant `K` on all of `R`.

## 4. Pre-committed test and outcome table

Sample residual-hard-case sets with speeds `≤ V` for `V ∈ {50, 100, 200, 400, 800}`,
uniformly at random subject to membership in `R` and `gcd = 1`, **20 000 sets per `V`**,
independent draws per `V`, computing `κ` exactly with `kmax = 16`.

| observed | pre-committed conclusion |
|---|---|
| `max κ` constant in `V`, no `κ = ∞` | H1 **survives**; record `K` and the largest `V` covered. Grade `EMPIRICAL`, scope = the sampled range. **Not** a proof and not a closure. |
| `max κ` grows with `V` | H1 **fails as stated**. Record the growth (fit `κ` vs `log V`); the reduction survives only as a `V`-dependent statement. |
| any `κ = ∞` at `kmax = 16` | H1 **refuted**. That set is a counterexample to the dyadic route; record it and check it is genuinely in `R`. |
| sampler yields `< 20 000` sets at some `V` | **ABSTAIN on that `V`**, recorded as owed with the reason. Abstention closes nothing. |

**Falsification condition, stated now:** a single `T ∈ R` with `κ(T) > 16`, or a
`max κ` that increases at every `V` step, refutes H1.

## 5. Power and what the test cannot do

`max` over a sample is a one-sided statistic: it can only under-report `κ`. A null
result ("`max κ = 7` again") is therefore weak evidence, and the pre-committed
conclusion above says so. The test has real power only against the **growth**
alternative, because a `κ` that grows like `log V` would show across a 16-fold range
of `V`. It has **no power** against a rare-exception alternative — a density-`10^-6`
family with large `κ` would be missed at 20 000 draws per `V`.

**Positive control (must fire).** Run the identical sampler with the threshold
raised from `1/8` to `1/7`. LRC(8) does not hold at `1/7`, so sets with no dyadic
`1/7`-witness must appear. If the control reports zero failures, the harness is
broken and the main result is void.

## 6. Self-audit — what is NOT covered

Per §2a the mechanical layers (statistic, exactness, does-the-control-fire) are
discharged by the artifact; the frame layers are not, and isolation is the mechanism
for those. **Uncovered here:**
- **object/disjointness** — whether `R` as defined is the right residual class, and
  whether the sampler's uniform-subject-to-`R` draw over-represents small odd parts.
- **matched-control adequacy** — the `1/7` control tests the harness, not the frame.
- **scope** — whether `κ` bounded on `R` would actually give an analytic proof, or
  only move the difficulty into "which `a`".
These three are the layers a self-audit cannot discharge, and they are owed.
