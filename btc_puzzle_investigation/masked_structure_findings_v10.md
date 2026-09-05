# Masked-Structure — Findings v10: the decomposition step (S₄ rung)

**Date:** 2026-07-16 · the rung of index calculus where asymptotic ECDLP cost lives — not
`|Aut|`-bounded. Script: `decomposition_yield_v1.py`.

## Framing (the useful consequence of "that we know of")

Our levers reduce to two mechanisms, each with a *provable* ceiling: **symmetry** (bounded
by `|Aut(E)|=6`) and **single-object equidistribution** (`O(p^{-1/2})`, vanishing). So
scaling, if it exists, must live where *neither* reaches. The decomposition step of index
calculus (write target `R = P₁+P₂+P₃`, `Pᵢ ∈ F`, governed by Semaev `S₄`) is such a place —
its cost is not a symmetry factor. This is the honest place to look.

## Result — the symmetry lever does NOT propagate to the step that matters

| p | yield/heuristic (CM) | yield (non-CM) | β-inv/random | core‖flap yield | var/Poisson (CM‖non-CM) |
|---|---|---|---|---|---|
| 1009 | 0.998 | 0.992 | **0.98** | 0.992‖1.015 | 8.3 ‖ 12.4 |
| 4021 | 1.005 | 0.973 | **0.98** | 1.011‖0.983 | 18.7 ‖ 12.1 |
| 10009 | 1.009 | 1.004 | **1.00** | 1.000‖1.034 | 17.3 ‖ 12.3 |

1. **The β lever vanishes at the decomposition step.** v9: β-invariant factor base gave
   **1.5×** at the S₃ *relation-counting* step. Here, for S₄ *decomposition of a random
   target*, β-inv/random = **0.98–1.00**. The one symmetry lever we had does **not** carry to
   the step whose cost governs ECDLP — because a random target is not β-aligned with the base.
   This strengthens (does not merely re-null) the bounded-lever picture.
2. **No target-dependence.** The target's own geometric label (core vs flap) does not change
   its decomposition yield (equal to <2%). No "easy point" predictor from the ε-label.
3. **Generic yield.** Decomposition density = the heuristic `|F|³/|E|` for CM and non-CM alike.

## One real feature — curve-independent, and a genuine further line

The decomposition count is **over-dispersed**: variance 8–19× Poisson, i.e. some targets
decompose many more ways than others (a heavy tail). But it is **identical for CM and non-CM**
(non-CM flat ~12), so it is a generic property of a fixed factor base (pairwise-sum
correlation / birthday structure), **not** a CM signature, and it does **not** grow cleanly
with p. The ε-label does not predict which targets are easy.

**The line this opens (un-shut):** *some targets are genuinely easier to decompose* — a real,
exploitable-in-principle feature (a lever would be: predict easy targets cheaply). We showed
the ε-label doesn't predict it. **Whether any cheap curve readout predicts easy-target-ness
is untested** and is the natural next probe — it would be a target-selection lever independent
of the |Aut| ceiling. Prior: likely also generic (the over-dispersion looks like generic
factor-base correlation), but it is not ruled out and not measured.

## Scope / grade

VERIFIED at p ≤ 10009, F ~ √p/4, 300 targets, exact group law, matched non-CM control.
Not secp's p; `S₅⁺` (4+-point decomposition) untested; the easy-target predictability untested.
The finding — **the symmetry lever does not survive to the decomposition step** — is a
scoped, quantified negative for the index-calculus fence, not a wall claim.
