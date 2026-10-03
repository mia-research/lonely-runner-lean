# Finite-window continuation and the remaining replacement target

3 October 2026. New Lean module: `FiniteWindowContinuationN.lean`.

## What is proved

Along a fixed affine deformation, a fixed lap vector is feasible precisely
when all its pairwise lap-window inequalities hold. Each inequality is affine
in the deformation parameter. Thus its feasible parameter set is closed;
finitely many such lap vectors also have closed combined coverage.

`endpoint_of_finite_coverage` proves that coverage of every parameter in
`[l,r)` by finitely many affine systems implies coverage at `r`. The selected
system need not eventually stabilise. `endpoint_lap_window` connects this
directly to actual closed clear bands and produces a positive endpoint time.

`endpoint_of_bounded_witnesses` removes the need to supply a finite candidate
list manually. Its explicit assumptions are:

- Positive endpoint disparities `a_i,d_i` with both at most `D`.
- For every `s` in `[0,1)`, a positive isolation-band witness time at most `T`.
- A natural number `N` with `D*T <= N`.

Every intermediate disparity is at most D. Its witness satisfies

    q_i + 1/8 <= d_i(s)*t <= D*T <= N.

Hence `q_i < N`; all lap vectors belong to a finite product of bounded natural
labels. The theorem obtains a positive endpoint clear-band witness from this
finite family. It does not assert the endpoint time returned remains <= T.

The bounds can depend on the fixed target. There is no requirement here for a
single lap cap across all arrangements. There is also no assertion that the
needed witness-time bounds have been proved for arbitrary targets.

## What this does NOT prove

- It does not supply coverage for the parameters before the endpoint.
- It does not supply a replacement beyond a pinched endpoint.
- It does not prove a universal time bound, global order-eight isolation, or
  that the earlier-capture product rule applies to every arrangement.

An affine constraint `1-s >= 0` is a simple regression: it survives at s=1
with zero slack and fails at every s>1. Thus closure at a limit and rightward
replacement must remain separate claims.

This reduces the accumulation concern conditionally: on any stretch where we
can derive bounded witnesses, arbitrary switching cannot erase isolation at
its limiting endpoint. The replacement/exhaustiveness obligation remains.

## Exact earlier-capture complement to investigate next

For positive b,c, G>0 and positive H,L, the product rule needs

    8H-1 <= G*c,
    (8L-1)*c <= (8k+1)*b.

Its complement splits into two strict cases:

    G < (8H-1)/c,
    (8k+1)/c < (8L-1)/b.

In words, c has not reached the proposed H entering edge at G, or b has not
reached the proposed L entering edge when c exits. Neither means that reading
is clear: it may occupy an earlier captured lap. The next mechanism must use
that actual earlier label and verify the other readings' margins.

The bounded extraction task is in `claude_capture_exceptions_brief_v1.md`.
Claude CLI execution was attempted but blocked by organisation subscription
policy; no Claude results were obtained. No authentication settings changed.

## Verification scope

Targeted build and declaration-wide axiom audit for this module, plus three
regressions. No full Spec gate, no commits, no pushes. Existing files and other
sessions' edits are unchanged.
