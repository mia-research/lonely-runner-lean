# Exact transport audit and next-return refinement

2026-10-07. Scope: the incoming-window / pinch-reflection / first-loss chain,
not a claim that the entire n=8 project is framework-native or complete.

## What was changed

Added `PeriodReflectionN.lean` without changing the target or any existing
route. At a currently feasible incoming band with time t>0, suppose H>0 is
an exact common return of its positive readings, E_i=d_i H integral. Set

    m = floor(t/H)
    u = (m+1)H - t
    lambda = u/t
    P_i = (m+1)E_i
    p_i = P_i - q_i - 1.

Lean proves 0<u<=H, 0<=p_i<E_i, and clearance in the p bands at u.
It also proves that those same p bands remain feasible in a right
neighbourhood of the deformation parameter, using the earlier feasibility
of the ORIGINAL q bands. No future successful labels are supplied.
Equality at the isolation threshold is allowed throughout.

The H bound applies at the current arrangement, not uniformly to every
nearby arrangement or successive pinch. H is a common return of the readings;
it must not be conflated with the slowest physical runner's rotation.

## Assumption audit

* `IncomingWindow.replacement_of_incoming`: old feasibility earlier and now
  is supplied. The endpoint time and future labels are derived. Rational
  current readings supply exact return data. Not arbitrary-real global transport.
* `MaximalWindowTransport.replacement_at_first_loss`: an old band is feasible
  initially and at some positive parameter, and fails at the target. Rational
  affine endpoints give a rational first-loss parameter. It derives replacement
  there, but does not establish initial outgoing feasibility or whole-path
  continuation by itself.
* `PeriodReflection.replacement_with_period_labels`: a current exact return
  is supplied explicitly. This bounds replacement labels at that arrangement
  independently of the old lap counts. It does NOT prove one finite set of
  labels across all arrangements.
* `PartialReflection.partial_reflected_right_inequalities`: the unreflected
  readings' strict clearance at the candidate time is still supplied (`hfree`).
  This is a genuine restriction of that sufficient lemma, not part of the
  loneliness target. It must not be presented as universally established.

## Two unresolved bridges

1. For arbitrary real targets, a pinch need not have a common return of ALL
   readings. A single irrational ratio rules out that hypothesis. Partial
   reflection avoids requiring a common return for bystanders, but currently
   assumes their successful placement. The next arrangement-specific task is
   to derive that placement or a different replacement from the actual seven
   readings. Merely assuming `hfree` would not close it. Boundary bystanders
   also need handling, not exclusion by a universal interior-margin premise.
2. Even on a rational-endpoint path, finite-stage rational replacements can
   in principle accumulate at a parameter before the target. Their current
   periods need not remain bounded. The new pointwise label bound is not a
   whole-deformation finiteness proof. No density or imposed time cap was
   inserted to close this gap.

## Verification

Targeted build of `PeriodReflectionN` passed. Four declarations audited:
the two new declarations and both `MaximalWindowTransportN` declarations.
All use only propext, Classical.choice and Quot.sound (three standard axioms,
not four new assumptions).

`experiments/nN/period_reflection_audit_v1.lean` also recursively walks proof
and type constants. Its output lists 25 reachable `LRC.*` constants for the
two transport roots, confined to PeriodReflection, MaximalWindowTransport,
IncomingWindow, PinchReflection and WindowPinch. No project stepping/density,
lower-order loneliness, Cover8 or bounded-witness deformation theorem occurs
in that audited dependency list. This checks actual proofs, not just imports.

Claude CLI review was attempted but stopped at its session limit. An
independent Codex subagent reviewed the mathematics read-only and confirmed
the local construction and both limitations. No heavy search was launched.

The global n=8 theorem remains open. Existing work was preserved; no commits
or pushes were made by this audit.
