# Direct symbolic handoff: protect the previous setter

2026-10-07. Implemented in `LRC/Spec/DirectHandoffN.lean`.

## Derived rule

Let b,c>0 be subject disparities (absolute pairwise differences; no physical
runner is set stationary). Suppose b has just reached its opening at r:

    b*r = K + 1/8.

Reading c is captured at r about its actual integer centre J:

    J - 1/8 < c*r < J + 1/8.

Its next opening is s=(J+1/8)/c. If b<=3c, Lean proves

    r < s,
    c*s = J+1/8,
    K+1/8 < b*s < K+7/8.

Thus this candidate clears BOTH readings. No future compatibility inequality,
return period, rationality assumption or interior old isolation is supplied.
The strict interior conclusion for b is derived, not assumed.

The proof is exact: 0<c(s-r)<1/4 and b<=3c imply
0<b(s-r)<3/4, the extent of b's newly opened clear band. The ratio condition
is scale invariant and the integer lap indices are arbitrary.

## What this forces in the actual cascade

`nextOpening_bands` derives J from current capture and identifies the new
instant with the existing cascade `nextOpening`, so J is not an invented
successful lap assignment.

`move_preserves_setter` handles the actual maximum-exit move, even with
several current blockers. If every currently captured c satisfies b<=3c,
that move keeps b clear in its current band. In particular, if d_min is the
least positive disparity and b<=3*d_min, the condition follows immediately.

`move_recapture_requires_small_setter` proves the converse obstruction:
if b is captured again after that actual move, the move has a currently
captured setter c with 3c<b. This restricts possible next setters directly
from the arrangement.

`return_exit_clears_pair` also shows: if the handoff b -> c immediately
recaptures b, then exiting that new capture of b clears c. Thus a local
b -> c -> b sequence cannot leave that same pair obstructing at the third
exit. Other readings may obstruct; the theorem does not force the global
maximum-exit cascade to choose b if another reading exits later.

## Boundary of the result

This is NOT a global decreasing-speed argument. The factor-three drop is
necessary for immediate recapture of the previous setter, not for every
handoff and not for a later return after intervening setters. No global move
budget or whole-arrangement isolation follows yet.

The ratio restriction is real: b=13/4, c=1, r=49/26, K=6, J=2 satisfies
the opening/capture conditions. At c's opening s=17/8, b*s=221/32 lies
in the capture slot below 7. The exact arithmetic is a Lean regression.

The direct next question is which OTHER readings can block the derived
opening, allowing their lap labels to change. The old two-sided-failure
example already demonstrates that checking only adjacent pairs cannot
replace that obligation. Accumulation and common-return arguments are not
requirements of this local direct rule.

## Verification and provenance

An independent Codex subagent derived/reviewed the geometric rule and
provided the exact ratio counterexample. No broad search or CPU-heavy job
was launched by the primary agent. The subagent's bounded Fraction check
also reconfirmed failure of a finite {2,3,5} immediate-repair menu; that
failure was already recorded in `bidirectional_replacement_v1.md`, so it
is not presented as a new reduction.

Targeted build passed. `experiments/nN/direct_handoff_audit_v1.lean` passed
all seven declaration checks and the exact regression; each theorem uses
only the SAME THREE standard axioms: propext, Classical.choice, Quot.sound.
Its recursive proof/type dependency audit prints 21 reachable project
constants. These use direct circle-band and cascade-opening facts, not
phase density, lower-order loneliness, a common-return theorem, or an
assumed uniform time bound. No full Spec gate was run.

Only the new module, audit input/output, and this report were added. No
existing source was changed; nothing was committed or pushed this turn.
