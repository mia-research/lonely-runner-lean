# Compatible obstructions and a complete replacement family

3 October 2026. Modules: `CoreWindowCompatibilityN.lean` and
`CoreWindowReplacementExampleN.lean`.

## General symbolic compatibility

For a finite nonempty collection of positive-time core windows [L_i,U_i],
prescribe nonnegative integer capture labels K_i. An inserted positive speed
V can swallow all of them on those labels exactly when

    (K_i-1/8)*U_j < (K_j+1/8)*L_i    for every i,j.

This includes i=j. It is necessary and sufficient, not just a rejection test.
It eliminates V by comparing the open forbidden speed intervals

    (K_i-1/8)/L_i < V < (K_i+1/8)/U_i.

If one cross inequality fails, that proposed label pattern is impossible.
If all finitely many possible patterns are impossible, some core window must
survive insertion. A single rejected pattern does not reject other labels.
The finite-label bounds come from `CoreWindowInsertionN`; no external speed
cap is needed for a fixed positive-width core window.

## Complete example: the compatible case now has a derived replacement

Fix the six readings

    1, 73/25, 99/25, 253/50, 321/50, 697/100.

Let V range over EVERY real speed at least 697/100. Use R=8t. The three early
core-clear windows are

    [1,700/697], [425/99,3100/697], [150/23,4700/697].

Lean verifies clearance throughout all three intervals. If any interval is
not swallowed by V, it supplies a full isolation. If all three are swallowed,
their six endpoint inequalities force, without a label enumeration,

    (K_1,K_2,K_3) = (1,4,6),
    3069/425 < V < 34153/4700.

Derivation: the third interval's width first forces V<10; the first interval
then forces K_1=1. That tightens V sufficiently to force K_2=4, then K_3=6.
The second lower edge and third upper edge give the displayed residual interval.

The core is also clear throughout

    [9,6300/697].

The core's lap labels there are (1,3,4,5,7,7). Every speed in the residual
interval is rescued inside this later window:

- If 65 <= 9V, use R=9.
- Otherwise use R=65/V, V's lap-8 exit.

The proof verifies 9 <= R <= 6300/697 and 65 <= V*R <= 71. Thus V and every
core reading are clear together. Endpoint equality is allowed.

`all_largest_insertions` combines the branches and proves isolation for this
fixed core plus every real V>=697/100. This is an infinite parameter family,
not just the original V=363/50, and no numerical certificate is used.

## What remains

The compatibility theorem is general. The explicit replacement family fixes
the six core ratios. It does not prove that arbitrary cores possess these
three early windows or this later one. The global next step is to derive the
corresponding core-window families and replacements as those six ratios vary.
Common rescaling does not create a new mechanism; varying core ratios can.

This establishes the requested pattern in one complete branch:

    early core windows -> finite joint obstruction -> forced replacement.

It does not establish global order-eight loneliness.

## Delegation and verification

Claude was asked to compute the exact residual speed intervals and late-window
coverage read-only. It declined the task and supplied no mathematical result.
The residual interval was independently calculated with Fraction arithmetic;
the implications and the entire rescue family were then proved in Lean.

Targeted build and axiom audit of both modules (12 declarations, including
three data definitions), plus two regressions. No full Spec gate. No commits
or pushes; existing modules from previous turns remain untouched.
