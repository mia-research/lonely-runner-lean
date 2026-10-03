# Bounded Claude task: earlier-capture exceptions

Purpose: supply exact discovery data to the symbolic/Lean proof work. Do not
claim a universal theorem from a population. Do not edit Lean, the running log,
other experiments, or Git history. Return a report; any new script/output must
have a new `claude_capture_exceptions_v1` name. No background runs or new agents.

## Known mechanism

Positive subject disparities, positions in eighths. Setter c exits lap k at
R=(8k+1)/c. Reading b is captured on lap L there exactly when

    (8L-1)c < (8k+1)b < (8L+1)c.

If also (8H-1) <= G*c, then the two lower edges give

    (8J+1)/b <= G*(8J+1)*(8k+1)/((8L-1)*(8H-1)),

for H,L>=1. `MappedCascadeRulesN.lean` proves this; it does not prove these
relationships always occur. The mapped example uses G=9,k=4,H=L=6,J=11,
giving 89/b <= 26433/2209 < 12.

## Task A: exact complement

Check the algebra and retain equalities. Failure of the first closed lower
edge is G < (8H-1)/c. Failure of the second is (8k+1)/c < (8L-1)/b.
These mean the proposed state is BEFORE that entering edge. They do not imply
clearance: it could be an earlier captured lap. Explain which earlier lap is
actually occupied, including boundary positions 1 and 7.

## Task B: bounded mechanical extraction

Use the existing exact `cascade_path_map_v1.path` logic, with a hard limit of
200 moves per arrangement; report truncations separately. Use Fraction, not
floating point. Cap the initial task at 200 input arrangements drawn from
existing late examples and perturbations; do not start an exhaustive tree.

For each final opener b on lap J, inspect actual earlier states G and actual
exit-to-capture links c,k -> b,L. Record H from c's position at G, not a lap
chosen to make the bound attractive. Keep the complete inequalities and exact
positions. Report:

1. The strongest bound from observed pairs, compared with the actual landing.
2. Cases with no positive-H/L pair, cases with pairs but a weak bound, and
   cases where a bound is useful. These must not be conflated.
3. Small exact witnesses in each exceptional class and which of the two
   lower-edge hypotheses fails for any proposed replacement pair.
4. Candidate alternative readings or earlier windows with their entire
   seven-reading clearance inequalities, not just pair separation.

Avoid classifying arrangements by a claimed universal landing. This is a
bounded survey of observed histories, intended to suggest speed-only rules.
Do not treat reference-grid equivalence as preservation of later paths.

## Separate proof target being handled in Lean

`FiniteWindowContinuationN` treats accumulation: a finite set of fixed lap
windows has closed parameter coverage. Uniformly bounded witness times along
one fixed bounded-speed affine path imply a finite label set. This prevents
loss at a limit, but neither supplies a rightward replacement nor proves the
required witness-time bound. No mechanical search on that target is needed.

## Access note

The local Claude CLI was attempted on 3 October 2026 with tools disabled for
an algebra check. It returned: organisation has disabled Claude subscription
access for Claude Code. No Claude analysis or search ran through that attempt.
