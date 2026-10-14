# A derived replacement-label rule at rational pinches

Completed 2026-09-30 (Australia/Brisbane). Local transport, not the global n=8 proof.

## Rule

At a rational pinch, let d_i>0 be the disparities, t>0 the old isolation time,
and q_i its clear lap labels. Choose a positive integer N such that every
8*N*d_i*t is integral. This exists by taking common denominators, and needs
no isolation search. Set

    lambda = 8*N-1,
    P_i = 8*N*d_i*t,
    q'_i = P_i-q_i-1.

Then every old clear phase is reflected exactly at t'=lambda*t. The old lower
boundary becomes an upper boundary and vice versa. The new labels are explicit.
The Python implementation chooses an lcm; Lean proves the common multiplier
exists by multiplying denominators, then constructs the integer labels.

## Why it moves past a pinch, rather than only checking the pinch itself

Use a local parameter h with d_i(h)=d_i+h*v_i and pinch h=0. Suppose the old
fixed lap window is feasible at h=0 and at some h=-delta, delta>0.
For every old active pairwise slack F_ij(0)=0, its slope B_ij is nonpositive.
The reflected pair, with its indices reversed, satisfies

    F'_ji(0)=F_ij(0),
    B'_ji = -lambda*B_ij >= 0.

Thus EVERY zero slack points into feasibility on the right, including all
simultaneous boundary constraints. Every positive slack persists for a small
positive interval. Taking a finite minimum gives e>0 such that the reflected
lap assignment is feasible for all 0<=h<=e. The proof also preserves positive
disparities and produces a positive isolation-band time there.

The general real-valued theorem exposes exact integer-period data as a
hypothesis. `rational_pinch_transport` DISCHARGES that hypothesis for rational
pinch disparities/time, with arbitrary real deformation directions. It does
not assume new-label feasibility or future isolation.

## Verification

- `Spec/PinchReflectionN.lean` builds successfully (8,264 jobs including replays).
- Exact tests: 459 AP-path pinches, seven with multiple active constraints;
  all replacements extend to the right.
- Another 100 deliberately constructed simultaneous-boundary cases pass.
- Largest selected multiplier in the AP tests: 3,695.
- Smallest verified right extension there: 2563561/659695430622.
- `experiments/nN/pinch_reflection_axioms_v1.lean` audits all 11 module theorems
  and three regressions. The exact two-boundary regression invokes the selector
  without providing replacement labels.
- Audit completed successfully: all 14 declarations depend only on
  propext, Classical.choice, and Quot.sound; no sorryAx remains.

## Critical limit: do not promote local transport to a global cover

On the previous wide example (0,1,50,105,106,136,189,199), start with the AP's
a=3 labels. Repeatedly choosing this reflection makes the following progress:

| Reflection count | Right parameter endpoint (approximate) | Digits in largest lap |
| --- | --- | --- |
| 0 | 0.7014451885794853 | 1 |
| 1 | 0.7020948180815877 | 4 |
| 2 | 0.7021876192254715 | 5 |
| 4 | 0.7021877205225211 | 9 |
| 8 | 0.7021877205363444 | 16 |
| 16 | 0.7021877205363444 | 32 |
| 31 | 0.7021877205363444 | 62 |

All computations use exact fractions; only the displayed endpoints are rounded.
This finite diagnostic is not a proof of infinite accumulation, but it shows
why the local theorem alone is insufficient as a practical global selector.
The earlier four-window cover already reaches s=1 for this same example.

Consequently we have removed the need to GUESS successful local replacement
labels at rational one-sided pinches. We have NOT proved that repeated use
reaches every target, nor excluded accumulation of switching parameters and
unbounded isolation times. Nor has exact-period reflection been extended here
to arbitrary irrational pinch data. A global coverage argument still remains.

No full Spec gate, commit, or push was performed for this work.
