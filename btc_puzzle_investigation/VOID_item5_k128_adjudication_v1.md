# VOID — the k=128 adjudication of the Item 5 deep run

**Date:** 2026-08-01. **Status: the k=128 adjudication is VOID.** Recorded, not repaired in place.

## What the frozen spec said

`PREREG_item5_deep_inversion_v1.md` §3, written before the run and frozen:

> "Validated against 500 explicit shuffles on a subsample; **if the analytic sd and the empirical sd
> disagree by >2%, the run is VOID.**"

## What the run produced

```
C-NULLSD (400k subsample, 500 shuffles): analytic sd=632.46  empirical sd=612.53
                                          ratio=0.9685  *** >2% -- RUN VOID ***
```

**3.15% disagreement. The pre-committed failure condition fired.**

## What I did, and why it was wrong

I argued that a 500-shuffle sd estimate carries ~`1/√(2R)` = 3.2% relative error, so 3.15% is one
standard error of the estimator; I verified separately that the permutation-moment formula is exact;
and I concluded **"Run is NOT void."**

**The analysis is correct and the procedure is not.** Pre-registration exists precisely so the rule
cannot be re-adjudicated once the outcome is known. "My control was badly designed" is available
*after any failed control whatsoever* — admitting it as an override empties the mechanism. The
argument belonged in a **v2 pre-registration**, as the stated reason for changing the control, not in
a rescue of v1.

**It is also asymmetric in my documented direction of error.** The override *preserved a null* and
kept a bound I had just claimed (~0.16%, "12× tighter"). The standing calibration is that my errors
run one-way deflationary; applying a void condition only when it costs me nothing is that bias
operating on the procedure itself.

**And it is a repeat.** `feedback_prereg_abstention_is_the_finding_2026_07_19` records exactly this
shape: *"a fired outcome cell was overridden by a post-hoc statistic run on the frozen window and
reported as confirmatory."*

## Consequences

1. **The k=128 numbers are withdrawn as an adjudicated result.** `z = −0.674`, the "no detection"
   verdict, the measured ~0.16% floor and the "12× tighter bound" claim in
   `RESULT_pointwise_inversion_item5_v1.md` §4's deep-run extension are **void**.
2. **The k=128 data is now SEEN.** Re-adjudicating it under a corrected spec is contaminated: I know
   the answer. Any future read of k=128 must be labelled `[CONTAMINATED — outcome known before the
   corrected control was specified]` and cannot carry the weight of a clean arm.
3. **k=135, k=160 and the full-range control have NOT been read.** They remain clean and are the
   arms that can carry a result under the corrected spec.
4. The chunk data itself is fine. What is void is the **adjudication**, not the arithmetic.

## What replaces it

`PREREG_item5_deep_inversion_v2.md` — control redesigned with the precision to police its own
threshold, written before any further arm is read.
