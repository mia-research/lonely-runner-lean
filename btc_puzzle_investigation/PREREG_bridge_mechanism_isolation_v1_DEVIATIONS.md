# DEVIATIONS — `PREREG_bridge_mechanism_isolation_v1.md`

**Date:** 2026-07-24 · Result: `RESULT_bridge_mechanism_and_constant_v1.md`

1. **H-constant's sub-claim (iii) failed and the hypothesis was repaired post-hoc.** The prereg's
   anti-fit guard fired as designed: `e(ν′) ⊥ e(π̄′)` is **false** (6 of 9 joint cells), so the
   pre-registered model is **rejected**, and `5/9` is *not* graded on the strength of (v)/(vi) passing.
   The replacement laws (E1)–(E4) were found **after** seeing the empty cells. Their protection is that
   each is a **biconditional or exact congruence with 0 violations in 12000**, not a rate — but they
   are **post-hoc and confirmed on the same sample that suggested them**. An independent-sample retest
   of (E1)–(E4) was **not** run and is owed.

2. **A null was mis-scoped in the session summary and is corrected in the result file.** The matched
   control was first described as "nothing there." That is an unscoped negative of the kind
   `feedback_conditional_negatives_phrasing` and `feedback_negative_bias_enlarge_nulls` forbid.
   Corrected to a **bound**: shape-generated association `< ~1.06` ratio at 3σ, scoped to 30-bit
   primes / this `Δ` multiset / this statistic / `N=17305`. The result file carries the bound, not the
   absence.

3. **A consistency flag was found and is reported rather than absorbed.** `P(s=0)` runs below `1/3` in
   both samples (`z = −1.92` combined). The prereg did not anticipate this and set no threshold for it.
   It is reported as unresolved, and (v)/(vi) are downgraded to `[CONSISTENT, not verified]`
   accordingly — rather than being reported as passes, which the raw p-values would have permitted.

4. **The matched control reached `N = 17305`, not the `20000` targeted** (loop cap), so its power
   (`27.5σ`) is slightly below the CM arm's (`29.5σ`). Both far exceed the effect size at issue; noted
   for completeness.

5. **P3 sampled `h=2` only.** The prereg said "`h>1`"; every discriminant available in the class-number
   tables I used at `D ≡ 5 mod 8` and modest size has `h=2`. `h ≥ 3` is **untested**, and the (M2)
   claim is scoped to `h=2` in the result file.

6. **Two scripts share code by `exec`-ing a prefix of `cubic_bridge_v1.py`.** Fragile but the imported
   region is the `ℤ[ω]` machinery already validated by controls K0/K1/K3 in
   `RESULT_cubic_sextic_bridge_v1`; those controls were **not** re-run in v2 of this arm.
