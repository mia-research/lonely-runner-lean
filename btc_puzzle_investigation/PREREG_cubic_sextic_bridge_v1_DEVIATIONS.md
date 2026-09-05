# DEVIATIONS — `PREREG_cubic_sextic_bridge_v1.md`

**Date:** 2026-07-24 · Result: `RESULT_cubic_sextic_bridge_v1.md`

1. **The train/freeze/test protocol (prereg §2) was NOT executed — deliberately, in the safe
   direction.** The prereg anticipated *fitting* a rule for `j−k` on a TRAIN set, freezing it, then
   testing out-of-sample. On working the algebra, the correction turned out to be **derivable**
   (`c₃ = s·(e(π̄′)−e(ν′))`, from Eisenstein reciprocity plus the unit characters), so **nothing was
   fitted at all** — the rule was written down from theory and tested everywhere, including on the
   nominal TRAIN set. This removes the post-hoc risk the protocol existed to control; it does not
   remove it *by* the protocol. Recorded so the substitution is visible.

2. **`e_λ(ω) = (a+b+1)/3 mod 3` was tested, not assumed.** The prereg did not name this supplement.
   It is a classical identity (Ireland–Rosen Prop 9.3.3) which I could not recall with confidence, so
   it was verified as a candidate (**6000/6000**) rather than cited. Per
   `feedback_verify_root_system_against_defining_polynomial_2026_07_20`, a half-remembered classical
   formula is exactly what must not be repeated on trust.

3. **Arm B's first run was invalidated by resampling and was redone.** The initial sampler drew random
   `p` inside a fixed bit-width, so at 10 bits ~40 distinct instances stood behind 6000 draws; the
   free-rate and excess columns were duplicate-inflated (free rate `0.2447`, `z ≈ −14` against `1/3`).
   **Those numbers are void and are not reported.** Arm B was re-run by *enumerating* every `p` in
   three ranges with no repetition; the forced-rate claim (`1.0000`) was unaffected, since a duplicated
   instance still satisfies the identity.

4. **A float cube root was written into the first Arm B script and removed before the reported run**
   (`u ** (1/3)`), violating `btc_puzzle_investigation/CLAUDE.md`. Replaced with an exact integer
   binary-search cube root. No reported number depends on the float version.

5. **Arm B's excess prediction (prereg §3(iii)) is under-powered, not confirmed.** Predicted
   `+0.015/+0.008/+0.003` vs observed `−0.015/+0.018/−0.004`; consistent, but the observed excess's own
   `sd` (`0.016` at `N=877`) exceeds the predicted signal. Reported as unresolved, **not** as passed.

6. **`c₃`'s value distribution was not pre-registered** and is reported descriptively only
   (`(s₁,s₂)` diagonal `993/1036/971`). The *diagonality* is proved (B3); the *uniformity* is an
   observation with no test attached.
