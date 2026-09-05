# DEVIATIONS — `PREREG_bridge_dichotomy_v1.md`

**Date:** 2026-07-24 · Result: `RESULT_bridge_dichotomy_v1.md`

1. **Four Arm-2 discriminants returned no instances, and the prereg had no provision for it.**
   `D = −7, −8, −15, −20` gave `< 40` instances in v1. This was **not** treated as a null: the cause
   was derived and then verified as **(D1)** — prime order requires `D ≡ 5 (mod 8)` (2 inert),
   `0` odd orders in `67,477` twists for the excluded classes. The prereg had anticipated the blocker
   only for `D = −4` (Arm 5, via the 2-torsion point); (D1) is the general law it is a case of. This
   **generalized the prereg's Arm 5 after seeing that arms were empty** — recorded as post-hoc.

2. **The prereg's secondary statistic was NOT run.** §2 named "uniformity of `(j−k) mod ℓ` under the
   frozen labelling `ζ_q := g^{(q−1)/ℓ}`" as a secondary. It was dropped: for `ℓ ≥ 5` there is no
   canonical alignment between `μ_ℓ ⊂ F_n` and `μ_ℓ ⊂ F_p`, so an arbitrary per-instance labelling
   would scramble a genuine relation and the statistic could not distinguish "no bridge" from "wrong
   labelling." **Reported as not-run, not as passed.** The pre-registered *primary* (generator-free
   2×2) carries every verdict, as specified.

3. **A power column was added that the prereg did not specify.** Nulls are quoted as `z ≈ 0.62·√E`
   against an Arm-1-sized effect. Added because the prereg's falsification clause ("association at the
   Arm-1 effect size") is meaningless without it — v1's `ℓ=11,13` rows had `E = 4.9` and `2.8`, i.e.
   `1.4σ`/`1.0σ` power, and would have been reported as nulls while testing essentially nothing.
   **v1's `ℓ=11,13` rows are therefore superseded and not reported as results.**

4. **Sampling method changed between v1 and v2.** v1 enumerated primes with an `O(√p)` search for
   `4p = t²+|D|v²`; v2 uses Tonelli–Shanks + Cornacchia–Smith with random primes at fixed bit width
   (30 bits for `ℓ=3`, 28 for `ℓ≥5`). Justification: v1 could not reach the `N` needed for power. The
   positive control agrees across both (`ratio 1.62` at `N=3000` enumerated, `1.69` at `N=6000`
   sampled), which is the check that the change is harmless.

5. **Multiple comparisons were not pre-corrected.** Ten association tests were run. Two nominally
   small p-values appeared in v1 (`D=−163`: `389/10001`; `D=−3, ℓ=7`: `366/10001`) — both **vanished**
   at higher power in v2 (`19834/20001`, `14529/20001`), which is the behaviour expected of noise, but
   no formal correction was applied and none was pre-registered.

6. **Not a deviation, recorded to prevent re-running:** `D = −4, −7, −8, −15, −20, −24, −40` and every
   other `D ≢ 5 (mod 8)` **cannot** yield prime `n`. Do not re-attempt association tests there.
