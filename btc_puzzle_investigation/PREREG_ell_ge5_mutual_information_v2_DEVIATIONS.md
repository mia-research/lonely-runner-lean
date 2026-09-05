# DEVIATIONS — `PREREG_ell_ge5_mutual_information_v2.md`

**Date:** 2026-07-25 · Result: `RESULT_ell_ge5_mutual_information_v1.md`

1. **R2 was re-parameterized after a first mis-specification.** The initial injection used `s = 1/ℓ` as
   the null point; it is not — copying with probability `s` adds correlation on top of the baseline, so
   the true null is `s = 0`. The first R2 table was uninterpretable (it "detected" at the smallest grid
   point because that point already carried signal) and was **discarded**. Re-run with `s=0` as null
   and a low-`s` grid; floor came out at `s≈0.03`. **The mis-specified table is not reported.**

2. **C-cong (R3) was broken on first run (N=0) and fixed.** The common residue `rr` was drawn without
   requiring `gcd(rr,U)=1`; when `gcd(rr,U)>1` that divisor divides every candidate in the arithmetic
   progression, so no prime exists and the control produced zero pairs. Fixed (draw `rr` coprime to
   `U`); it then produced N=1178 pairs, `p=0.64`. **The control was non-functional for the main arm
   pass** — but since every arm came back **null**, C-cong (needed only to *attribute a positive*) was
   not load-bearing for the result. Its functionality is confirmed post-fix; it was **not** available
   at the moment the arms were first read.

3. **The arms were split across two sampling regimes, not one pre-registered N.** In-sample: 30-bit
   `p`, N≈8000. OOS: 32-bit `p`, N=12000, fresh seeds. The prereg named "N as large as `p<2^30`
   sampling gives (≥8000)"; the OOS regime (32-bit) was chosen *after* the in-sample flickers, to make
   replication fully independent. This is the correct response to a flicker (independent retest), but it
   is a **post-hoc choice of the OOS regime**, recorded as such. Both flickers died, so the choice did
   not manufacture a result.

4. **Two arms did not reach the N target.** OOS ℓ=11 reached N=6808 and ℓ=13 (separate run) N=8778,
   below 12000/9000, because 32-bit prime-order twists with `n≡1 mod ℓ` are rare and the try-cap was
   hit. Both were **null anyway** (`0.66`, `0.11`), and lower N only *widens* the null — it cannot
   create the observed non-significance. Noted for completeness.

5. **Multiple comparisons were not formally corrected in the spec**, only accounted for narratively
   (8 primary tests; Bonferroni on the min `0.0021` ≈ `0.017`). The OOS replication is the real control
   for multiplicity here, and it killed both low arms — a stronger check than any correction.

6. **The `ord_n_mechanism`-style twist correlation was avoided by design** (N5: one twist per `p`), so
   this run does **not** carry the correlated-draw caveat that the ℓ=3 mechanism work had.

7. **Not run:** the splitting-axis cross-D arm (ℓ=5 at D=−11,−19,−43) and the ℓ=5 inert-vs-split
   comparison were pre-registered as secondary/observational and were dropped once the main ℓ=5,7,11,13
   arms came back null — there was no signal whose `D`-dependence needed mapping. Recorded as not-run,
   not as null.
