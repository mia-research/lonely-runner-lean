# DEVIATIONS — `PREREG_ord_n_structure_v1.md` + `PREREG_ord_n_mechanism_v1.md`

**Date:** 2026-07-24 · Result: `RESULT_ord_n_residue_structure_v1.md`

## Deviations from `PREREG_ord_n_structure_v1`

1. **Added an unregistered family experiment.** The prereg tested H-sextic only at secp (Q1–Q5 are
   single-instance). Testing whether CM *forces* `p` into the index-6 subgroup requires a family, so a
   `j=0` family sweep (`p ≡ 1 mod 3`, four odd-order twists, `n` prime) was added after Q1–Q5 ran.
   **This is an extension, not a re-analysis of the frozen window** — new data, new object. The
   prereg's confirm/falsify criteria for H-sextic were applied unchanged.
2. **The reciprocity half of H-sextic's confirmation criterion was not executed as written.** The
   prereg required reproducing the sextic symbol "by the reciprocity computation from `t` alone."
   The family test falsified the cubic half first (`z = +0.27`, control `0.3325`), which made the
   Eisenstein computation moot. **Recorded as not-run, not as passed.**
3. **A self-test in the OOS script failed 29/5125** (`(p/n) == ((1−t)/p)` for `n ≡ 1 mod 4`) and was
   **not** chased down, because the corrected-sampler run superseded that script entirely and the
   identity is not load-bearing for any claim in the result file. **Open, unexplained, and small.**
   It is listed here rather than dropped.

## Deviations from `PREREG_ord_n_mechanism_v1`

4. **Hypothesis (i) was falsified and the mechanism was repaired mid-run.** The prereg split
   instances into a SMALL branch (`t ≥ 2`, `p mod n = t−1`) and a LARGE branch (`t ≤ 0`), and
   predicted the LARGE branch would sit at `0.500`. It came in at `0.5849` (`z ≈ +8`). Cause: a
   bookkeeping error of mine, **not** a second mechanism — `p ≡ t−1 (mod n)` holds in *both* branches,
   and since `n ≡ 1 mod 8` gives `(−1/n) = +1`, the forcing applies to `|t−1|` throughout. The
   corrected, unified statistic was then run.
   **This is a post-hoc repair of the hypothesis.** Its protection is that the repaired law is not
   fitted: it predicts rate **exactly** `1.0000` (falsifiable by a single counterexample) and a
   parameter-free excess, and both held — `0/1546` violations, predicted-vs-observed excess `0.93`,
   `1.20`, `0.66` where statistics allow. Had the repair been a fit, the forced cell would have come
   back at ~0.9, not at 1.0000.
5. **Cell counts were not pre-committed.** Sample sizes per bit-length were chosen for runtime, and
   at 40–64 bits the forced population falls to `5, 1, 0` instances, so those rows confirm the
   *density* law but carry no independent weight on the *rate* law.

## Not a deviation, recorded to prevent a re-run

6. The `4p = L²+27M²` sampler was suspected of restricting the family to primes where 2 is a cubic
   residue. **It does not** — see `RESULT_… §5`; an independent Cornacchia sampler reproduced the
   family instance-for-instance. Do not re-open this.
