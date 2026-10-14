# The Theorem 11.1 arm — and the whole `n = 8` gap is `V` a power of 2

2026-09-07. Continues `ESCAPE_COVERAGE_v1.md`, which measured only the Theorem 10.1 arm
and named the 11.1 arm — about half the hard case — as never measured. Script:
`experiments/n8/escape_coverage_v2.py`.

**Pre-registration.** Extension of `PREREG_ESCAPE_COVERAGE_v1.md` with §2 (statistic),
§5 (constructive-witness control), §6 (exactness) and §§8–9 (scope, pre-commitments)
applying verbatim; the only change is the configuration fed to Theorem 5.2. **Deviation
recorded:** v1's spec declared Theorem 11.1 out of scope, and this arm is that
out-of-scope set measured under the identical design. The residual strata below
(`v₁`, `p`, `q`, and `r`) are the ones the spec fixed in advance.

## 1. The 11.1 arm is much weaker than the 10.1 arm

Exhaustive, `gcd = 1` 7-sets, speeds `≤ 16`, hard case, `gcd(p, L_G) > 1`:

| | arm size | (ii) Lemma 5.2-D | (iii) Thm 5.2-P | **coverage** | residual |
|---|---|---|---|---|---|
| Theorem 10.1 | 1 828 | 45.08% | 99.34% | **99.89%** | 2 |
| **Theorem 11.1** | **5 249** | 16.97% | 76.57% | **76.91%** | **1 212** |

Escapes (i) and (iv) fire **0** times on the 11.1 arm as well — consistent with, but still
not a proof of, the vacuity that *is* proved for 10.1 (`ESCAPE_COVERAGE_v1` §1).
Witness-verification failures: **0**; every firing escape produced a certificate verified
in exact rationals across all seven speeds.

**Combined at `B = 16`:** the hard case holds 7 077 tuples, of which **1 214 (17.2%)** are
uncovered. So our own general-`n` manuscript is unconditional at `n = 8` on **82.8%** of
the hard case — and essentially the entire gap sits in Theorem 11.1.

Reporting the 10.1 arm alone would have read as "99.99% covered". That figure is real and
it is not the picture.

## 2. The gap is `V` a power of 2  `[EMPIRICAL — exhaustive at `B = 16`]`

Residual by the fast speed `V`:

| `V` | 8 | 9 | 10 | 12 | 14 | 15 | **16** |
|---|---|---|---|---|---|---|---|
| arm | 6 | 20 | 35 | 231 | 330 | 1 365 | 3 262 |
| residual | 4 | 1 | 0 | 7 | 0 | 1 | **1 199** |
| uncovered | 66.7% | 5.0% | 0% | 3.0% | 0% | 0.1% | **36.8%** |

**1 203 of the 1 212 residual tuples — 99.3% — have `V` a power of 2.**

Equivalently, by the pre-fixed `p` stratum (`p` = largest prime factor of `V`, so `p = 2`
iff `V = 2^k`):

| `p` | 2 | 3 | 5 | ≥ 7 |
|---|---|---|---|---|
| arm | 3 268 | 251 | 1 400 | 330 |
| residual | **1 203** | 8 | 1 | 0 |
| uncovered | **36.8%** | 3.2% | 0.1% | **0%** |

And by `r = #{slow speeds divisible by p}`: `r = 1` 6.8% uncovered, `r = 2` **41.8%**,
`r = 3` **36.4%**, `r = 4` 8.7%, `r = 5` **0%**. The gap concentrates at `p = 2` with two
or three even slow speeds.

## 3. What this localises

At `n = 8`, the unconditional reach of our own general-`n` manuscript fails **essentially
only when the largest speed `V` is a power of 2**, and within that, at `r ∈ {2,3}`. Every
`p ≥ 7` case is covered, and `p = 5` is covered but for a single tuple.

That is a 2-adic obstruction, at `n = 8 = 2³`, in a manuscript that makes no primality
assumption on `n` anywhere. **A related 2-adic obstruction is already on record** —
`project_general_n_two_lineages` states the general-`n` blocker as `2φ(n)/n = 1`, which
holds iff `n` is a power of 2, with the `n = 2^k` branch of Corollary 11.0 as the target.
**These are not the same statement** — that one is about `n`, this one is about `V` — and
they should not be merged without a check. What is established here is only the second.

## 4. Scope

Exhaustive for `gcd = 1` 7-sets with speeds `≤ 16`; `B = 20` was running when this was
written. Compute-cap exclusions: 0. `n = 8`, integer speeds, threshold `1/8`. The
coverage figures are of **sufficient** conditions: an uncovered tuple is an instance where
the manuscript reduces to LRC(8) itself (Remark 5.2-G, L1104), not a counterexample —
every residual tuple in `ESCAPE_COVERAGE_v1` §3 had `M(T)` roughly double `1/8`.

## 5. Ledger

Decided cells 2 of 135 (unchanged; different line). `n = 8` is not proved. Established:
the 11.1 arm's coverage is 76.91% against the 10.1 arm's 99.89%; the combined gap is 17.2%
of the hard case; and that gap is `V = 2^k` to 99.3%. **The next object is Theorem 11.1's
pigeonhole when `V` is a power of 2** — that, and not the general hard case, is what an
analytic `n = 8` needs from this line.
