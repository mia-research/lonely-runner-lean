# N1 — the ½-saturation "anomaly with no account": both halves now have one

**Date:** 2026-07-30. Script: `n1_saturation_residual_v1.py` (+ `.json`).
**Grade: `[EMPIRICAL — measured, 34 primes, p ∈ [127, 6199]]`.**
⚠ Same user-authorised gate relaxation — **no `experiment-designer` prereg.**

---

## 0. The target

`POSITIVE_FINDINGS_MASTER_v4.md` M3/N1 — **the record's one measured anomaly with no account**,
listed OPEN, *"twice attempted, twice not closed"*:

> Saturation = `max_a |V(a)| ÷ (dim·√p)`, `dim = 4`. `χ₂(y)` gives **0.470** `[0.432–0.500]`
> (6 primes, "converging to ½") while the **same-dimension** additive `bx+cy` gives **0.876** —
> a **1.86× gap at identical dimension**.

Two separable questions. The record conflated them; they have different answers.

## 1. Q1 — why ½ and not 0.876? The mechanism is ON FILE, and MASTER_v4's status is STALE

`ANALYSIS_n1_cap_anew_channel_kronecker_route_v1.md` (**2026-07-26**) already supplies it: the 120°
lock `α₂/α₁ = ζ₃` gives `|1 + ζ₃| = 1` **exactly**, so `V = 2i·Im(α(1+ζ₃))` and only **2 of the 4**
eigenvalues carry independent weight ⇒ ceiling `2√p` = **½ of `4√p`**, against 4 genuinely free
eigenvalues for `bx+cy`. **⇒ `½ = 2/4`, and the 1.86× gap is `0.876/0.470`.**

**MASTER_v4 is dated 2026-07-20 and therefore predates its own answer.** Not re-tested here; flagged
because the OPEN status is stale, not because the mechanism is new. *(This is a second instance of
the failure mode logged on 2026-07-26: "item 2's verdict is 2026-07-24; the 120° identity is
2026-07-25 — the two files never meet." Same pattern, different item.)*

## 2. Q2 — is the sub-½ deficit a REAL residual? **No: it is finite-size, and the null's own slope proves it**

If the 120° lock is exact, `max|u|` (`u = V/(2i√p)`, `|u| ≤ 1`) is the maximum of `L = (n−1)/6` draws
from the semicircle marginal. The semicircle density vanishes like `√(1−u)` at the edge, so
`1 − max|u| ~ c·L^{−2/3}` and the deficit `½ − saturation` must decay as `p^{−2/3}`.

**Measured, 34 primes, `p ∈ [127, 6199]` (a 49× range):**

| quantity | value | prediction |
|---|---|---|
| log-log slope, **null** deficit vs `p` | **−0.663** | **−2/3 = −0.667** ✅ |
| log-log slope, **data** deficit vs `p` | −0.807 | (see caveat) |
| ratio `def_data / def_null`, mean | 0.748 | 1 if pure finite-size |
| ratio, small-`p` half → large-`p` half | 0.766 → 0.730 | no drift |

The saturation runs 0.4785, 0.4757, 0.4549 … 0.4983, 0.4998, 0.4993 — **reproducing the record's
`[0.432–0.500]` at its small primes and converging to ½ at the larger ones.**

**⇒ The `0.470` is a finite-size artifact of a max statistic, not a property of the curve.** The null
built from the 120° lock alone predicts a deficit of the same order and the correct decay exponent
across 49× in `p`.

⚠ **Caveat on the data slope.** `−0.807` is not robust. `1 − max|u|` is a min-type statistic with
enormous relative scatter (`ratio` sd 0.578; the data deficit spans 0.00016 to 0.045), and single
points near zero on a log scale dominate the fit. The **null** slope is the calibrated quantity here;
the data slope should not be read as a distinct exponent.

## 3. The one residual, and why it is NOT live

Data sits slightly closer to the cap than the null: per-prime `z` of `max|u|` has mean **+0.378**,
**pooled +2.20**, **24/34 positive**.

**This must not be reported as a finding, and the reason is in this session's own record.** It is the
**same statistic** (`S3_max` vs the semicircle null) that `RESULT_semicircle_null_and_verification_v1.md`
§1 already flagged in-sample (14/17, pooled +2.06) and **retested out-of-sample on 15 fresh primes:
pooled +0.30 (semicircle) and +0.54 (pooled-empirical-marginal control), 8/15 signs.** The 34-prime
set here **contains the 17 discovery primes**, so its pooled `z` is inflated by construction.
Restricted to the 7 primes here that were OOS (`5107 … 6199`): **4/7 positive** — consistent with the
null. **Dead, and re-reporting it would be counting the discovery sample twice.**

## 4. Status of N1 — graded

- **Mechanism half `[on file, 2026-07-26; not re-tested here]`**: `½ = 2/4` from the 120° lock,
  `|1+ζ₃| = 1`. **MASTER_v4's "no account / OPEN" is stale and should be updated.**
- **Numeric half `[EMPIRICAL — measured here]`**: the `0.470 → ½` shortfall is the finite-size
  deficit of a max over `L ≈ p/6` semicircle draws; the null reproduces the exponent
  (`−0.663` vs `−2/3`) and the magnitude (ratio ~0.75, no drift) across `p ∈ [127, 6199]`.
- **SCOPE / what is NOT established.** This does **not** prove the 120° lock — that remains
  verified at 22 primes, not proved for all `p`, and is the Kronecker/Stickelberger target. It does
  **not** address the `bx+cy` side beyond the eigenvalue count. It bounds the deficit **as a
  max-statistic**; a residual smaller than the finite-size scatter (~`p^{−2/3}`) is not excluded.
- **⇒ N1 is accounted for on both halves, at the stated scope.** Not "closed" in the PROVED sense:
  the mechanism inherits the 120° law's verified-not-proved status.
