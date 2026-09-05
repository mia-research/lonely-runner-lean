# DEVIATIONS — `PREREG_row_budget_lowtail_v1.md`

*2026-07-24. Filed at write-up time. Five deviations. Read with
`RESULT_row_budget_lowtail_v1.md`.*

---

## D1 — ⚠ P-DET was first run UNDER-POWERED, failed, and was re-run at spec

The first P-DET pass used `mcap = 400` frequencies and `R = 32` instead of the frozen `m_p`
(2 187 … 26 143) and `R = 64`. It reported criteria 3 **and** 4 failing.

**That failure was my reduction, not the instrument.** At `m = 400` the null `sd` is inflated by
`√(m_p/400)` — a factor of 5–8 at the mid primes — so `z(ε=0.20)` came back `+2.2 … +4.8` instead of
the `+6` bar. Re-run at full spec, **criterion 4 PASSES at every prime with `p ≥ 577`**.

The correct response to an under-powered control failing is to run it at spec, **never** to relax
the criterion. Recorded because the under-powered numbers exist in the session and could otherwise
be mistaken for the result.

## D2 — criterion 3 failed at spec, and the criterion is mis-specified (the run abstains anyway)

`N̄(ε)` is **not** strictly increasing at 8 of 10 primes; it dips between `ε=0` and `ε≈0.05–0.10`,
then rises monotonically. Diagnosed in `RESULT §3`: the plant interpolates *from the character*, and
the character end carries its own excess, so the plant simultaneously **adds** tone-spike low rows
and **destroys** the character's alignment. At `ε=0.05` the destruction removes ≈60% of the excess
(measured `−50.5% … −77.8%`, all 10 primes).

The spec's monotone model `ε²/(1−ε²)` describes the spike term alone and is valid only when the
`ε=0` carrier has no excess.

**No post-hoc repair was applied.** Criterion 3 was frozen, it failed, and outcome **O6** governs:
no verdict. The fix (plant into the MN-μ6 carrier) is named in `RESULT §3` and **requires a new
frozen spec**; it may not be applied to this run's numbers.

## D3 — `S1` and `S6` were not run; `S2` was not reported

Of the six pre-committed secondaries: `S3` (order statistic, verdict-gating) and `S5` (μ₆-orbit
occupancy, the mandated "effect outside the projected subspace") **were** run and are reported.
`S4` is partly covered by the ladder table. **`S1` (the low/high Spearman coupling) and `S6` (the
`c=0` / `b=0` strata) were not run**, and `S2` (dispersion) was computed but not reported.

`S1` is the one the spec singles out as the only non-additive statistic in the design, i.e. the only
one F5 does not render uninformative on the character side. **Its absence is a real gap** and it
should be in the v2 run. It does not affect the abstention, which is driven by the P-DET gate.

## D4 — the special strata were not analysed

F7 requires `c=0` and `b=0` to be analysed separately with negation-commuting nulls and never pooled.
The frozen `_FREQS_SPECIAL.txt` list (hash `dfa9f7a4…`, verified present) **was not consumed**; only
the generic stratum ran. No pooling violation occurred — the special strata simply were not run.

## D5 — a self-inflicted check error, corrected before it propagated

Verifying the spec's F8 claims, I first computed the tone control **including the `a=0` row** and
reported it as an off-by-one in the spec (`n−1` observed vs `n−2` claimed). **The spec is correct**:
F4 excludes `a=0` from every statistic. Re-checked with `a=0` excluded: chirp `= 0` and tone `= n−2`
**exactly**, at `n = 139, 397, 1009, 2143`.

Recorded because it is the same shape as the errors this project keeps catching — a claim checked
against the wrong convention rather than against the object's own definition. The other three
spec-time claims I checked all held: the order-12 frequency collapse
(`|U(a;b,c)| = |U(a;−b,c)|` elementwise, `8.6×10⁻¹⁶`), `β = 113` for `p = 991` (the spec's own
self-caught transcription fix — `826³ mod 991 = 78 ≠ 1`, and `826` is `p=2089`'s value), and the
chirp floor.

---

## D6 — ⚠ UNDISCLOSED at first filing: I swept the WRONG `ε` grid, and it feeds the failed criterion

Found by the v2 spec audit, not by me. v1 §4.1 froze

    eps in {0.05, 0.10, 0.15, 0.20, 0.30, 0.50, 1.00}

`row_budget_pdet_v1.py:25` ran

    EPS = [0.05, 0.10, 0.20, 0.30, 0.50, 0.80, 1.00]

**`0.15` dropped, `0.80` added.** This is not cosmetic: criterion 3 is *"`N̄(ε)` strictly increasing
across the seven swept levels"*, so **the swept levels are an input to the criterion that failed.**

**Does it change the outcome?** No. The dip is between `ε=0` and `ε≈0.05–0.10`, present in both
grids; neither adding `0.15` nor removing `0.80` touches it. The abstention stands. But the
disclosure is mandatory and was missing from the first filing of this file.

## D7 — SEEN-DATA ATTESTATION for the v2 strata arm: the out-of-sample set is **NOT** available

`PREREG_row_budget_lowtail_v2.md` registers `H-STRATA` (Arm B) with `p ∈ {163, 211, 349, 433, 991}`
as an out-of-sample holdout, **admissible only under a written attestation that those five primes
were not read before the freeze.**

> **I attest the opposite. Those five primes WERE read.** `row_budget_s1_s6_v1.py` was run on all ten
> frozen primes and `RESULT_row_budget_secondaries_S1_S6_v1.md` §2 reports the `c=0` and `b=0` `z`
> values for the full list. The holdout does not exist.

**Consequence, applied: outcome O-B4 (descriptive) governs Arm B.** The strata split may not be
reported as an out-of-sample confirmation, and `Z₅` may not be computed as a discovery statistic.
Acquiring a genuine holdout would require primes outside the frozen curve list, which the spec
forbids — so this is a limitation to state, not to work around.
