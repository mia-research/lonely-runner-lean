# RESULT — N7 sub-Rayleigh deficit locus drill: the near-zero |U| excess has NO clean (b,c) geometric locus; the striking c-axis "concentration" is FORCED anisotropy

**Date:** 2026-08-22. Executes `PREREG_subrayleigh_deficit_locus_c_channel_v1.md` (location arms) over the
30 frozen model primes × τ∈{0.05,0.10,0.15}. **Anomaly-drill CHARACTERIZATION, not a verdict/closure.**
Scripts: `scratchpad/anew_p43_validation/n7_locus_drill.py`, `n7_locus_full.py`. Model range only
(p∈[151,12043], E:y²=x³+7); **no claim at p≈2²⁵⁶**. Inherits the established effect (mean|U| ~0.1% below a
matched Hermitian null, ~8% near-zero excess, Σ|U|² exactly conserved) — its existence is not re-tested.

## Statistic-integrity events (the drill's main value this run)
1. **P5 caught a rate-leak in the first statistic.** The δ̂-differenced X² normalized by the *null-rate*
   variance; a uniform 8% rate excess (which the deficit IS) leaked in and tripped the "concentration"
   detector. Fixed by the **conditional-multinomial X²** (condition on the total near-zero count, test only
   the allocation across strata — rate-invariant). Re-validated: **P1 (diag concentration) fires
   diag-dominant p=1/201; P5 (uniform rate) does not trip.**
2. **A forced anisotropy nearly read as a find.** The primary X² vs a UNIFORM allocation pointed hard at
   the c-axis: Stouffer **+186**, τ-robust, NC-√N corr **+0.99**, dom=caxis at all 30 primes. But the
   char-vs-**null** permutation p was significant at only ~27% of primes, and at several large primes the
   NULL draws concentrate on the c-axis MORE than char. The b=0 axis is intrinsically near-zero-prone in the
   folded FFT — **a forced geometric anisotropy the matched null shares, not char-specific.** The correct
   statistic is char's allocation vs the NULL's allocation (`za`), which differences the forced anisotropy out.

## Result (char-vs-NULL allocation `za`; NC-floor za null-vs-null clean, |Z|<2.2 all strata)

| organizer | `za` Stouffer (τ=.05/.10/.15) | reading |
|---|---|---|
| **c-axis** (b=0) | +0.5 / +2.8 / +2.5 | **null** — the +186 was forced anisotropy, NOT char-specific |
| **c=±b diagonal** | −0.0 / +0.5 / +0.3 | null |
| **bulk c⁺ / c⁻** | ≈0 / ≈0 / ≈0 | null |
| **S-C2 (c-sign D_c)** | −0.9 / +0.3 / −1.2 | **null** — no c↦−c asymmetry (the smoke's p=691 blip was noise) |
| **b-axis** (c=0, x-only) | −2.7 / **−4.7** / **−6.9** | weak char-specific near-zero **DEFICIT**, √N-rising, NC-floor-clean, **but NOT τ-robust** (τ=0.05 marginal) |

## Verdict — pre-reg branch B (bounded characterization), with one weak named lead

**The near-zero |U| excess is NOT localized in the tested (b,c) geometric organizers** — c-sign, the c=±b
diagonal, the bulk c-halves, and (char-specifically) the c-axis are all null once the forced b=0 anisotropy
is removed. Per the counter-prior bar: OBJECT = near-zero |U| location on the 5-stratum (b,c) partition;
CLASS = char-specific allocation concentration vs the matched Hermitian null; POWER = pooled thin-stratum
floor ~2.5–3.6× δ_global, bulk ~0.06× (§8); SCOPE = 30 model primes [151,12043]. This **narrows the
mechanism**: the excess behaves as a **global / moment effect**, not a geometric locus in (b,c).

**EXPLICITLY NOT CLOSED (branch-B mandatory clause):** the **imaginary-part isotype** (this was a
magnitude-locus drill; ADD3-C left the imaginary part open), **higher-order (≥3rd) phase invariants**, a
**cumulant identity** on the near-zero tail, the co-occurrence arms **S-Cpair / S-mu6** (MC-GR null, not run
here — deferred), and non-(b,c) bases. N7 stays live and mechanism-open.

**Secondary lead (named, not a finding):** a weak char-specific **depletion of near-zeros on the c=0
(x-only) axis** — the global excess is slightly *avoided* on the b-axis. za −4.7/−6.9 at τ=0.10/0.15,
√N-rising, calibration-confirmed, but not τ-robust (τ=0.05). Owed: its own τ-concordant, powered follow-up
(is the x-only sub-spectrum `U(b,0)=Σ_d g(d)e^{-2πi b x_d/p}` char-specifically less cancelling?).

## Owed
- Co-occurrence arms S-Cpair / S-mu6 (MC-GR null) — the μ₂/μ₆ *organization* (vs *location*) — not run.
- The b-axis depletion follow-up (τ-robustness, mechanism).
- Frame items from the pre-reg self-audit (MC-GR adequacy, organizer non-orthogonality) remain isolation-owed.

*No ECDLP/leakage claim. The characterization bounds the near-zero excess's (b,c) location; the deficit
itself is unchanged and mechanism-open, now narrowed toward a global/moment (phase) effect.*
