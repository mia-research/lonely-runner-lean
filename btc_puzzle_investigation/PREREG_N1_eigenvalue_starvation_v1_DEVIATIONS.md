# DEVIATIONS — `PREREG_N1_eigenvalue_starvation_v1.md`

**Filed 2026-07-23, retrospectively.** This file should have existed before the run it describes.

---

## D1 — `n1_exact_saturation_v1.py` ran under this prereg's remit and did not conform to it

The frozen spec states (line 7): *"**Binding on:** any run reporting results for finding **N1**."*
`n1_exact_saturation_v1.py` reported results for N1 (`RESULT_N1_reframed_2sqrtp_cap_v1.md`). It was
therefore bound by this spec. It did not follow it:

| spec requirement | what the run did |
|---|---|
| §1 *"Exactly one primary statistic … It is **pooled**, not a max"* (exact 4th spectral moment) | used **max `Q(a) = \|V(a)\|²/p`** — a max, not pooled |
| §1b legacy saturation is **secondary**, *"reported, never a verdict"* | made the saturation max the **basis of the conclusion** |
| §2 matched nulls (group-automorphism relabeling; sign-randomisation; regime-swap) | **none run** |
| §3a magnitude plant (must fire); §3b rank calibrators | **none run** |
| §3c unforced-hit accounting; §4 family/multiple-comparison rule | **not applied** |
| §0e/§0f regime separation (`m = −2` vs `m = 2` cells never pooled) | primes **not** stratified by regime |

**No deviation was filed at the time.** That is the failure: a deviation is not necessarily wrong, it
is necessarily disclosed, and this one was not.

---

## D2 — Consequences: what is withdrawn, what stands

**WITHDRAWN as a conclusion about N1** — the measured claims of
`RESULT_N1_reframed_2sqrtp_cap_v1.md` §2–§3 are **downgraded to an unregistered observation**. They
may not be cited as an N1 finding, may not be counted in any tally, and may not be used to close,
reframe, or reprioritise N1 until re-run under this spec (or under a superseding prereg). Specifically
downgraded: *"both χ₂ readouts cap at 2√p"*, *"the cap is real, not a fluctuation"*, *"the ½ is a
non-tight ceiling"*, and the §3 before/after table. The index entry headed "★ N1 REFRAMED" overstates
what an unregistered max-statistic run can support and is corrected alongside this file.

**STANDS, because it is not a measurement.** §1 of that document — that `[−1]` sends the group
character `ω = e_n(a·)` to `ω⁻¹` and therefore maps `H¹(a) → H¹(−a)` rather than splitting `H¹(a)`,
so there is no fixed-`a` 2+2 eigenspace decomposition and the ledger's named decidable test does not
discriminate — is a **derivation**, with no statistic, no null and no free parameter. It is unaffected
by this deviation. It also does not depend on any number in the withdrawn sections.

**Also stands:** the *refutation* of my own integrality hypothesis (`Q(a) ∈ Z`). A hypothesis of the
run's own author, killed by the run's own check, is not a finding about N1 and needs no registration
to be recorded as dead.

---

## D3 — What a conforming re-run requires

Per §1/§2/§3 of the spec: the pooled exact 4th spectral moment as primary; the three matched nulls of
§2; the §3a magnitude plant and §3b rank calibrators firing; §3c unforced-hit accounting; regimes
`m = −2` and `m = 2` reported as **separate cells**, never pooled (§0e, §4a).

**Carry forward into that re-run** — §A2.6 already established, and this spec must not re-litigate,
that *no bulk average over all frequencies can detect the effect* (the dimension shows up in `O(1)`
of `n` frequencies, `O(n)` against a bulk of `O(n²)`), and that the §1 pooled 4th moment is exactly
such a bulk average. **The spec's own primary statistic is therefore under suspicion of being
structurally blind**, which is what its gate P1 failure already recorded. Resolving that tension —
either a new primary statistic that is extremal-tail sensitive *and* pre-registered with a matched
null, or an explicit re-registration — is a precondition for any N1 verdict, not an afterthought.
