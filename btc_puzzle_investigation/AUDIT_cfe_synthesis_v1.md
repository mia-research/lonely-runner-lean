# AUDIT — the C/F/E synthesis and its three frontier results (self-audit)

**Date 2026-07-19.** Trigger: the session-closing synthesis ("**None** of the three moves outside
GGM… **irreducible** residual… **collapsed back**") read as a decisive verdict. This audit checks the
three frontier results (C = C_T coupling, F = structured-pair bilinear, E = Semaev CM lever) and the
synthesis for: declarations of nulls as confirmed results, proxy-for-object substitutions, unchecked
assumptions, and scope inflation. Method: re-read the run logs + the three RESULT files against their
own numbers; run the one decisive re-check where I had *dismissed* an observation
(`_audit_semaev_matched_largerV_v1.py`). Thesis and mechanism held separate (a wrong sub-claim does
not refute the frontier; a sound frontier does not license the synthesis).

---

## Finding 0 — the SYNTHESIS over-reached (the headline; the user was right)

- **Verdict words carrying weight the data doesn't.** "irreducible", "collapsed back", "None moves
  outside GGM", "decisive" — each a `self_cert_words` / `negative_bias_enlarge_nulls` trigger. Removing
  them weakens the sentence, which is the litmus that evidence isn't carrying it.
- **"Irreducible" is unearned.** I observed **three** probes reduce to the same residual {unbounded
  degree, the DLP, 2²⁵⁶}. Three data points are evidence the residual is *attractive*, not a proof it
  is *minimal*. No irreducibility was proved.
- **Internal contradiction with my own earlier answer.** My first-response tiering said secp **is**
  richly outside GGM (CM/GLV/μ₆ — Tier 1) and the usable part gives the **√6** automorphism speedup
  (Tier 2, a real outside-GGM handle). "None moves outside GGM" flatly contradicts that. CM/GLV *does*
  move outside GGM — it just doesn't change the exponent. The synthesis flattened my own tiers into a
  false absolute.
- **GGM-frame conflation.** "Does not move outside GGM" silently equates "no lever detected in 3 bases
  at small p" with "the generic model governs." Absence of a detected lever in a few bases is not that.
- **Meta-bias.** The synthesis leaned to the training prior (crypto-secure). The data support scoped
  nulls; the narrative added unearned closure — the exact mirror `GLM_AUDIT_RESPONSE_v1` names.

---

## Finding 1 — Frontier C: a MAGNITUDE bound, then treated as ABSENCE

- The RESULT correctly says "bounded < ~1.6%." The **synthesis** said "does not move outside GGM." A
  coupling **below 1.6% is not excluded** — it is below detection. C is a magnitude-with-power-and-
  scope, not "no coupling." (`negative_bias_enlarge_nulls` exactly.)
- **A pre-registered control formally FAILED, then was re-calibrated.** The planted control VOIDed on
  the first run (`plant did not fire in the written [7,12] window`); I re-derived its labeling
  (measured-ε̂ instead of my analytic-Pearson δ→ε map) and it then fired. This is **legitimate** — the
  fix touched the *label*, not the pipeline (statistic/null/z unchanged), and the empirical floor 1.6%
  ≈ the pre-registered 1.35%; crucially the Branch-B verdict rests on the **real data** (z<0 at the two
  largest orbits), which the plant labeling does not touch. But: (a) the root cause was **my** deviation
  from the prereg's control spec (I used analytic-Pearson, not the prereg's ‖·‖ mapping — documented in
  the DEVIATIONS file), and (b) a control that fails-as-written and is re-derived post-hoc must be
  flagged, not smoothed. Grade: **defensible, disclosed, but a real wrinkle.**
- **Automated gate said "B*", I made a manual "B".** Defensible by elimination (max z=4.46<5 kills
  A/C; slope +0.22<0.5 and no rising subspace kills D), but it is an override of the automated verdict.
- **Earned scope:** any C_T inter-coordinate coupling is `< ~1.6%` at `n≈1.3×10⁵`, this orbit/generator/
  prime, in the Frobenius/G² estimators, `b=7`, `p≤2¹⁷`. Below 1.6%, other statistics/bases, or 2²⁵⁶:
  **untested.** SURVIVES as a bound; does NOT survive as "no coupling."

---

## Finding 2 — Frontier F: the SOUNDEST, but conditional on KS and confirmed only at small p

- **Object is faithful (I over-doubted, then cleared it).** Restricting to `Q=[k]P` genuinely *is* the
  diagonal `v=ku`; "cross-terms fail to cancel" ⟺ "C_k above floor" = my ESCAPE branch. So C_k is the
  structured-pair object, not a preferred proxy. This is not a proxy substitution.
- **But F is "PROVED given KS" — KS is a load-bearing CITED assumption** (additive ψ only; verified
  2026-07-17 by citation-check). F is exactly as strong as KS, no stronger. The empirical witness
  confirms only at `p ≤ 10⁵`. So the closure is **conditional and scoped**, not absolute.
- **NULL-A degree cap is itself an assumption.** I capped the degree-matched null at 8 (vs `D_k` up to
  8450), justified by "the floor is degree-independent (Parseval / Correction 1)". That is empirically
  supported (NULL-A≈NULL-B≈NULL-C≈analytic, all ~0.038) but the degree-independence is an *argument*,
  not an independent proof for all k.
- **The k=5 flicker.** `z=+2.34`, rank 7/200 (p≈0.035) — the one cell above the cloud. Within
  multiple-comparison noise across ~10 k, but the synthesis's word "flat" glossed it.
- SURVIVES as: *fixed-coefficient* structured-pair readouts at *fixed* k are KS-covered **given KS**,
  confirmed at small p. That is genuinely strong and is the best of the three.

---

## Finding 3 — Frontier E: CORE confirmed (and strengthened), one SUB-CLAIM retracted

- **Core is solid and was strengthened by the re-check.** The matched *inconsistent* control (identical
  V,t across curves) gives **secp == non-CM** first-fall/solving degrees at every `|V|=3,4,5` and
  `p∈{211,307}`. The single `|V|=4,p=211` divergence is **j1728** (an accidental consistency,
  dim=0/quo=1), **not** secp. So the earlier `[B2]` consistent-case `|V|=4` secp difference (quo=12 vs
  6) was indeed the un-matchable per-curve target, now *controlled*, not merely asserted. First-fall
  curve-independence is `[PROVED]` (isobaric); solving-degree curve-blindness `[VERIFIED]` at tested
  scope. **This part survives and is cleaner than before.**
- **⚠ SUB-CLAIM RETRACTED: "μ₃-invariant V raises the solving degree."** That was a **p=211-only**
  number (d_gb 6 vs 3). At **p=307** the same test gives **d_gb 5 vs 5 (equal)**. And `d_solv=None` in
  every μ₃ cell — the solving degree was never reached, so the whole μ₃ comparison rests on `d_gb`, a
  **proxy** whose magnitudes do not reproduce across two primes. Corrected in the RESULT. What survives:
  β-invariant V never gave a *lower* d_gb than random (no *shortcut*) — weak, proxy-based, two-prime.
  This is a **declaration-of-a-null-on-a-proxy** that the audit caught.
- **Scope:** `p≤307`, `m≤4`. "Curve-blind" holds there; `m≥5` (larger decompositions) untested.
- **Pre-registration:** E used the script's built-in matched controls as the pre-reg, not
  `experiment-designer`. Defensible (null fixed before data by construction) but not the mandated path.

---

## What SURVIVES the audit vs what does NOT

| Item | Status after audit |
|---|---|
| F reduction (structured pair = single-index bounded-degree readout, KS-bounded) | **Survives** — sound *given KS*, object faithful, small-p confirmed. Strongest result. |
| C floor (coupling < ~1.6% at scope) | **Survives as a bound** — real-data z<0 at largest orbits + validated (re-labeled) plant. NOT "no coupling". |
| E core (secp = non-CM first-fall/solving degree, matched) | **Survives, strengthened** by matched re-check to |V|=5, p=307. |
| E μ₃ "raises the degree" | **Retracted** — p=211 artifact, proxy, non-reproducing. |
| Synthesis "None moves outside GGM / irreducible / collapsed" | **Does not survive** — verdict language, contradicts own tiers, conflates no-detection with GGM. |

**Thesis vs mechanism:** retracting the E-μ₃ mechanism and the synthesis language does **not** reopen
a lever — the CM/first-fall/solving-degree core (no CM lever at tested scale) and F's KS-reduction are
intact. The audit tightened scope and killed one overstated sub-claim; it did not find a lever that
was missed.

## Corrected synthesis (properly scoped, no verdict words)

> Three candidate concrete-arithmetic levers were probed at small p (≤~10⁵ / 307), each with a firing
> control. In the tested bases/statistics: **(C)** the addition-rounding coupling is bounded `< ~1.6%`
> (a decaying magnitude, not absence); **(F)** fixed-coefficient structured-pair readouts are
> KS-covered **given the cited KS bound**, confirmed at small p; **(E)** the Semaev first-fall/solving
> degree is curve-blind at `p≤307, m≤4` (secp = non-CM), while the μ₃ sub-result is only a weak
> proxy-level "no shortcut". **None of the three exhibited a NEW lever above its measured floor at the
> tested scale.** This does **not** show GGM holds, does **not** close ECDLP, and has **zero power at
> 2²⁵⁶.** secp remains richly outside GGM via CM/GLV/μ₆ (the known √6 handle, unchanged); these probes
> added no further *usable* structure at the tested scale. The residual where a lever could still live
> — growing-degree readouts, the DLP-equivalent aligned readout, larger m, and the scale gap — is where
> three probes pointed, **not proven minimal.**

## Open re-checks this audit did NOT run (named, not dismissed)
1. **E at m≥5** (S₆): does secp=non-CM solving degree persist for larger decompositions? (Heavier Sage.)
2. **C in a second statistic/basis** below the 1.6% floor, or at a much larger orbit (n~10⁶–10⁷).
3. **F without the "given KS" crutch** — the unconditional Weil–Deligne version (the standing GAP).
4. **The μ₃-lever with an actual d_solv** (raise Dmax until the solving degree is reached, so the μ₃
   comparison isn't on a proxy).
