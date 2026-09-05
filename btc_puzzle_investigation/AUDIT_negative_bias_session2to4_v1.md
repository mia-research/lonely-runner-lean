# AUDIT — negative-bias re-check of Sessions 2–4 (v35/v36/v37)

**Date:** 2026-07-18 · **Trigger:** user flagged the phrase *"the mantra pointed me at the shadow
sector and it came back generic … isolated to one decidable lattice-counting statement"* as a revert
to the documented negative bias ([[feedback_negative_bias_enlarge_nulls_2026_07_17]]).
**Scripts:** `_audit_Sy_structure_v1.py`, `_audit_ct_and_xy_v1.py` (+ decay re-fit inline).

**The failure mode audited.** I ran *null tests* ("is X zero more than chance?") and reported the
answer with **dismissal words** — "generic", "at the floor", "refuted", "no structure". The memory's
rule: a bound is a **magnitude**, not "no structure"; structure lives in a value-law / symmetry-type /
subspace. I did not look there. This audit re-opens the three dismissals and **characterizes** each.
**Verdict up front: the bias was real in the CHARACTERIZATIONS; the leakage bottom-lines survive.**

---

## 1. `Sy` "generic" (v36 §2) — WRONG as a characterization

I wrote the odd-sector object `Sy = Σ_P s_y(P)χ₂(y_P)` "came back generic". Characterizing it
(`_audit_Sy_structure_v1.py`, p≡3 mod 4, IN [100,4000) + OOS [4000,10000)):

| property | finding | status |
|---|---|---|
| divisibility | **`6 | Sy` always** (gcd of all `|Sy|` = 6, IN and OOS) | exact structure; **forced by μ₃** (`y(λd)=y(d)` ⇒ `χ₂(y₀)` μ₃-invariant ⇒ `3 | Sy/2`) |
| magnitude | `|Sy|/2√p`: mean **1.05** (IN) / **0.84** (OOS), max ~2.4 | a **Weil-scale magnitude**, not "nothing" |
| sign | **positive-skewed**: +16/−6 (IN, z=2.13), +19/−10 (OOS, z=1.67); pooled ≈ **2.7σ** | suggestive, **NOT a law** — needs more data; may be convention-linked |

**"Generic" erased all three.** The correct statement: *`Sy` is a Weil-magnitude character sum with
`6|Sy` (μ₃-forced) and a mild unexplained positive-sign skew; it has **no** exact conservation beyond
the forced `p≡1 mod 4` zero and **no** `p mod 8` law (unlike `S`).* The **leakage conclusion is
unchanged** (still an x/y character sum inside bounds — no leak), but the characterization was biased
to "nothing" when the object is structured at the Weil scale.

---

## 2. `C_T` "the 2-3% is finite-n" (v35 §10) — conclusion right, but I leaned on someone else's number

Two separate claims were bundled:
- **(a) The shear mechanism is refuted** — `λ₂=λ₃=1/3` EXACTLY under the uniform model, θ-independent.
  **This is solid** (exact computation) and stands.
- **(b) The observed 2-3% is finite-n** — I asserted this, but **my own v35 data did not show it**:
  the 4-point fit gave exponent `−0.279`, and I **silently substituted DRILL 01's `−0.584`** to make
  the required-n table. That substitution was the bias — presenting a borrowed number as if my run
  established it.

**Re-audit** (`_audit_ct_and_xy_v1.py` + inline, full-orbit large-n primes, n=258→99666, 7 points):
fitted exponent **`b = −0.495`, log-log `r = −0.92`** — a clean power-law decay, consistent with
`1/√n` and with DRILL 01. **So (b) is now EARNED from my own data.** The conclusion holds; the v35
writeup overstated what its own evidence showed. *(First naive attempt used composite-order `G`
orbits — small, noisy `n`; corrected to full generator orbits.)*

---

## 3. `x/y` "at the floor, captures no fraction of the shadow" (v35 §9) — holds, now characterized

The DLP-aligned `C/floor` sits at 1.05–1.4 with a firing planted control (6→18) — that part was
correct. The missing piece was **what `x/y` is**, not just how big its aligned correlation is.
Characterized (`_audit_ct_and_xy_v1.py`): `sign(x/y)` aligns with the known `sign(xy)` D-shadow bit at
**0.50–0.56** (≈ chance, ~1σ at these `N`) and with y-parity at ~0.51. So `x/y` is a **joint
(x,y) readout that is ~independent of the known cheap shadow bit** — it captures neither more nor the
same. "No fraction of the shadow" now rests on a characterization, not just the floor metric. **Holds.**

---

## 4. Summary — what the bias did and did not touch

- **Touched (corrected here):** the *characterizations*. "Generic" (`Sy`) hid a Weil-magnitude,
  `6|Sy`, sign-skewed object. "Finite-n" (`C_T`) was asserted on a borrowed exponent, now earned.
  Language like "non-symmetric in origin" (my chat summary) overreaches — the correct claim is **"not
  enforced by any hexagonal-lattice symmetry"** (v36's actual result), which does not exclude a
  Gauss/Jacobi-sum origin.
- **Did NOT touch (survive the audit):** the leakage bottom-lines. `Sy`, `x/y`, the `C_T` residual are
  all inside the Part V bound; none is a leak. The reflection kill (`L≠L̄`) and the H1 reduction
  (v37) are exact and stand.
- **Symmetric rigor** ([[feedback_dont_pre_evaluate_shut_thinking_2026_07_11]]): the positive that
  surfaced (`Sy` sign-skew) is held to the SAME bar — ~2.7σ pooled is **suggestive, not a finding**;
  it is not promoted to a law. No false positive manufactured to compensate for the false negatives.

**Standing correction to the method:** after a null test, **characterize the object** (divisibility,
magnitude vs Weil, symmetry type, value-law, sign-law) before writing any of {generic, at-the-floor,
no structure, refuted}. A magnitude at √p is a *result about size*, and it is reported as such.

*(Corrects the characterization language in `masked_structure_findings_v35.md` §9–10 and
`v36.md` §2. The findings' decidable content is unchanged; the dismissal framing is retracted.)*
