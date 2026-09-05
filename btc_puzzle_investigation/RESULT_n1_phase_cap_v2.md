# RESULT v2 — N1 re-typed to a phase-pairing question; the v1 headline is withdrawn

*2026-07-24. **Supersedes `RESULT_n1_phase_cap_v1.md`**, whose headline ("N1 EXPLAINED") and whose
§3 inference were overclaimed. Numbers are unchanged; grades are not. Rigor audit:
`n1_phase_cap_sweep_v1_DEVIATIONS.md` (**6 gaps — read them first**). Script:
`n1_phase_cap_sweep_v1.py`.*

**No leakage, key-recovery or ECDLP claim. Nothing here reaches `p = 2²⁵⁶−2³²−977`.**

---

## 0. Process standing of this run, stated before its content

**This run did not meet this project's bar.** It had **no `experiment-designer` pre-registration**
(CLAUDE.md §2 names "sweep" as mandatory; I overrode it), **no planted control**, **no out-of-sample
split**, and **no numerical criterion separating its own outcomes R2 and R3**. It also **contradicted
its own frozen text** by drawing inference from readouts the script had declared non-inferential.

Consequently this document reports the run at two grades: what is a **deterministic computation**
(unaffected by any of the above) and what was an **inference** (withdrawn or downgraded).

## 1. What stands — deterministic, no null, no inference

A falsifying instance was available at **every one of 193 primes** and never occurred.

> **`[VERIFIED — 193 primes, 402,718 distinct μ₆ configurations]`
> `S_y(p) := max_{a≠0}|V(a)|/√p ≤ 2`, with ZERO violations.**
> Largest observed `S_y = 1.99979` (`p = 1237`).

Also standing, all forced or exact:

- **The `α ↦ −ᾱ` closure** `[DERIVED — FORCED]`, and its forced readout check confirmed at all 193
  primes: `V` purely imaginary at `p ≡ 3 mod 4`, real at `p ≡ 1 mod 4`, worst `9.5×10⁻¹⁶`.
- **`|V(a)| = 2√p·|sin θ₁ + sin θ₂|`** (`p≡3 mod 4`) — four unit vectors, **two real parameters**.
  Independent of this sweep.
- **All four twisted eigenvalues have modulus exactly `√p`** `[VERIFIED — p = 13, 43 only; six
  unforced cells]`. So N1 is **not** eigenvalue starvation.
- `S_x(p) > 2` at **51 of 193** primes, max excess `0.0203` — **as a number.**
- The Hasse-guard bug, caught before any reading (§4).

## 2. What is withdrawn or downgraded

| v1 claim | v2 status |
|---|---|
| **"N1 EXPLAINED"** | **WITHDRAWN.** Correct framing: **N1 is re-typed** from an unexplained magnitude to a phase-pairing question with **one unproved inequality** left. The frontier is not closed. |
| "Pre-committed **R2 fires**"; `S_y → 2` | **`[EXPLORATORY — post-hoc trend]`.** R2 ("converges") and R3 ("plateaus below 2") were never separated by a threshold, so they are not decidable against each other. The means by range (1.97911 / 1.98563 / 1.99189) and the slope (`−0.448`) were computed after seeing the data. (D5) |
| §3 "**discriminating** comparison": `χ₂(x)` shows the cap is not an estimator / max-over-configurations / `+1` artifact | **INFERENCE WITHDRAWN.** The script froze these readouts as *"context, not controls — no inference is drawn from them."* That disclaimer stands. **The alternative explanation — that `S_y ≤ 2` is an artifact of the estimator or of the `+1` term — is currently UNEXCLUDED.** (D4) |
| the run as a pre-registered result | **not pre-registered** (D1); no deviations file until challenged (D2); no plant (D3); no holdout (D6) |

## 3. Where N1 actually stands

**The chain, honestly graded:**

1. Four eigenvalues, all modulus `√p` — `[VERIFIED, 2 primes / 6 unforced cells]`
2. Multiset closed under `α ↦ −ᾱ` — `[DERIVED — FORCED]`
3. ⇒ `|V| = 2√p·|sin θ₁ + sin θ₂|`, two real parameters — `[DERIVED]`
4. `|sin θ₁ + sin θ₂| ≤ 1` — `[VERIFIED at 193 primes, deterministically]`, **but not proved**, and
   the run establishing it does not carry a control excluding an instrument artifact.

**Net:** the `½` is *consistent with* being the phase-pairing cap `2√p`, and that is now a sharp,
well-posed question rather than an unexplained number. It is **not** established that the cap is a
property of the curve rather than of the measurement — that is what a control would have shown.

## 4. The instrument bug, unchanged from v1 and still worth carrying

The first pass had **no Hasse guard**. `curve_orbit` returns `ord(G)`, not `#E`; when `G` lands in a
small prime-order subgroup, `ord(G)` is prime and the primality filter accepts it — admitting
`p=1951 → n=5`, `p=11833 → n=61`, impossible for `#E`. Those rows dragged every mean down (pre-fix
`1.5556 / 1.6477 / 1.5506`) and **would have read as R3 rather than R2** — the opposite call. Fixed
by `|n − (p+1)| ≤ 2√p`. No reading was taken before the fix. Fifth instrument bug of this session;
the tell was an arithmetic impossibility in a printed column.

## 5. A compliant re-run

1. `experiment-designer` pre-registration with a **numerical** R2/R3 criterion **and its computed
   false-failure rate** — the specific gap that broke v1 and v2 of the row-budget spec, and that this
   run then reproduced.
2. A **planted control**: force a phase configuration with `|sin θ₁ + sin θ₂| > 1` and confirm the
   statistic reports `S > 2`. Without it, D3 stands and §1's bound has no power statement.
3. A **pre-frozen holdout** of primes, unread until the discovery set is written up.
4. `χ₂(x)` and the random target registered **as controls with firing criteria**, or left
   non-inferential — not both.
