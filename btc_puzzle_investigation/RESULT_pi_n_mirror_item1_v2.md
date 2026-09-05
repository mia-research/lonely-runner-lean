# RESULT — ITEM 1 (v2, CORRECTED): the `(π_n)` mirror is a genuinely different object. v1's "defect" is RETRACTED.

**Date:** 2026-08-01. **Supersedes `RESULT_pi_n_mirror_item1_v1.md` §2–§4.**
**Script:** `pi_n_mirror_v3.py`. **Grade:** `[VERIFIED — exact]`.

## 0. RETRACTION — what v1 got wrong

v1 claimed the pinned pair is "not a property of the ideal" because a reduced basis is defined only
up to the six Eisenstein units, imposed a "canonical normalization" `arg(π) ∈ [0°,60°)`, found the
pinned pair constant, and called the record's bridge a forced statistic. **All of that is wrong.**

`π` is **not merely a generator of an ideal — it is the Frobenius endomorphism**, and it satisfies

> `π + π̄ = 2·Re(π) = t = p + 1 − #E(F_p)`.

The six associates `u·π` have six **different** traces. Multiplying by a unit changes `Re(π)`, hence
changes `t`, hence no longer represents the curve. v1's normalization did exactly that: it forced
every prime into one 60° wedge, **erasing the curve's Frobenius angle**, which is why the pinned
pair came out constant. v1 manufactured the flatland and then blamed the rule for it.

**Two specific failures, recorded:**
1. v1's own output printed `"t = 2Re(pi) = 671331852483699643819086596696745227420 (matches curve
   trace)"` — and `t_p = 432420386565659656852420866390673177327`. **A verification claim was
   printed in output text without the verification being performed.**
2. v1 called the record's hardcoded `aP,bP` an "undocumented convention". It is not:
   **`2·aP − bP = 432420386565659656852420866390673177327 = t_p` exactly.** It is the trace-pinned
   Frobenius, i.e. the mathematically forced choice.

## 1. The correct construction (exact, closed form)

For `N(π) = M` and trace `t` with `t² − 4M = −3k²`:

> `π = ((t+k)/2, k)` in `(1,ω)` coordinates; the conjugate is `((t−k)/2, −k)`.
> These two are the only Frobenius elements; the other four associates are not.

**Instrument check: `frobenius(p, t_p)` reproduces the record's `(aP, bP)` exactly.** ✓

## 2. ITEM 1 result

| ideal | `π` | trace check | pinned pair |
|---|---|---|---|
| `(π_p)` | `(367917413016453100223835821029139468249, 303414439467246543595250775667605759171)` | `2Re = t_p` ✓ | **`[1,4]`** |
| `(π_n)` | `(−64502973549206556628585045361533709077, 303414439467246543595250775667605759171)` | `2Re = t_n` ✓ | **`[0,3]`** |

`t_n = n+1−p = 2 − t_p`, exact. `N(π) = M` and parallelogram area `= M` verified for both.

> ### The pinned pairs DIFFER. The falsifier fires.
> Per §2.4's own criterion: **"the two ideals are not interchangeable and the mirror is a different
> object."** Both sides use the identical sector labelling, so the *difference* is
> convention-independent even though the absolute labels are not.

**This is the informative branch.** The `(π_n)` mirror is not a redundant copy of the `(π_p)`
programme — the lift geometry genuinely differs between the two ideals, so the norm band, Cap Law,
`σ`, frame operator and `C_T` on `(π_n)` are **distinct unrun objects**, not restatements.

## 3. One unresolved discrepancy — flagged, NOT called a defect

Under my sector construction (`R₁ = π`, `R₂ = πω`; sector `s` spans `[60s°, 60(s+1)°)` on the unit
rays) secp reads pinned pair `[1,4]`, whereas the record reports `c₀ = c₃ = 1/8`, i.e. `[0,3]`; and
the bridge rule scores 35/69 rather than the recorded 0 violations. A constant label shift does not
reconcile them (different `t` need different shifts).

**Candidate cause, unverified:** `eisenstein_lift_sextant_exact_v1.py`'s `gauss()` reduces using
`dot(a,b) = a₀b₀ + a₁b₁` — the plain dot product of the `(1,ω)` **coefficients** — whereas the
Eisenstein norm is `a² − ab + b²`; meanwhile its `sextant()` rotates in `ω`-coordinates. That is an
internal mismatch between the reduction form and the labelling frame.

**I am not calling this a defect.** I over-claimed once on this item already. What is established is
only that my labelling and the record's disagree and I have not reconciled them. **The §2 conclusion
does not depend on the reconciliation**, since it compares two ideals under one labelling.

## 4. Still unrun in §2.4

Norm band, Cap Law, `σ`, frame operator, `C_T` on `(π_n)` — now known to be genuinely distinct
objects rather than restatements. The `h(−n)` analogue of `|FLD| = 6h(−p)` remains a small-prime
study (class numbers at `2^256` are not directly computable).

## 5. Method note

The error class here is **conflating a lattice-theoretic object with an arithmetic one**: an ideal is
defined up to units; a Frobenius endomorphism is not. Any future normalization of `π` must preserve
`2Re(π) = t`, and a script that normalizes `π` should assert that equality rather than print a claim
about it.
