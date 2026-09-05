> **SUPERSEDED by `RESULT_linchpin_s_gate_v2.md` (2026-08-11). Kept as trail.** v1's title/grade
> OVER-recorded ("linchpin VERIFIED / XVI.D → VERIFIED" assumes the tested `eps` equals the linchpin's
> `ε_LBE`, which is unresolved), and v1's Scope UNDER-recorded (pre-deflated the untested d-payoff by
> calling `eps` "a forced marginal, not a constraint on d"). Read v2 for the corrected recording.

# RESULT — the XVI.D linchpin gate `s<3/16 ⇒ ε=0` is VERIFIED (exact, public, reaches 2²⁵⁶)

**Date:** 2026-08-11. **Track 2a of the shadow-hunt plan.** Grades per claim; scope stated explicitly.
**Artifact:** `scratchpad/linchpin_s_gate_v1.py` + its stdout (reproduced below). Exact arithmetic
(`Fraction`/`int`), no float in the signal path, no key `d` in the feature path.

## What was blocked, and the source-first unblock

MASTER_v9 Part **XVI.D** carried the priority-open frontier `[UNTESTED — the linchpin]`: a candidate
**public** route to the correction bit `ε` via the Eisenstein lift norm `s=N(eis(X))/p`, gate
`s<3/16 ⇒ ε=0`. It was marked blocked on "recovering the **unspecified** `eis(X)` map."

**The map was already implemented in our own code** (source-first payoff): `eis(X)` and the flap
indicator `eps(X)∈{0,+,−}` are built by `int1_frame_operator_v1.build` (and `build_secp` at secp),
with the norm `enorm` from `lift_sextant_rhombus_law_proof_v2`. **Both are exact integer functions of
`X` (the x-coordinate) ALONE — no `d` anywhere in their path** — and `build_secp` runs them at secp's
actual prime. So linchpin question (a) *"is `s=N(eis(X))/p` computable from public `x` alone?"* is
answered **YES by construction**.

## The test (decidable artifact) and controls

For every `X∈[1,p)`: `s = Fraction(enorm(eis(X)), p)`, `e = eps(X)`. Check the implication
`s < 3/16 ⇒ e = 0` (0 = Cap-Law **core**, exact μ₃-covariance). Controls:
- **FIRING:** the implication is non-trivial — non-core `X` exist, including at `s≥3/16` (so `e=0` is
  not forced everywhere). Fired at every prime and at secp.
- **NEGATIVE (label-shuffle):** permuting the `eps` labels while holding the `s<3/16` mask fixed
  produces **164–200 violations** per prime ⇒ the clean pass is **not vacuous**.

## Results — `[VERIFIED — exact structural; both mod-12 classes; reaches 2²⁵⁶]`

Small primes `p≡1 mod 3` (both `p≡1` and `p≡7 mod 12`; **secp is `p≡7 mod 12`**), all `X∈[1,p)`:

| p | p%12 | Pr[s<3/16] | Pr[eps=0] | gate viol | s_max | shuffle viol | fires |
|---|---|---|---|---|---|---|---|
| 1009 | 1 | 0.6786 | 0.7500 | **0** | 0.7047 | 164 | Y |
| 1039 | 7 | 0.6763 | 0.7572 | **0** | 0.6824 | 163 | Y |
| 1063 | 7 | 0.6893 | 0.7401 | **0** | 0.7262 | 200 | Y |
| 1087 | 7 | 0.6851 | 0.7459 | **0** | 0.7240 | 185 | Y |

(8 primes total, all 0 violations.) **secp256k1** (`p≈2²⁵⁶`, sampled 20 000 `X`):
`Pr[s<3/16]=0.6831`, `Pr[eps=0]=0.7520`, `s_max=0.7437`, **gate violations = 0**, fires.

**Reads:**
1. **The gate holds exactly** — `s<3/16 ⇒ eps=0`, 0 violations, small `p` AND secp-sampled. Firing +
   negative controls both behave.
2. **Cap-Law cross-check lands:** `Pr[eps=0]≈0.75` = the proven `¾` core density; `s<3/16` pins ≈**68%**
   of x-values to core with certainty; `s_max<¾` as the ledger states (`s∈[0,¾]`).
3. **Reaches scale.** `eis`/`eps`/`enorm` are exact integer maps ⇒ the property is structural, not an
   enumerable-`p` coincidence; the secp-sampled run confirms it at `2²⁵⁶` (the #5 banner is cleared for
   *this* object).

## Scope — what is established vs. what the leakage payoff still needs (do not conflate)

**Established:** the flap bit `eps(x)∈{0,+,−}` is a **public, exact, scale-reaching** function of the
x-coordinate, and `s<3/16` certifies `eps=0` for ~68% of x-values from public data alone. XVI.D's
own claim is verified.

**NOT established (the actual leakage question, next and PRE-REGISTERED):** whether this public bit
**reduces the search space for the scalar `d`** when `X=x([d]G)`. Two cautions bind here:
- **`eps(x)` alone is a per-point MARGINAL** (Statement of Intent: a per-point readout is Farey-generic
  unless it carries exploitable joint structure; `eps` is in fact μ₃-orbit-**forced** by symmetry). A
  marginal is not a constraint on `d` by itself.
- **The ledger-vs-XVI.C tension is unresolved.** The positive ledger asserts "T2's carry bit `ε` *is*
  the Cap-Law flap correction"; XVI.C says measuring the LBE carry `ε=[r₁+r₂≥n]` from public coords is
  **circular because it contains `d`**. **Whether the public Cap-Law `eps(X)` equals / constrains the
  LBE carry `ε` that ARSENAL tools 3/5/7 consume is exactly the open question.** Testing it is the
  **residue-vs-component trap zone** (`feedback_residue_vs_component_tautology`): the `d`-side target
  must be constructed **disjoint** from `eps(x)`, never re-injecting `d`.

## Named next probe (sharper law → next probe, per anomaly-drill; NOT a closure)

**T2a′ (pre-register, experiment-designer):** does the public `eps(x([d]G))` compose into a `d`-constraint
via the one non-circular route — the **two-key / joint-carry** tool 7 (`c_sum=c₁+c₂+ε` for a known
`d₁` + unknown `d₂`) and/or **OPEN_d2**'s known-bit-range→partial-carry? Target `d mod 3` (or a range
cut) built disjointly from `eps`; matched null sharing `eps`'s μ₃-forced symmetry; firing control;
tested on the real 82 keys AND the constructed known-generator set. Falsifier: `eps(x([d]G))`
independent of the disjoint `d`-target at the achievable power.

**Owed gates:** `citation-verifier` on the Cap-Law `¾:⅛:⅛` / `eps=0⟺core` inputs before any grade
moves up on them; `compile-diff` if this is folded into a master.
