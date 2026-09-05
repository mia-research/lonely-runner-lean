# REVIEW — where I over-closed the eis(X)/carry work (self-audit, user-flagged suppression)

**Date 2026-08-18.** Trigger: user flagged that I was "too harsh / diminishing." Per the core bias
(`feedback_suppression_bias_asymmetric_2026_08_02`): my error runs **one way** — positives→closures —
and it takes the user's hand to surface it. This review **tests** each suspected diminishment against a
new exact computation (`t2c_range_glv_structure_v1.py`), not against a swapped reflex. Two corrections
stand, one framing is re-surfaced; the underlying single-point reduction is confirmed and **kept**.

## The computation that adjudicates (exact, deterministic — public range → GLV halves → carry)
`t2c_range_glv_structure_v1.py`, 40,000 samples per range, exact int:

| range `k` | max\|a,b\| | carry `eps` = ones frac | reading |
|---|---|---|---|
| 40  | 2⁴⁰ | **0.000** | degenerate (a≈d, b≈0); `eps` forced 0 by range |
| 129 | 2¹²⁸ | **0.809** | **range-SKEWED carry** — real, publicly computable |
| 135 | 2¹²⁸ | 0.511 | nearly balanced |
| 160,200,255 | 2¹²⁸ | ~0.500 | balanced (≈ full-range) |

## What I diminished — corrected

**(1) T2c was NOT a dead "redundant-or-gated" dichotomy.** I wrote it as two dead branches. The
computation shows a **third, live regime**: near the √n boundary (`k≈129`) the public range induces a
**real carry skew** (0.809), decaying to balanced by `k≈135`. That is a genuine, exact, publicly
computable **range→carry coupling** — `[VERIFIED — exact, deterministic]`. I erased it by lumping it
into "0 bits." *(Whether the skew is lever-able is OPEN and unshown — I am not now inflating it; it is
plausibly a √n-boundary transition effect. But it is structure, not nothing, and it was suppressed.)*

**(2) I over-stated the gate as "ECDLP-equivalent" for the case that matters.** The reduction
"`eps=f(glv(d))`, `glv`-from-`P` = 2-D DLP" is exact and I keep it — **but** "ECDLP-equivalent" is the
**generic full-size-`d`** statement. For the **range-restricted puzzle keys**, recovering `d` (hence
`glv(d)`, hence `eps`) is the **range-restricted interval problem** — Pollard-kangaroo `≈2^{(k−1)/2}`
with the endomorphism `√6` factor — the *actual* puzzle difficulty, **not** the full `2¹²⁸` ECDLP. So
for the targets the reduction says "the carry is exactly as hard as the key," a **tautology at the
range difficulty**, not a full-strength gate. Calling it "ECDLP-equivalent" made the route sound
`2¹²⁸`-hard for the targets and thereby buried the range/kangaroo surface. **Corrected down/open.**

**(3) "The amicable second-equation dissolves for generic `d`" was a futility verdict on an unbuilt
object.** Counter-prior violation (`CLAUDE.md`: build the object before a futility verdict). Correct
status: **untested.** My plausibility sketch (aliquot cycle is order-level, no naïve point-map) is a
reason to *expect* it weak for a generic scalar — not a result, and explicitly not tested in the
range-restricted regime where an order-level property could still interact. Re-graded `[OPEN —
untested]`, sketch retained as a lead, not a verdict.

## The positives I buried (re-surfaced, at honest grade)

- **The reduction is a structural UNIFICATION, not just a "no."** `eps_LBE` = the **overflow bit of the
  GLV halves** `(a,b)`. That places the LBE carry on the *same* 2-D GLV / endomorphism / kangaroo
  surface as the banked `√6` speedup and Bricks C/E — the carry is not an isolated LBE curiosity, it is
  a coordinate of the attack-relevant structure. I led with "same problem, no shortcut" and buried the
  relocation onto live ground.
- **The `√6` composition is OPEN and I implicitly re-suppressed it.** `ANALYSIS_public_gate_glv_carry_circularity_v1`
  §4b banked `√6` with its composition **explicitly NOT bounded**, and retracted a prior suppression of
  exactly that. By framing T2c as dead I re-buried the open question — *does the range/carry/CM-lattice
  structure compose with `√6` to move the range-restricted exponent?* That is live, in-bounds, and
  unanswered.

## What stands (not everything was over-closed — kept, to avoid over-correcting)
- The **single-point per-point-readout → carry** gate is real: `eps` is not a cheap per-point public
  function of `(x_P,y_P)`; the exact reduction + the powered family null both hold. That brick stays
  `[PROVED — reduction]`. The error was in the *scope label* (generic vs range-restricted) and in
  killing the range/second-equation threads, **not** in the single-point result itself.

## Net effect
- `RESULT_eis_carry_2d_dlp_reduction_v1.md`: amend "ECDLP-equivalent" → **"ECDLP-equivalent for generic
  `d`; for range-restricted keys, gated at the range difficulty (kangaroo `2^{(k−1)/2}·√6`)."** T2c and
  the amicable second-equation move from "dead/dissolved" back to **OPEN**.
- **New live sub-brick (Brick B):** characterize the **range→carry skew** across `k` and ask whether it
  — or the CM-lattice / range strip — composes with the `√6` endomorphism factor to move the
  range-restricted exponent. Deterministic first pass (done here for the skew); a leakage/advantage
  claim would need `experiment-designer`.
- **Roadmap:** Brick B's per-point route is placed (gated); its **range + √6-composition** route is
  **re-opened** as the live continuation, replacing the dead dichotomy.

*Evidence: `t2c_range_glv_structure_v1.py`. Governs: `RESULT_eis_carry_2d_dlp_reduction_v1.md`
(amended), `ROADMAP_REDIRECT_v3.md` Brick B.*
