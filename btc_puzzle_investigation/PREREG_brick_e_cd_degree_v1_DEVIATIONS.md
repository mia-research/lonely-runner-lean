# DEVIATIONS — Brick E c(d)-degree prereg

Registered spec: `PREREG_brick_e_cd_degree_v1.md` (SHA-256 `71c2a985…`, frozen 2026-08-20).
Deviations recorded here, never by editing the frozen spec. Each is timestamped and states whether it
was found **before** any real-signal read (pre-registration-preserving) or after.

---

## D1 · Q3 degree statistic is per-LARGE-prime-factor — found before any real read (2026-08-20)

**Source:** validating the mechanical engine `brick_e_degree_fitter_v1.py` on the Q5-i **planted**
firing control (planted data, not the real `c(d)`). No real-signal value was computed.

**Finding.** Over `M = ord(A_new-part)` with a small prime factor (e.g. `M=1893=3·631` at `p=43`),
`d^q ≡ d (mod q)` (Fermat) collapses every polynomial mod the small factor `q=3` to a function of
`d mod 3`. So points sharing a residue mod 3 must agree mod 3 for ANY exact fit to exist; a generic map
(and the matched null) therefore admits **no** polynomial fit at all mod 3 (`min_degree_fit → None`),
independent of degree. Consequence: the small factor carries **no degree information** and its
`None`/collapse is not comparable to a numeric degree.

**Refinement to Q3 (mechanical, does not change the hypothesis or the null).** The degree statistic `D`
is read **per CRT factor, on the large prime factor(s) only** (`631` at `p=43`, where `d=0..n-1` are
distinct so the Vandermonde is full-rank). Report `D_q` for each prime power `q^e ∥ M` separately;
the headline `D` is `max` over the large factors (those with `q > n`). The small-factor fit is reported
as a consistency flag (does `c(d) mod q` depend only on `d mod q`?), not as a degree.

**Engine evidence (planted/synthetic only):** planted deg-2 → `D=2`, linear coeff `0`, inversion
recovers `d`; planted deg-3 → `D=3`; random map → `None` mod `M`, `D=30` mod `631` (no false low-D);
CRT residues match. All in `brick_e_degree_fitter_v1.py` `__main__`.

**Status:** mechanical refinement, self-audit-sufficient (§2a mechanical layer). It sharpens *how* the
frozen statistic is read; it does not relax the null (Q4), the falsification thresholds (Q6), or the
held-for-gate status of the real measurement. The isolated `experiment-designer` gate (owed) should
confirm the `max`-over-large-factors reading and whether `D_q ≤ N/3` is the right threshold per factor
for small `n`.

---

## D2 · μ₃-covariance has a DEGREE FLOOR (=10 at p=43); control (ii) plant corrected — before any real read (2026-08-21)

Applies to **v2** (SHA e3fe35d0). Found while building the null machinery (`brick_e_run_v1.py`) and the
minimal-covariant-degree computation — null-side / structural only, **no real `c⁺` value read**.

**Finding (exact, mod 631 over the 15-point `Q` at p=43).** The space of μ₃-covariant polynomials
(`c(25d)≡κc(d)`) is 5-dim, spanned by degrees **{10,11,12,13,14}** (dim 1,2,3,4,5). So **no μ₃-covariant
polynomial has degree < 10** — the forced covariance imposes a **degree floor of 10**. The μ₃-null
`D`-histogram (4000 draws) is pinned accordingly: `D=14` (3991), `D=13` (9), none below. Hence:
- gate R2's "p=43 null histogram broad ⇒ lead only" is **empirically off**: the null is *tightly* pinned
  at 13–14, floor 10. A real `c⁺` at `D∈{10,11,12}` gives `π≈0` — p=43 can separate a below-floor
  signal (powered claim still = degree-STABILITY, but p=43 is not power-*less*).
- **"low D" = below the μ₃-covariance floor**, which the matched null already encodes; comparing `D_obs`
  to the μ₃-null is exactly right (both floored). No change to the frozen statistic or null.

**Control (ii) plant CORRECTED.** v2 §5(ii)'s "μ₃-covariant low-degree monomial `c(d)=a·d^{i₀}`" is
**impossible** (no low monomial is covariant; floor 10). Correct minimal plant = the **degree-10
covariant polynomial** (J=10 nullspace vector). Fired: covariant=True, fitted `D=10`, `π=0/4000`.

**Exploitation scope note (honest).** The floor bounds the *absolute* exploitable degree from below: at
p=43 a "solvable" `D=10` over `|Q|=15` is not a brute-force win. The exploitation question is whether
`c⁺` sits **below** the null's floor, tracked across the ladder — the floor scales with `p` and the
matched null accounts for it, so the test is well-posed; the absolute-degree caveat travels to the
secp-transfer claim, not the test.

**Control status before the real read:** (i) engine FIRE; (ii) pipeline FIRE (corrected); (iii)
calibration CALIBRATED (max|F(p)−p|≈0.002). **(iv) ρ-identity — NOT YET (needs Sage F_{p²} + explicit
ζ₄ endomorphism).** The real `c⁺` arm stays unread until (iv) fires. Mechanical finding,
self-audit-sufficient (§2a). Artifacts: `brick_e_run_v1.py`, the minimal-degree computation logged in
session.

---

## D3 · Control (iii) calibration is BROKEN + INAPPLICABLE at p=43 — caught by the banned-word diagnostic (2026-08-21)

**How it surfaced.** The v1 draft of `RESULT_brick_e_cd_degree_v1.md` and the session report leaned on the
banned credibility-hedge "honest/honestly" (memory `feedback_no_credibility_hedges`: the word is a
DIAGNOSTIC that a control-validity or algebra claim went unchecked). A reviewer flagged it. Per the rule
("stub-test the claim, then delete the word — never delete only") the stub test found a real defect.

**Two failures in control (iii) ("null draws → π ~ Uniform; CALIBRATED, max|F(p)−p|≈0.002").**
1. **Buggy metric.** The reported `0.002` was wrong. The stub test (`brick_e_run_v1` calibration path,
   recomputed) gives the TRUE KS deviation from Uniform = **0.998**. The original code's sorted-deviation
   loop did not track the true maximum.
2. **Inapplicable by design at this rung.** The statistic `D` is essentially **two-valued** at p=43
   (13 or 14; DEVIATIONS D2's degree floor 10 + generic ceiling 14, and only 31/20000 land at 13). A
   two-valued statistic has a **discrete** p-value that piles up at 1.0 (1996/2000 of fresh null draws get
   π=1.0) — it **cannot** be Uniform[0,1]. So "π ~ Uniform" is the wrong calibration criterion for a
   degenerate/low-dynamic-range statistic; control (iii) only becomes meaningful at rungs where the null
   `D`-histogram has spread (p≥163).

**Consequence.** "All four controls fired" (v1 draft) is an OVERCLAIM: **three fired (i, ii, iv); (iii)
did not.** The p=43 *reading* survives (`D_obs=14, π=1.0` is null-consistent independent of calibration —
a *large* π cannot be a false-positive artifact), but the grade drops to NEAR-VACUOUS and the rung carries
a one-bit observation, not a powered null.

**Fixes owed before a powered rung.** (a) Correct the KS computation in the calibration code. (b) Scope
control (iii) to rungs where the null `D`-histogram has ≥ some spread (so a discrete-uniform expectation is
even sensible); at degenerate rungs, replace it with the exact discrete calibration (compare the empirical
π-distribution to the *discrete* null-D law, not Uniform). (c) This is the 3rd+ broken-control instance on
the project (cf. `VOID_anew_cartier_c4`, `feedback_test_on_both_sets` "check the CONTROL ROW fires"); the
same-model gate (experiment-designer) did not catch it — it was caught by the user's word-diagnostic.
Mechanical finding, self-audit-sufficient once the stub test is in hand.
