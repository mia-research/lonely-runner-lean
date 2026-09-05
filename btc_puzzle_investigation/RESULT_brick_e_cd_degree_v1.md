# RESULT — Brick E, p=43: `c⁺(d)` is generic-degree (scoped NULL, lowest-power rung)

**Date 2026-08-21.** Executed against the frozen, frame-gate-CLEARED spec `PREREG_brick_e_cd_degree_v2.md`
(SHA **e3fe35d0**, echoed at run time and matched). Exact integer arithmetic; no float in the signal
path. No ECDLP/key-recovery claim. **This is one rung (p=43) of a degree-stability ladder; it is NOT a
closure of Brick E — see §4.**

> **CORRECTION (2026-08-21, after this file's first draft).** The first draft claimed "all four controls
> fired." **That was an overclaim — control (iii) did NOT validly fire.** Caught when a reviewer flagged a
> banned credibility-hedge in the write-up; the stub test (`DEVIATIONS D3`) then showed the statistic `D`
> is essentially two-valued (13/14) at p=43, so its p-value is discrete and piles up at 1.0 — it *cannot*
> be Uniform, making control (iii) **inapplicable** here, and my reported "max\|F(p)−p\|≈0.002 CALIBRATED"
> was a **buggy** max-deviation computation (true KS = **0.998**). Corrected table below. This does not
> overturn the p=43 reading (§2: `D_obs=14`, `π=1.0` is null-consistent regardless of calibration, since
> a *large* π cannot be a false-positive artifact), but it weakens the grade (§4) and it means the rung is
> **near-vacuous**, not a "clean" null. Control (iii) must be redesigned/scoped to powered rungs (p≥163)
> before any rung that could yield a *small* π.

## 1. Preconditions — control status (corrected)

| control | spec §5 | result |
|---|---|---|
| (i) engine | planted deg-2 → D=2, inverts | **FIRE** (`brick_e_degree_fitter_v1.py`) |
| (ii) pipeline | degree-10 μ₃-covariant plant → D=10, π=0 | **FIRE** (corrected per DEVIATIONS D2 — no low monomial is covariant) |
| (iii) calibration | null draws → π ~ Uniform | **INAPPLICABLE / BROKEN at p=43** — `D` two-valued ⇒ p-value discrete, cannot be Uniform (true KS 0.998, not the 0.002 first reported). See DEVIATIONS D3. |
| (iv) ρ-identity | `φ([−d]G)=±ρ·φ([d]G)` in `Jac(F_{p²})` | **FIRE** — 30/30, **15/15 on non-QR d** (`brick_e_ctrl_iv_rho_identity_v1.sage`) |

**Three of four controls validly fire (i, ii, iv); (iii) is inapplicable at this degenerate rung.** The
p=43 reading (§2) does not depend on (iii): `π=1.0` (real at the ceiling) is interpretable without a
calibration guard, which is only load-bearing when a *small* π is claimed. Control (iv) confirms the
non-QR half `= ρ·(QR half)` — the warrant for the QR-half restriction. Data integrity: the real `c⁺(d)`
carries the forced μ₃-covariance `c⁺(25d)≡1849·c⁺(d)` exactly (all 15 values).

## 2. The read (p=43)

Domain `Q` = QR-half, `|Q|=15`; `c⁺(d)=dlog_{S(G)}(S([d]G)) ∈ Z/1893` (the `lbe_dlog.sage` I1 table).
Statistic = min-degree polynomial fit over the large factor 631 (DEVIATIONS D1).

- **`D_obs = 14`** — the **maximal possible** degree for 15 points (the full Lagrange interpolant).
- **μ₃-null D-histogram** (20 000 covariant draws): `D=14` (19 969), `D=13` (31), none below.
- **`π = P_null[D' ≤ D_obs] = 20000/20000 = 1.00000`.**
- **INV: N/A** — at `D_obs=|Q|−1` the fit is the full interpolant: no compression, equivalent to brute
  force.

**Reading:** the QR-half `c⁺(d)` is **not a low-degree polynomial in `d`** at p=43 — it is generic
(top-degree). No solvable-congruence channel at this rung. `[VERIFIED-scope]`.

## 3. Exactly what power this rung has (and does not)

Per DEVIATIONS D2 the μ₃-covariance imposes a **degree floor of 10**, and the null is pinned at 13–14.
So at p=43 the statistic has almost no dynamic range: it can separate a **strong** channel
(`D_obs ∈ {10,11,12}` → π≈0) from generic, but cannot distinguish `D=13` from `D=14` with power
(31/20000 at 13). **The real `c⁺` sits at the very ceiling (14).** Therefore:
- **Ruled out at p=43:** a strong low-degree channel (`D ≤ 12`). It is absent — `c⁺` is maximally generic.
- **Not ruled out at p=43:** a weak channel (`D = 13`), unresolvable at `|Q|=15`.

## 4. Scope — NOT a closure (project stance)

A scoped null is not an avenue closure (CLAUDE.md: burden-of-proof on the closure; a null is bound to
its method+sample). This retires nothing beyond: *at p=43, the QR-half `c⁺(d)` degree statistic shows no
strong low-degree channel.* The **powered claim is degree-STABILITY across the ladder**
`{67,79,163,211,547}`, with real dynamic range from **p≥163** (reps ≥ 23; max degree grows with `|Q|`).
The Brick E hypothesis (a low-degree `c(d)` solvable for `d`) stands or falls on that ladder, not on this
rung. The A_new channel more broadly (Prong 1's supersingular `A_new`, the `ζ₄` absolute-eigenvalue
question) is untouched by this one degree statistic.

**Grade:** `[VERIFIED-scope — p=43 rung, NEAR-VACUOUS: c⁺ at the generic degree ceiling (14); rules out a
strong channel D≤12, cannot resolve D=13; π=1.0 vs matched μ₃-null]`. Controls i/ii/iv valid; **(iii)
inapplicable at this degenerate rung** (DEVIATIONS D3). Not promoted to any avenue-level claim. The rung
carries a one-bit observation (ceiling vs D=13), not a powered null.

## 5. Next

Generalize `lbe_dlog.sage` to the ladder (parameterize `p`, `β`, the `A_new`-part dlog — Pohlig–Hellman
if `|A_new(F_p)|` is large), run the four controls per rung, then the frozen statistic. **First powered
rung: p=163** (reps=23). Degree-stability at the ceiling across ≥2 powered rungs would retire the Brick E
low-degree channel *with power*; a sub-floor `D` at any rung is a signal to chase.

*Enabler: `RESULT_anew_…_v3.md` (Prong 1). Spec: `PREREG_brick_e_cd_degree_v2.md` (e3fe35d0). Engine:
`brick_e_degree_fitter_v1.py`. Controls: `brick_e_run_v1.py`, `brick_e_ctrl_iv_rho_identity_v1.sage`.*
