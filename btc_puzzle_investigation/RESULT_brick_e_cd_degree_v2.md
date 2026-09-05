# RESULT v2 — Brick E, powered ladder: the cover-scramble degree `c⁺(d)` is at the GENERIC CEILING across all well-posed rungs — the low-degree channel is retired WITH power

**Date 2026-08-23.** Executes the frozen, frame-gate-CLEARED spec `PREREG_brick_e_cd_degree_v2.md`
(SHA **e3fe35d0**, echoed and matched at every run). Supersedes the p=43-only `RESULT_brick_e_cd_degree_v1.md`
(retained). Exact finite-field / integer arithmetic; the only floats are reported percentiles. No
ECDLP / key-recovery / keyspace claim, and none is reachable (this is the NULL direction — see §5).

**Grade:** `[VERIFIED-scope — cover-scramble degree at the generic ceiling (D=|Q|−1) at 3 well-posed rungs
p∈{43,127,547}; degree-STABLE at the ceiling across ≥2 POWERED rungs {127,547}; control-ii FIRES at every
rung (planted deg-2 → D=2, π=0.0005) so a low-degree channel would be seen — none is. The Brick E
low-degree cover-scramble channel ("read c⁺, solve for d") is RETIRED WITH POWER over the tested ladder.]`

---

## 1. The finding that reshaped the ladder (D5 — well-posedness)
The degree fit lives over `Z/q` for `q` a prime factor of `|A_new(F_p)|=p²+p+1`, with domain `d∈[1,n)`,
`n=#E(F_p)≈p`. It is **well-posed only if `q ≥ n`** (else the domain collides mod q and no CRT factor is
fittable). Auditing the frozen ladder `{43,67,79,163,211,547}`:

| p | n | reps | qmax(p²+p+1) | well-posed (qmax≥n)? |
|---|---|---|---|---|
| 43 | 31 | 5 | 631 | ✓ (lead) |
| 67 | 79 | 13 | 31 | **✗** |
| 79 | 67 | 11 | 43 | **✗** |
| 163 | 139 | 23 | 67 | **✗** |
| 211 | 199 | 33 | 37 | **✗** |
| **547** | 547 | 91 | 613 | ✓ (powered) |

**Only p=43 and p=547 of the chosen ladder are well-posed.** The prior-session p=163 and p=211 runs
(~2 h of Sage instrument each) were on **ill-posed** rungs — `large=[]`, no degree read was ever possible
there (they crashed on control-iv before the analysis exposed this). A search over admissible primes
(`p≡7 mod12`, `n=#E` prime, `6∣n−1`, `qmax≥n`) supplied a second cheap powered rung, **p=127** (reps=21,
qmax=5419), added as DEVIATION D5. The frozen STATISTIC and controls are unchanged; only the rung
SELECTION is corrected for the well-posedness the spec already requires ("the large factor… where the
Q-values are distinct").

## 2. Engineering fixes (all validated on p=43 against RESULT v1's D_obs=14)
- **D5b (Pohlig–Hellman + cyclic projection).** `p²+p+1` is squarefree ⇒ `A_new(F_p)` cyclic; work in the
  Sylow-qmax subgroup via the group cofactor `M//qmax` — dlog table = qmax (613 at p=547, not the 26733
  the prior run wastefully built), and NO per-element `.order()` (that call hung p=547 for 4.5 h).
- **D6 (control-iv `I2`).** v1's `Fq.gen()` is a root of Sage's default modulus, not `√−1`; fixed to
  `Fq(-1).sqrt()`. Now fires **15/15** non-QR d at p=43.
- **D7 (fast degree engine).** The analysis fitter climbed `D=0..|Q|−1` with Gaussian elimination each —
  `O(|Q|⁴)` per fit, infeasible at |Q|=273 × 2000 null draws (≈ days). Replaced by **Newton divided
  differences** (`O(|Q|²)`, inverse denominators precomputed once since Q is fixed): the interpolant is
  unique, so its degree = the old `min_degree_fit` D. p=547 analysis now runs in **5 s**.
  Engine `brick_e_analysis_v2.py`; reproduces p=43 D_obs=14 exactly.

## 3. The powered read (per rung, exact)
Object: `c⁺(d)=dlog_{S(G)}(S([d]G)) mod qmax` on the QR-half `Q`; statistic = min-degree of the
interpolant; μ₃-matched null = 2000 covariant draws (`c⁺(λd)=κ c⁺(d)`, κ³≡1 mod qmax verified EXACT at
every rung).

| p | reps | \|Q\| | qmax | **D_obs** | ceiling \|Q\|−1 | μ₃-null degrees | control-ii (deg-2 plant) | LOW-D? |
|---|---|---|---|---|---|---|---|---|
| 43 | 5 | 15 | 631 | **14** | 14 | {13,14} | D=2, π=5e-4 FIRE | No |
| 127 | 21 | 63 | 5419 | **62** | 62 | {62} | D=2, π=5e-4 FIRE | No |
| 547 | 91 | 273 | 613 | **272** | 272 | {271,272} | D=2, π=5e-4 FIRE | No |

`c⁺(d)` sits at the **generic maximal degree** at every rung — indistinguishable from a random
μ₃-covariant map (whose interpolant is full-degree almost surely; the null spread is 0–1). **INV** returns
the unique `d=1` at each rung, i.e. the degree-`|Q|−1` "fit" is the full Lagrange interpolant — no
compression, equivalent to brute force. No solvable low-degree structure at any rung.

## 4. Controls
- **(i) engine:** planted deg-2 → D=2, inverts — `brick_e_degree_fitter_v1.py` / v2 Newton. FIRE.
- **(ii) pipeline (the POWER control):** a plant routed through the full null+degree pipeline → D=2,
  π=5e-4 at **every** rung. So a strong low-degree channel WOULD register; the real ceiling read is a
  **powered** null, not a blind one. FIRE.
- **(iii) calibration:** the μ₃-null degree is pinned at the ceiling (spread 0–1) at every rung, so its
  p-value is discrete and cannot be Uniform — **INAPPLICABLE / degenerate**, exactly as at p=43
  (DEVIATIONS D3/D4). The read does not depend on it: `π=1.0` (real at the ceiling) is not a
  false-positive artifact, and the discriminating power comes from control-ii's dynamic range, which
  GROWS with |Q| (rules out D≤~270 at p=547 vs only D≤12 at p=43).
- **(iv) ρ-identity (structural, QR-half warrant):** FIRE 15/15 at p=43. **OWED at p=127/547** — the
  `F_{p²}` function-field instrument (~p² places over GF(p²)) did not complete in the session's budget.
  The identity `non-QR half = ρ·(QR half)` is a scale-independent consequence of the `ζ₄` endomorphism
  (`ρ²=[−1]`) and is expected to hold; it is recorded as owed, not assumed. The degree read is on the
  QR-half and is unaffected by whether (iv) is re-confirmed at the larger rungs.

## 5. Scope — what this retires, and what it does NOT (burden-of-proof on the closure)
**Retired WITH power (the deliverable):** the Brick E hypothesis that `c⁺(d)` is a **low-degree** polynomial
solvable for `d` (the "cover-scramble is a solvable channel" attack). Across three well-posed rungs, and
two POWERED ones, `c⁺` is at the generic degree ceiling with the instrument proven able to detect a
low-degree plant. Per the prereg §6 this is the condition that "retires the Brick E low-degree channel
with power." The cover-scramble map is **maximal-degree**; reading `c⁺([d]G)` and inverting is no cheaper
than brute force.

**NOT claimed:** (a) a keyspace/ECDLP consequence — this is the null arm (a high-degree scramble gives no
transfer); (b) a resolution of the maximally-weak `D=|Q|−1` vs `|Q|−2` boundary (the null occasionally
drops one — unresolvable, and irrelevant to a *low*-degree attack); (c) anything about the broader
`A_new` channel (Prong 1's supersingular structure, the `ζ₄` **absolute-eigenvalue** question) — untouched
by this one degree statistic. **This is a scoped null bound to method+rungs, not an avenue closure.**

## 6. Next
- **Second POWERED rung achieved (p=127) — degree-stability confirmed.** Further well-posed rungs
  (p=967 reps=151, p=1303 reps=208; qmax search in `brick_e_analysis_v2` / the ladder audit) would extend
  the stability, cheaply now (Newton fitter + PH).
- **Owed:** control-iv (ρ-identity) at p=127/547 via a cheaper `F_{p²}` instrument; `compile-diff` before
  any master promotion.
- **Companion:** the L-mono monodromy campaign (`PLAN_lmono_monodromy_campaign_v1`) is the theoretical
  both-ends attack — Brick E bounds the transfer-map *degree* (this result: maximal), L-mono the spectral
  geometry of the cover's rigidity.

*Spec: `PREREG_brick_e_cd_degree_v2.md` (e3fe35d0). Runner: `brick_e_rung_v2.sage` (D5b/D6). Engine:
`brick_e_analysis_v2.py` (D7 Newton), `brick_e_degree_fitter_v1.py`. Data:
`brick_e_rung_{43,127,547}_v2_data.json`. Enabler: `RESULT_anew_…_v3.md` (Prong 1). Predecessor:
`RESULT_brick_e_cd_degree_v1.md` (p=43).*
