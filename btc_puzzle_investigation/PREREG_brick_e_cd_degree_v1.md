# PREREG — Brick E: minimal polynomial degree of `c(d) = dlog_{A_new}(φ([d]G))`

**Grade slot: `[PROVISIONAL — experiment-designer unavailable]`** (session limit, attempted 2026-08-20,
resets ~22:20 Australia/Brisbane; the isolated designer gate is **owed**, §7). Frozen self-written
pre-registration. Time-order preserved: the statistic, matched null, firing controls, and falsification
condition below are fixed **before any `c(d)`-vs-`d` value is computed.** SHA-256 freeze in
`PREREG_brick_e_cd_degree_v1.md.sha256`. No leakage/ECDLP/key-recovery claim; no grade may be promoted
off this spec until the gate clears (§2a condition 4). Exact integer / finite-field arithmetic only —
no float in any signal-path step (CLAUDE.md NO-FLOAT rule).

---

## 0. Object (fixed)

`E : y² = x³+7` over `F_p`, `p ≡ 7 mod 12` (⇒ `ω=ζ₃∈F_p`, `E` ordinary, `n=#E(F_p)` prime). `G` a
generator; GLV `φ_GLV:(x,y)↦(βx,y) = [λ]`, `λ` order 3 in `(Z/n)*`. Cover `C : w⁴ = x³+7`, genus 3;
`C→E` is `(x,w)↦(x,y=w²)`. `Jac(C) ~ E × A_new`, `A_new` 2-dim, **superspecial/supersingular at
`p≡3 mod 4`** (`RESULT_anew_supersingularity_step3_gap_and_cartier_route_v1/v2/v3`), so its DLP is easy
(MOV `k=3`). Set-map `φ: E(F_p)→A_new`: pull `P` back to its fibre divisor on `C`, take the class in
`Jac(C)`, project to the `A_new` isotypic factor (the `M3`/`M5` construction,
`OPEN_lbe_isotypic_projection_v1.md`). `c(d) := dlog_{A_new}(φ([d]G))`, `d∈Z/n`. `c` needs only the
public point `[d]G`, never `d`.

**Two facts respected, not tested.** (F1) `Hom(E,A_new)=0` ⇒ `φ` has no homomorphism component ⇒ the
**linear term of `c` is forced 0** (structural motivation only). (F2) FORCED orbit-covariance
`c(λd) = κ·c(d)`, `κ²+κ+1 ≡ 0 (mod M)` (measured, N14 / `RESULT_isotypic_trace_lever_status_v1.md`).
Any null MUST preserve (F2) or it is a broken control.

## 1. Design decisions (Q1–Q6), resolved — each flagged for the gate to confirm

**Q1 · Domain.** The fibre of `C→E` over `P=(x_P,y_P)` is `{w:w²=y_P}={±√y_P}`; the class `φ(P)` is
`F_p`-rational iff `y_P` is a QR (else `F_{p²}`). **Primary domain: the FULL group `E(F_p)`, all `n`
points, with every dlog taken in `A_new(F_{p²})`** (embed `A_new(F_p)⊆A_new(F_{p²})`; still supersingular
⇒ DLP still easy), so all `c(d)` share **one** modulus `M = ` (the `A_new`-part order of `A_new(F_{p²})`).
**Robustness arm:** the rational-lift-only subset (QR half, `≈(n−1)/2` points, dlog in `A_new(F_p)`,
modulus `1893=3·631` at `p=43`) recomputed as a cross-check; the two arms must agree on `D`.
*[gate-confirm: that embedding into `A_new(F_{p²})` does not itself introduce structure — the null runs
in the same group, controlling for it.]*

**Q2 · Modulus / CRT.** Fit over `Z/M` by CRT into prime-power factors `M=∏ q_i^{e_i}`; per factor,
solve the exact Vandermonde system over `Z/q_i^{e_i}` (integer linear algebra, Hensel-lift through the
`e_i` levels). No float. `d` taken as its integer representative in `[0,n)`.

**Q3 · Statistic.** `D := ` smallest degree with an EXACT fit `c(d) ≡ Σ_{i≤D} a_i d^i (mod M)` on the
frozen domain (with `a_1≡0` **not** imposed — (F1) is a prediction to observe, not a constraint to bake
in). Because a degree-`(N−1)` fit is trivial for `N` points, `D` is read only **relative to** the null:
report the permutation p-value `π = Pr_null[D' ≤ D_obs]`, and the *inversion* flag `INV` = (does the
degree-`D` fit solve uniquely for `d` given `c(target)`?). "Low degree" is asserted only if
**`D ≤ N/3` AND `π ≤ 0.01` AND `INV` true AND stable across the Q6 ladder.**

**Q4 · Matched null (shares the forced symmetry).** Draw random maps `c'` satisfying `c'(λd)=κc'(d)`
EXACTLY (pick `c'` freely on one representative per `⟨λ⟩`-orbit, propagate by F2), otherwise random in
`A_new`. This preserves (F1)-consistency and (F2) exactly and varies only the UNFORCED degree content.
`≥ 2000` null draws for the p-value. A null draw must show generic-high `D` and `INV` false.

**Q5 · Firing controls (must fire before the real arm is read).** (i) **Planted degree-2:** build
`c*(d) = a₂d²+a₀` as an actual `A_new` element sequence; the fitter must return `D=2` and the inversion
must recover `d`. (ii) **Affine/GLV positive control** from `RESULT_isotypic_trace_lever_status_v1.md`:
must fire per that file. If either control fails to fire, the RUN IS VOID (do not read the real arm) —
this is the forced-zero-control trap that voided the earlier Cartier run (`VOID_anew_cartier_c4_...`);
the planted control is chosen so vanishing is **not** forced (a genuine degree-2 signal is present).

**Q6 · Power, scope, falsification.** Ladder `p ∈ {43, 67, 79, 163, 211, 331}` (all `≡7 mod 12`,
`E:y²=x³+7`); the banner-admissible claim is degree-**stability**: the same low `D` recurs across the
ladder. `p=43` alone (`n=31`) has **weak** power — a low `D` there is a lead to climb the ladder, not a
result. **Falsification:** high `D` (`>N/3`) OR `π>0.01` OR `INV` false at `p=43`, OR `D` not stable
across the ladder ⇒ the low-degree-solvable-channel hypothesis is **refuted**, and the measured `D`
becomes the first quantitative bound on the cover-scramble degree. **Scope:** none of these rows carry
secp power (scale banner); only *form-level degree-stability, if it holds,* is a statement about the
cover-scramble degree, and its transfer to secp additionally requires N2 (`A_new` supersingular at secp,
supplied by Prong 1) plus `A_new`'s own `k=3` DLP cost at secp (`L_{p³}(1/3)`), neither claimed here.

## 2. Outcome table (both cells are bricks)

| outcome | reading | grade it would earn (after the gate clears) |
|---|---|---|
| low `D`, `π≤0.01`, `INV`, stable | a **solvable non-homomorphic channel**: read `c` via `A_new` DLP, solve degree-`D` congruence for `d` | `[EMPIRICAL — form-level, model scale]`; secp transfer separately gated |
| high `D` / not stable / `INV` false | first **degree bound** on the cover-scramble `d↦c(d)` | `[VERIFIED-scope — degree ≥ D₀ bound at the tested `p`]` |

## 3. Self-audit — frame layers NOT dischargeable by this self-written spec (§2a)

Per CLAUDE.md §2a, a self-audit clears **mechanical** layers (statistic well-defined, exactness, "does
the plant fire") but **cannot** clear **frame** layers — isolation is the mechanism. Named uncovered:

- **Matched-control adequacy (frame).** The Q4 null shares (F2) by construction, but whether it shares
  *every* forced symmetry of the real `φ` (e.g. a hidden `ζ₄`/biquadratic covariance from the `w⁴`
  cover, `ANALYSIS_zeta4_...`) is exactly the frame question a self-written null can miss. **This is the
  layer that produced the project's forced-zero-control voids.** Uncovered until the gate runs.
- **Pre-commitment isolation (frame).** I wrote both the hypothesis and the null; the isolated designer
  is what guards the null from being unconsciously shaped to the expected answer. Uncovered.
- **Scope/falsification framing (frame).** §1 Q6's falsification thresholds are my choice; an isolated
  designer may find `N/3` or `π≤0.01` mis-set for `n=31`. Uncovered.

**Covered (mechanical, self-sufficient with the artifact):** the exact-arithmetic fit (Q2), the
statistic's definition (Q3), and the planted-control firing check (Q5-i) — these I will validate on the
instrument before any real read.

## 4. What may proceed now vs. what is held

- **May proceed (does not see the real signal):** build the instrument (cover `C`, `A_new` isotypic
  projection, divisor-pullback `φ`, `A_new` dlog), and validate it on the **firing controls only**
  (planted degree-2; affine/GLV). Planted data ≠ the real `c(d)` sequence.
- **HELD until the experiment-designer gate clears (or explicit go-ahead to run provisionally):** the
  real `c(d)`-vs-`d` measurement and its `D/π/INV` readout. A provisional run, if authorized, is tagged
  `[PROVISIONAL]`, carries §3's uncovered-frame list in its grade slot, and promotes no grade (§2a).

## 5–7. Freeze / owed gates

- **§5 Freeze.** SHA-256 of this file recorded alongside it; the run script must echo the hash it was
  registered against before reading the real arm.
- **§6 Deviations** go in `PREREG_brick_e_cd_degree_v1_DEVIATIONS.md`, never by editing this file.
- **§7 Owed gates.** (a) `experiment-designer` isolated review of this spec — the frame-layer gate,
  attempted 2026-08-20, failed on session limit, **owed**. (b) `citation-verifier` on the caveat-2
  bypass (Prong 1 §2.2) — attempted same, failed same, **owed**. (c) `compile-diff` before any master
  promotion.

*Feeds: Brick E run (`RESULT_brick_e_cd_degree_v1.md`, not yet created). Enabler: Prong 1
(`RESULT_anew_supersingularity_step3_gap_and_cartier_route_v3.md`). Predecessor idea:
`ANALYSIS_idea_improvements_and_nogo_relook_v1.md` §1.*
