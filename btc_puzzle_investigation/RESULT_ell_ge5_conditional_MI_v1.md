# ℓ≥5, conditioned: the marginal blind spot now has an instrument that sees it — and holds no bridge

**Date:** 2026-07-25 · Pre-registered `PREREG_ell_ge5_conditional_MI_v2.md` (v1 audited by
`experiment-designer` before any arm; both required fixes folded in and independently verified).
Deviations: `PREREG_ell_ge5_conditional_MI_v2_DEVIATIONS.md`. Scripts (in-repo,
`scripts_bridge_programme/`): `ell_condmi_fast_v1.py` (numpy statistic core + calibration),
`ell_condmi_machinery_v1.py` (M0/Mc+/Mc− pure-Python cross-check), `ell_condmi_run_v2.py`
(arms + controls), `ell_condmi_verify_designer_v1.py` (audit-catch verification).
Exact integers for the number theory; MI is a monotone statistic vs exact permutation nulls.

**What this attacks.** `RESULT_ell_ge5_mutual_information_v1` proved the marginal `I(j;k)` null at
ℓ=5,7,11,13, and pre-committed (§4/N4) the one alternative it structurally could not see: a **purely
conditional** bridge `I(j;k | ideal data) > 0`. A uniform-shift bridge `j = k + f(w)` has `j ⊥ k`
marginally (invisible to the completed probe) yet `j,k` locked *within* each stratum of the mediator.
This probe builds and verifies the instrument for exactly that, and aims it.

**The mediator is pre-registered, not fished — but not "forced."** The sampler requires
`p ≡ n ≡ 1 (mod ℓ)`, so `t = p+1−n ≡ 1 (mod ℓ)` on every instance (verified 300/300 per arm) ⇒ `t mod ℓ`
is degenerate and the first varying ℓ-adic digit is `w = ((t−1)/ℓ) mod ℓ`. That is the `3→ℓ` substitution
of the mediator in the ℓ=3 law **(E3)** `e(π̄′)−e(ν′) ≡ (t−1)/3 (mod 3)`, which is **`[VERIFIED —
12000/12000]`, not proved** (`RESULT_bridge_mechanism_and_constant_v1` states this explicitly). Whether an
ℓ≥5 analogue of E3 exists *at all* is the hypothesis under test — so `w` is a principled pre-commitment,
not a forced consequence.

---

## 0. The instrument was verified before it was aimed (all machinery passes)

| control | result | meaning |
|---|---|---|
| **M0** `Îc`,`Tc` invariant under unit relabelings | **bit-identical** (numpy + pure-Python agree) | both statistics **choice-free** |
| **★ Mc+** synthetic `j=(k+w)`, `w,k` indep uniform | **marginal MI `p≈0.68–0.91`** vs `Îc,Tc` `p=0.0003` | on synthetic ground truth where `j⊥k` marginally, the conditional stats reject and marginal MI does not ⇒ the statistic detects the uniform-shift coupling marginal MI misses (a property of the statistic on synthetic data, not a claim about the arms) |
| **Mc−** / calibration (200 synthetic-null draws) | FPR tracks α: `.05→.035–.055`, `.01→0–.015`, **`.00625→0–.015`** | permutation nulls **exact by exchangeability**, confirmed empirically — no false-positive inflation at the decision threshold |
| **R2** power (uniform-shift injection) | detectable `s`: **Tc ≈0.03 (N=12000) / ≈0.06 (N=8000)**; Îc ≈0.04–0.06 / ≈0.06 | detects a conditional bridge where **~3–6% of instances** follow the law; null (`s=0`) never fires |

Audit-required design (both verified before use): **`Tc` is PRIMARY at ℓ≥11** (measured: at ℓ=13,
N=12000, s=0.03 → Îc 40% vs **Tc 95%** — Îc is under-powered over `ℓ³` cells; Tc carries it); `Îc`
stays as the omnibus that alone catches **non-shift** conditional dependence.

## 1. Calibration on real curves — fires on the known bridge, silent on the controls

| control | ℓ | `Tcond` p | `Icond` p | verdict |
|---|---|---|---|---|
| **C+** D=−3 (bridge known, B1 `[PROVED]`) | 3 | **0.0000** | **0.0000** | fires ✓ (conditional stats catch the ℓ=3 bridge) |
| **C−** D=−11 (no bridge) | 3 | 0.417 | 0.611 | null ✓ |
| **C−r** random base | 5,7,11,13 | 0.73/0.38/0.42/0.37 | — | null ✓ |
| **C-cong** (shared-U congruence, targeted) | 5 | **0.370** | — | null ✓ (N=2500, per-w-stratum min=475) |
| **Mc-cong+** planted positive (s=0.12) | 5 | **0.0000** | — | the C-cong control has power at this N ⇒ its natural null reflects absence of coupling, not no-power |

## 2. The arms, in-sample and out-of-sample

**In-sample** (30-bit `p`, N≈8000, seed 13 — the SAME frozen sample as the marginal probe):

| ℓ | `Tcond` p (primary ℓ≥11) | `Icond` p (omnibus) |
|---|---|---|
| 5 | 0.071 | 0.216 |
| 7 | 0.522 | 0.339 |
| **11** | 0.0071 | **0.0014** |
| **13** | 0.0286 | **0.0015** |

Two arms came in below the 0.00625 Bonferroni gate, driven by the **omnibus `Icond`**, with the
targeted `Tcond` only marginal. Neither was reported as a signal. Two features indicated noise before
the retest: (i) `Icond`
fired *more* than the shift-targeted `Tcond` — the **wrong ordering for a shift bridge** (an actual
shift `j=k+f(w)` favours `Tc`); (ii) the flickers sit at exactly ℓ=11,13 — the **same two arms** the marginal
probe flickered on, on the **same seed-13 sample**. Per the anomaly-drill protocol (OOS retest before
naming; the record already had 4 chance patterns die), both went to a fully independent sample.

**Out-of-sample** (32-bit `p`, fresh seeds; N reduced by 32-bit rarity — see D1):

| ℓ | in-sample (Îc / Tc) | **OOS (Îc / Tc)** | fate |
|---|---|---|---|
| **11** | 0.0014 / 0.0071 | **0.825 / 0.868** | **DIED** — deep null / anti-signal |
| **13** | 0.0015 / 0.0286 | **0.0166 / 0.077** | **DIED** — above the 0.00625 gate |

ℓ=11 landed at `p=0.87` — the far side of the null, so this is not a weak signal lost to power. These
are the fifth and sixth in-sample patterns in this record to fail an out-of-sample retest.

## 3. Result — graded as a bound, with power and scope (not a closure)

> **No conditional bridge between `χ_ℓ(p mod n)` and `χ_ℓ(n mod p)` mediated by `w = (t−1)/ℓ mod ℓ`
> is detectable at ℓ = 5,7,11,13 — by a choice-free stratified MI (`Îc`) or a choice-free targeted
> conditional-shift statistic (`Tc`), out-of-sample.**  `[VERIFIED — bounded]`

The added capability is measured, not asserted: the conditional statistic rejects on the synthetic
uniform-shift coupling that marginal MI misses (Mc+: p=0.0003 vs ≈0.7), and it fires on the ℓ=3 bridge
(C+: p=0.0000). Quantitatively (R2): any conditional bridge copying `≳ 6%` of instances (the OOS-achieved
floor, D1) would have fired; none did.

## 4. Scope — pre-committed, stated as bounds

- **One mediator.** This bounds conditioning on `w = (t−1)/ℓ mod ℓ` (the E3 generalization). A conditional
  bridge mediated by a **different** reduction of the ideal data — `v mod ℓ`, the second ℓ-adic digit
  `(t−1)/ℓ² mod ℓ`, or **global (non-residue) structure** of `(t,v)` — is **out of scope**. That a
  general-ℓ analogue of the E3 law exists *at all* is the hypothesis; no ℓ≥5 law is proven.
- **Power at the achieved OOS N.** The bound is at ~6% copy-fraction (D1: OOS build fell short of N=12000
  at 32-bit). A conditional bridge below ~6% remains **formally unexcluded** — not closed.
- **Rational, not ideal.** Still the rational exponents `(j,k)`; nothing here touches ℓ-th power
  reciprocity in `ℚ(ζ_ℓ)` at the ideal level (Lemmermeyer Ch. 7 — classical), where a relation at the
  ideal level can wash to rational independence, marginal *or* conditional.
- **Small ℓ only.** secp's own factors `149, 631, …` stay out of MI reach (`ℓ²`×`ℓ` cells).

## 5. What this closes and what it opens

**Bounds (not closes):** the specific alternative §4 of the marginal probe left open — *"a
purely-conditional ℓ≥5 bridge via the natural ideal residue could be hiding"* — is **bounded away at the
tested mediator and the achieved power**, with an instrument shown (Mc+) to reject on exactly that
synthetic case. The `D=−3` bridge is not detected past ℓ=3 by either a marginal or a conditional
statistic (a bound at these ℓ / this power, per §4 — not a proof of non-existence).

**Opens (the leads, per §4):** the **other mediators** — `v mod ℓ`, the second ℓ-adic digit,
global `(t,v)` structure — each a distinct conditional channel this probe did not aim at; and the
**ideal-level symbol** in `ℚ(ζ_ℓ)`, where the general power-reciprocity law actually lives and which no
rational-exponent test (marginal or conditional) can reach. Both are named as bounds to push on, not
closed doors.

## 6. Prior art / grade

Exploration, not a novelty claim (no gate tripped). The contribution is a **measurement with a new,
verified conditional instrument** (choice-free stratified/targeted MI; Mc+ shows it rejects the synthetic
uniform-shift coupling marginal MI misses; FPR tracks α; C+-validated on the ℓ=3 bridge). The general
power-reciprocity law is classical. Public data only; no leakage / ECDLP content.
