# DEVIATIONS — PREREG_ell_ge5_conditional_MI (v1→v2 and run)

Filed as they occurred. None changes a verdict (all arms null in + OOS); all are recorded plainly.

## D0 (pre-data spec revision, NOT a deviation) — v1→v2 after the mandated audit
`experiment-designer` audited v1 before any arm ran and returned two required fixes (Tcond primary at
ℓ≥11 + per-arm power gate; C-cong planted positive + adequate stratified N). Both verified independently
before acting (`ell_condmi_verify_designer_v1.py`: common-U identities 300/300; Icond-vs-Tcond power
split confirmed at ℓ=11,13) and folded into v2. This is the intended workflow (pre-data revision after a
mandated audit), not p-hacking.

## D1 — OOS build fell short of the target N (32-bit prime-order-twist rarity)
Target OOS `N=12000`; **achieved `ℓ=11 → N=6893`, `ℓ=13 → N=7851`** (build hit its `tries` cap; at
32-bit the double-primality + congruence conditions make prime-order CM instances rare). Consequence:
the OOS power floor is **~0.06 copy-fraction (matching N≈8000), NOT the 0.03 measured at N=12000** — the
`FLOOR[12000]` values the script printed for the OOS arms **overstate power**; the OOS bound is at
the N≈7000 floor (~0.06). This does **not** rescue the flickers: `ℓ=11` OOS landed at `p=0.868/0.825`
(the statistic sits on the far side of the null, so this is not a missed weak signal — a real bridge
would push `p` down), and `ℓ=13` died by the pre-committed rule
(`p=0.0166 > 0.00625`). A weak conditional bridge below ~6% copy-fraction remains formally unexcluded —
stated as the scope of the bound, not a closure.

## D2 — C-cong construction bug: `U = |t−1|` is ALWAYS divisible by ℓ (forced by `t ≡ 1 mod ℓ`)
The v2 `build_ccong` first copied the marginal probe's guard `U % ell == 0: continue` (and a CRT step
needing `U` invertible mod ℓ). But the **forced degeneracy `t ≡ 1 mod ℓ` makes `U = |t−1| ≡ 0 (mod ℓ)`
for every instance**, so that guard skipped 100% of instances ⇒ **C-cong N=0**. Root cause is deeper than
the marginal probe's earlier `gcd(rr,U)>1` N=0 (same *symptom*, different *cause*). **Fix:** since `ℓ∣U`,
`P ≡ Q (mod U)` already forces `P ≡ Q (mod ℓ)`; draw `rr ≡ 1 (mod ℓ)` coprime to `U` and walk by
`step = U` (the mod-ℓ condition is subsumed; no CRT inverse). Post-fix: **N=2500, per-w-stratum min=475**,
natural C-cong Tcond `p=0.37` (null), **`Mc-cong+` planted positive (s=0.12) fires `p=0.0000`** ⇒ control
shown to have power. **Non-load-bearing here** (all arms null ⇒ nothing to attribute), but fixed and
demonstrated per the audit's required addition, and recorded because a broken control must never pass
silently. Recurring lesson: the C-cong shared-modulus construction is fragile; verify `N>0` and a planted
positive every time before trusting a C-cong null.

## D3 — in-sample flickers coincide with the marginal probe's, on the SAME frozen sample
The in-sample arms reuse seed-13 / 30-bit / N≈8000 — the **same frozen sample** the marginal probe used.
Both probes flickered at **exactly ℓ=11 and ℓ=13** in-sample (marginal MI 0.0021/0.013; conditional Icond
0.0014/0.0015) and **both died OOS on independent data**. This corroborates the noise reading: a
sample-specific fluctuation of this particular ~8000-point draw, not a mediator-specific signal. Not a
deviation from spec; logged because it strengthens the null interpretation.
