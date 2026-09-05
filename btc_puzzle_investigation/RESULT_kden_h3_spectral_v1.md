# RESULT — H3: the Ramanujan-comb SPECTRAL hypothesis is REFUTED; the level-set phases are incoherent (v1, 2026-07-23)

**Spec:** `PREREG_kden_ramanujan_comb_v1.md` §2.5–2.6, §3, §4.2. **Branch A applies** (H2b confirmed
exactly), so per §7 this arm is **CHARACTERIZATION ONLY** — no `p` from it is independent evidence.
Per §0.3 F-1 the forced predicted-vs-observed spectrum correlation was **not** computed.
**Run:** `kden_h3_spectral_v1.py` → `kden_h3_run_v1.out`.

---

## 1. Headline — the pre-registered falsification clause fires

§6: *"HYP-S is KILLED if … **`R2_ram < 0.30` on a majority of C while `ΔR2 ≤ 0`**."*

```
config:   W1      W2      W3      W4      T1      T2      T3      T4
R2_ram   -0.394  -0.366  -0.349  -0.426  -0.109  -0.066  -0.182  -0.351
R2_flat  +0.309  +0.294  +0.281  +0.259  +0.091  +0.076  +0.064  +0.061
ΔR2      -0.703  -0.660  -0.630  -0.685  -0.201  -0.141  -0.246  -0.412
```

`R2_ram < 0.30` on **8/8** and `ΔR2 ≤ 0` on **8/8**. **HYP-S is KILLED.**

`R2_ram` is *negative* everywhere — the coherent comb model fits worse than a constant — while the
**incoherent** `FLAT(f) = Σ_q q²·Ŵ(w̄_q,f)²·φ(q)` model is positive everywhere. **The `φ(q)` intervals
of a given `q` do not share a common width, so the Ramanujan-sum coherence assumption fails.** The
geometry *is* a primitive-`j/q` comb (H2b, exactly), but its **phases add incoherently**.

This is precisely the content §0.3 F-1 identified as the part HYP-G does *not* force — and it came
back negative. **The mechanism I proposed for the `|f| = 24` mode is refuted by its own test.**

`S_ram = −2.24`, rank 0/999 → "fires" by the letter of the threshold, but the direction is
uninformative: it says the comb model fits the *real* sequence better than it fits run-permuted ones,
while fitting all of them badly. It does not rescue HYP-S, and the `or`-clause above is unconditioned.

---

## 2. `H3-top`: **0/8 hits.** The `12/24/24` reading does not survive the harder null

`TOP3_pred` (hashed before `P_obs` existed) vs the observed top above-floor mode:

| | W1 | W2 | W3 | W4 | T1 | T2 | T3 | T4 |
|---|---|---|---|---|---|---|---|---|
| predicted | 12,70,31 | 12,31,34 | 12,41,37 | 24,72,30 | 12,60,48 | 60,12,154 | 120,48,36 | 120,48,36 |
| observed | 1363 | 255 | 492 | 1026 | 301 | 285 | 3880 | 2871 |

**Do not read this as contradicting the prior `|f| = 12/24/24`** — it is a *different estimator against
a different null*. The prior figure was `argmax P/Null-0` (value shuffle, `kmax=16`); this is
`argmax P/Null-1` over `f ∈ [1,F_max]`, where **Null-1 preserves the run-length multiset and
piecewise-constancy** and only destroys Farey placement.

That difference is the point, and it is a **scope correction on the prior finding**: piecewise
constancy *by itself* produces low-frequency mass, so a low-frequency top mode measured against a
value-shuffle floor can be an artifact of run structure rather than of arithmetic placement. Under the
null that controls for run structure, the top mode is not at a small highly-composite `f`. The spec
demanded Null-1 for exactly this reason. **The `12/24/24` mode is now a candidate artifact of the weak
null** — stated as a testable correction, not as a refutation of the measured numbers.

---

## 3. What IS positive: a divisor-structure effect survives Null-1

`Δ_HC` (mean `log P_obs` on the top decile of `D_M(f) = Σ_{q≤M, q|f} φ(q)` minus the rest), pooled
over the 8 configs: **`+3.46`, rank 0/999** against Null-1. Per-config `Δ_HC` is positive on 6/8
(`W2 +0.20, W4 +0.33, T1 +0.17, T2 +0.76, T3 +1.08, T4 +1.28`; negative on `W1 −0.19, W3 −0.15`).

So **frequencies divisible by many `q ≤ M` do carry excess log-power**, above a null that already
preserves run structure. There is a real divisor-indexed effect on the spectrum — it is simply **not**
the coherent Ramanujan-comb one. Branch A: characterization only, no independent evidential weight.

**`H3-resid`** (residual `log P_obs − log RAM` against `q`-sub-family combs) is mildly negative for
every sub-family, most for **squarefree `q`** (`−0.26 … −0.35`) and least for **`q | A`**
(`−0.04 … −0.09`). No sub-family carries the residual; it is not a matter of projecting onto the wrong
`q`-family.

---

## 4. Controls — the arm is VOID on part of `C`, and under-controlled elsewhere

| control | status |
|---|---|
| **PC-comb** on W1/W2/W3 | **FIRES** (`R2_ram(synthetic)` = 0.935 / 0.905 / 0.972, rank 0/199) |
| **PC-comb** on T1/T2 | **FAILS** (`R2_ram(synthetic) = 0.0052`, far below the required 0.80) |
| **PC-comb** on W4/T3/T4 | **NOT RUN** |
| **PC-comb-α** (detection floor) | **NOT RUN** |
| **PC-neg** (false-positive gate) | **NOT RUN** |

Per §4.2, PC-comb failure ⇒ **VOID**. So:

- **T1, T2: the H3 arm is VOID.** The readout could not see a comb handed to it. Their cells above
  carry no weight.
- **W4, T3, T4: uncontrolled** — no plant was run at all.
- **W1, W2, W3: controlled and valid.** The HYP-S kill rests on these three, where `R2_ram` is
  `−0.35 … −0.43` against `R2_flat ≈ +0.28 … +0.31`. The kill is unambiguous on the controlled subset.
- **`S_ram` and `Δ_HC` "fired" without PC-neg**, so their false-positive rate is **uncalibrated**.
  Both are reported as characterization with that caveat attached, not as calibrated detections.

**Likely cause of the T1/T2 plant failure, for the record:** `F_max = min(2M², A/2)`; on the T-block
`2M² > A/2`, so `F_max = A/2` and the model is asked to fit the **entire Nyquist band**, including the
high-frequency region where the equal-width window approximation is worst. On the W-block
`F_max = 2M² ≪ A/2`, a low-frequency window. This is a design defect in the frozen `F_max` rule, not a
property of the data.

---

## 5. Net

- **HYP-G (geometry):** comb of `φ(q)` primitive intervals — **verified exactly, and derivable**
  (`RESULT_kden_ramanujan_comb_v1.md`). Unaffected by anything here.
- **HYP-S (spectrum):** equal-width Ramanujan factorization — **KILLED** by its own pre-registered
  clause, on the controlled subset.
- **The `|f| = 24` mode remains unexplained**, and is now additionally a candidate artifact of the
  weak Null-0 floor used to measure it.
- **Open:** re-run `H3-top` and the legacy excess under Null-1 with a corrected `F_max` rule
  (low-frequency window on every config), plus PC-comb on all 8, PC-comb-α, and PC-neg. Until then no
  calibrated spectral statement is available.

**No curve, lift, or `d`-side content.** `k_den` is a function of `d` alone. **No ECDLP content.**
