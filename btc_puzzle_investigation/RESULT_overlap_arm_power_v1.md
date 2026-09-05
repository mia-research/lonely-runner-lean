# Planted-positive control for the OVERLAP arm of `lift_band_spectral_v1.py` (v1, 2026-07-23)

**Object:** the third arm of `lift_band_spectral_v1.run_curve` — the block that correlates each curve
readout's low-frequency power spectrum against the band targets `derr` and `k_den`, ranks the Pearson
`rho` against a 200-permutation null of the curve vector, and prints `|z|`. That arm shipped a matched
NULL (`shuffle_floor`, permutation of `cvec`) and **no planted positive**. Per
`btc_puzzle_pubkey_relations_controlled_2026_07_18` — *audit old nulls for a firing control before
trusting them* — it was in the flagged category, and `RESULT_lrc_null_typing_transfer_v1.md` §2.3
typed its null **conditionally void** pending exactly this measurement.

**What this file adds:** the missing firing control, and the arm's detection floor measured in the
same observable the arm already prints for real readouts.

**Decidable artifacts:**

| artifact | sha256 |
|---|---|
| `overlap_plant_exact_v1.py` (exact-int signal path) | `de9c7ded43027f937e6fdd0547f519012487f39d26c060d6e9d578b187625abf` |
| `overlap_arm_power_v1.py` (statistic layer + sweep) | `a562acb3ef543380c5de40b4be3715aca1df34e74e655bb9a10879efd47d4bc7` |
| `lift_band_spectral_v1.py` (arm under test, unmodified) | `31a48b8ac25078eb2041e15205a5f2cc0968518e5aa0e42acb3a8f4f4460fb22` |

Environment: Python 3.14.3, numpy 2.3.3. The arm under test was **not modified**; its statistic
(`overlap_z`) is reproduced verbatim and its threshold (`|z| > 3`) and null size (200 permutations)
are used as written.

---

## 0. Headline

**The arm can fire.** It is not a dead statistic. But its detection floor, expressed in the units the
arm already reports, sits **above where every real curve readout was measured** — so §2.3's conjecture
is confirmed quantitatively: the observed null was determined upstream by the readouts' flatness, not
by an independent test of coupling.

Two further findings fell out of the control, both of which change how the arm's own output should be
read:

1. the **`derr` leg of the arm has essentially no power at all** — it does not fire below `f = 0.7`,
   and at `L ≥ 4096` only at the degenerate `f = 1` where the plant *is* the target;
2. the arm's `|z| > 3` rule is empirically a **2.0 %–4.75 % test, not a 0.27 % test**, so across the
   36 comparisons the arm prints, ~1 spurious flag is *expected* — and exactly 1 was observed.

---

## 1. Method

### 1.1 The plant

```
plant(f) = f · (band target)  +  (1 − f) · (white component)
```

built so that the two components carry **equal l2 weight** before mixing, then swept over
`f ∈ {1, 0.7, 0.5, 0.35, 0.25, 0.18, 0.12, 0.09, 0.06, 0.04, 0.03, 0.02, 0.015, 0.01, 0.007, 0.005,
0.003, 0.002, 0.001, 0}` and fed into the arm as if it were a curve readout.

Two families, because "white" admits two readings:

| family | white component | what it answers |
|---|---|---|
| **PLANT A** | a random permutation of the target itself | exactly variance- **and** value-multiset-matched; 40 independent draws per `f`, so the rate is a real power estimate |
| **PLANT B** | an **actual** curve readout (`eis_u, eis_v, norm_s, flap_eps, sextant, sign_xy`) | the faithful counterfactual: *if this real readout had carried fraction `f` of `k_den`, would the arm have seen it?* 6 draws per `f` (one per readout) |

`f = 0` degenerates to the arm's own null, so the `f = 0` row is the control-of-the-control.
`f = 1` degenerates to `plant ∝ target`, giving `rho = 1.000` by construction — **that row is a
tautology and is not evidence of power**; it is reported only to confirm the wiring.

### 1.2 Numerical integrity (`btc_puzzle_investigation/CLAUDE.md`)

The signal path was split into its own module so it is separately checkable:

```bash
bash check_no_float.sh overlap_plant_exact_v1.py
```

→ `OK` (exit 0). Targets, curve readouts and the planted mixture are Python `int`; the l2 scale
matching uses `isqrt` and `Fraction.limit_denominator(256)` — an exact bounded-denominator rational,
never a float ratio. `selftest()` verifies, across 72 plant configurations per curve, that every
planted element is `int`, equals an independent `Fraction` recomputation, and satisfies
`|plant| < 2^52`; observed maxima were `2^27 / 2^29 / 2^32` for `L = 1024 / 4096 / 16384`, so the
float64 FFT downstream loses no bits of the integer signal.

Float enters only as the monotone statistic (power spectrum → Pearson `rho` → `z`), ranked against
the same matched permutation null the arm itself uses. No float threshold touches the data.

The parent `lift_band_spectral_v1.py` does **not** pass `check_no_float.sh` — but neither is it in
the guard's default exact-era set; it is a statistic file. The split above is what makes the exactness
claim here decidable rather than asserted.

---

## 2. Result — the arm fires, and where

Detection floor = smallest `f` in the grid reaching the stated detection rate at the arm's own
`|z| > 3`. Values are grid points, so the true floor is bracketed between adjacent grid entries.

| curve `L` | target | plant | `f_min` @ rate ≥ 0.50 | `f_min` @ rate ≥ 0.95 |
|---|---|---|---|---|
| 1024 | `derr` | A | 0.70 | 1.00 *(degenerate)* |
| 1024 | `derr` | B | 0.70 | 1.00 *(degenerate)* |
| 1024 | `k_den` | A | 0.35 | 0.50 |
| 1024 | `k_den` | B | 0.35 | 0.50 |
| 4096 | `derr` | A | 1.00 *(degenerate)* | 1.00 *(degenerate)* |
| 4096 | `derr` | B | 1.00 *(degenerate)* | 1.00 *(degenerate)* |
| 4096 | `k_den` | A | 0.25 | 0.35 |
| 4096 | `k_den` | B | 0.18 | 0.35 |
| 16384 | `derr` | A | 1.00 *(degenerate)* | 1.00 *(degenerate)* |
| 16384 | `derr` | B | 1.00 *(degenerate)* | 1.00 *(degenerate)* |
| 16384 | `k_den` | A | 0.18 | 0.25 |
| 16384 | `k_den` | B | 0.18 | 0.35 |

**`k_den` leg:** live. Floor `f ≈ 0.18–0.35` at 50 % power, `f ≈ 0.25–0.50` at 95 %, improving
monotonically with `L`. A curve readout carrying ~a fifth of `k_den`'s low-frequency structure would
have been caught half the time at `L = 16384`.

**`derr` leg:** the two plant families agree that it does not fire below `f = 0.7`, and at
`L ≥ 4096` the only firing row is the degenerate `f = 1`. The reason is visible in the arm's own
printout: `derr`'s low-frequency excess is **0.1–0.2×**, i.e. *below* the white floor, so the
reference vector `dref` on that leg is itself sub-floor noise and the correlation has noise on
**both** sides. `[VERIFIED]` — the `derr` half of the arm carries no detection power at these
`(L, kmax)`; its published rows are uninformative in both directions.

---

## 3. The bridge — the floor in the units the arm already prints

The arm prints a `low-freq excess` column for every real readout. The sweep reports the same
statistic for each planted sequence, putting plants and real readouts on one scale.

| detection rate | planted low-freq excess at that rate (`k_den` leg, across `L` and both families) |
|---|---|
| ≥ 0.95 | **2.0× – 3.7×** |
| ≈ 0.50 | **1.4× – 2.2×** |
| ≈ 0.15–0.35 | 1.1× – 1.65× |
| ≈ 0 (= size) | ≤ 1.0× |

Real curve readouts, as measured by the arm itself, `L = 1024 / 4096 / 16384`:

```
eis_u   0.5 / 1.0 / 1.2      flap_eps  1.0 / 1.1 / 0.9
eis_v   1.4 / 1.0 / 0.9      sextant   1.4 / 0.7 / 0.8
norm_s  1.4 / 1.1 / 0.7      sign_xy   1.0 / 0.6 / 1.3
```

**All 18 real readouts sit at ≤ 1.4×, median ≈ 1.0×** — i.e. at or below the level where the arm's
detection rate is indistinguishable from its size. `[VERIFIED]`

This is the settling measurement §2.3 called for. The overlap null is **not** an independent
observation about coupling between the lift readouts and the band: at the low-frequency excess the
readouts actually exhibit, the arm has ~no power, so a null was the near-certain outcome regardless of
whether coupling exists. The typing "conditionally void" in `RESULT_lrc_null_typing_transfer_v1.md`
§2.3 is upheld, now with a number attached rather than an inference from §2.1.

---

## 4. Threshold calibration — a correction to how the arm's output reads

The arm's `z` is a rank against 200 permutations of a **32-element** vector, not a gaussian z-score.
Its actual size was measured directly with 400 independent `f = 0` plants per cell:

| `L` | target | draws | hits | **FP rate** | q95 \|z\| | q99 \|z\| | max \|z\| |
|---|---|---|---|---|---|---|---|
| 1024 | `derr` | 400 | 8 | 0.0200 | 2.57 | 3.25 | 3.81 |
| 1024 | `k_den` | 400 | 12 | 0.0300 | 2.74 | 3.64 | 4.66 |
| 4096 | `derr` | 400 | 10 | 0.0250 | 2.67 | 3.29 | 3.83 |
| 4096 | `k_den` | 400 | 19 | **0.0475** | 2.94 | 3.87 | 4.71 |
| 16384 | `derr` | 400 | 15 | 0.0375 | 2.77 | 3.90 | 5.23 |
| 16384 | `k_den` | 400 | 14 | 0.0350 | 2.77 | 3.64 | 4.30 |

`|z| > 3` is a **2.0 %–4.75 % test per comparison** (pooled `78/2400 = 3.25 %`), not the 0.27 % a
gaussian reading implies. The arm prints 36 comparisons (6 readouts × 2 targets × 3 curves), so under
the pure null the expected number of `|z| > 3` flags is `36 × 0.0325 ≈ 1.2`, and the probability of at
least one is `1 − (1 − 0.0325)^36 ≈ 70 %`. A single flag from this arm is therefore **not** evidence of
a shared mode. `[VERIFIED]`

Cross-check on real readouts: the calibration above uses permutation noise, which carries the
*target's* value multiset rather than a readout's. The PLANT B `f = 0` rows use the six **actual**
readouts and give 1 hit in 36 (`= 2.8 %`) — consistent with the pooled 3.25 %, so the size estimate is
not an artifact of the noise family.

### 4.1 Factual correction to the recorded summary

`lift_band_joint_findings_v1.md:78` records the arm's outcome as *"every |z| < 1.8 across all three
curves."* Re-running `lift_band_spectral_v1.py` unmodified at the environment above, that is not what
the arm prints: at `p = 8209`, `k_den × sign_xy` gives **`rho = +0.530, z = +3.0`** — which trips the
script's own `<-- overlap above floor` flag. Two other rows exceed 1.8 (`k_den × eis_u`, `z = +2.0` at
`p = 33343`; `norm_s`, `z = +1.7`).

Per §4 this single flag is within the ~1.2 spurious hits expected under the null and should not be
read as structure. But the recorded number is wrong as stated and the qualifier "every" does not hold.
`[VERIFIED — current run; the source of the 1.8 figure is not established, and no claim is made about
what an earlier run produced]`

---

## 5. Scope and limits

- **Scope of the floor.** Toy prime-order curves `p ∈ {2143, 8209, 33343}`; bands `A = 2^10, 2^12,
  2^14`; Farey caps `M ∈ {32, 48, 64}`; `kmax = 16` (32-element low-frequency vector); threshold
  `|z| > 3`; 200-permutation null; 40 draws (A) / 6 draws (B) per `f`. Nothing here transfers to the
  256-bit band or to other `kmax` without re-measurement.
- **Alternative class.** The plant is an **additive** mixture in the sequence. A readout could share
  `k_den`'s spectral shape without being an additive mixture of it (e.g. a nonlinear or
  frequency-selective coupling). The floor is a floor **against additive-mixture alternatives**, and
  says nothing about detection power against alternatives outside that class.
- **Grid resolution.** `f_min` entries are grid points; the true floor lies between adjacent entries.
- **Rate resolution.** PLANT B's rate is over 6 readouts, so its resolution is 1/6; the `0.17` cell at
  `L = 4096` is one readout (`sign_xy`), not a rate estimate. PLANT A's 40 draws carry the power
  claims; PLANT B carries the counterfactual framing.
- **What this does not do.** It does not test whether coupling exists. It measures what the arm could
  have seen. Establishing the presence or absence of a shared mode requires a readout with
  above-floor low-frequency mass, or a statistic that does not take the readout's low-frequency
  spectrum as an input.

---

## 6. Consequences for the record

| item | before | after |
|---|---|---|
| overlap arm's null | listed alongside the Part-1 grid as an independent confirmation | **uninformative at the readouts' measured excess**, with a measured floor: needs ≥ ~1.4× (50 % power) / ≥ ~2.0× (95 %) vs. real readouts at ≤ 1.4×, median 1.0× |
| `RESULT_lrc_null_typing_transfer_v1.md` §2.3 typing | `[VERIFIED]` that the arm has no plant; "could not have fired" argued from §2.1 | typing **upheld and quantified**; "could not have fired" now rests on a measured power curve, not on an inference |
| `derr` leg of the arm | reported alongside the `k_den` leg | **no detection power** at these settings; both sides of that correlation are sub-floor noise |
| arm's `|z| > 3` threshold | read as a 3-sigma rule | a **2–4.75 % test**; ~1.2 spurious flags expected across the 36 printed comparisons |
| "every \|z\| < 1.8" | recorded in `lift_band_joint_findings_v1.md:78` | **does not hold** in the current run (`z = +3.0` at `p = 8209`); the flag is within the arm's own noise |
| the arm itself | untested for power | **can fire** — floor `f ≈ 0.18` at `L = 16384`, `k_den` leg |

**No claim is retracted about the band or the curve.** `k_den`'s low-frequency capacity
(5.4× → 12.2× → 28.0×, stable top mode) is untouched, as is the Part-1 magnitude bound. What changes
is what the overlap arm's null licenses.

**No ECDLP content.** Everything measured here is the power of a statistic applied to spectra in `d`.
No claim is made about recovering `d`, and no avenue is closed — a measured detection floor is a
statement about this arm at this scope, not about whether the coupling it was pointed at exists.

---

## 7. Grades

| item | grade |
|---|---|
| the overlap arm can fire (plant detected at rate 1.00 for `f ≥ 0.35`, `k_den`, `L = 16384`) | `[VERIFIED]` — 40 independent draws, arm unmodified |
| detection floor `f ≈ 0.18–0.35` @ 50 %, `0.25–0.50` @ 95 % (`k_den` leg) | `[EMPIRICAL, scoped]` — grid-resolved, scope in §5, controls fired |
| floor in printed units: ≥ ~1.4× excess @ 50 %, ≥ ~2.0× @ 95 % | `[EMPIRICAL, scoped]` |
| all 18 real readouts at ≤ 1.4× excess, median ≈ 1.0× | `[VERIFIED]` — the arm's own printout |
| the overlap null was determined upstream, not independently | `[ARGUED from two VERIFIED rows]` — floor above the readouts' measured level |
| `derr` leg has no detection power at these settings | `[VERIFIED]` — fires only at degenerate `f = 1` for `L ≥ 4096`, both families |
| `\|z\| > 3` has empirical size 2.0 %–4.75 % | `[VERIFIED]` — 400 draws/cell, 6 cells |
| `lift_band_joint_findings_v1.md:78` "every \|z\| < 1.8" is wrong for the current run | `[VERIFIED]` — unmodified re-run, `z = +3.0` |
| exact-int signal path | `[VERIFIED]` — `check_no_float.sh` OK on `overlap_plant_exact_v1.py`; `Fraction` cross-check; max `\|plant\| = 2^32 < 2^52` |
| power against non-additive coupling | `[UNTESTED]` — outside the plant's alternative class (§5) |

*Grade legend: PROVED · VERIFIED (exact/numeric at scale) · ARGUED · EMPIRICAL (scoped, controls
fired) · HYPOTHESIS · CITED · UNTESTED.*

---

## 8. Reproduce

```bash
cd btc_puzzle_investigation && bash check_no_float.sh overlap_plant_exact_v1.py && python3 overlap_arm_power_v1.py
```

Runtime ≈ 75 s. Deterministic — every draw is a seeded `np.random.default_rng`.
