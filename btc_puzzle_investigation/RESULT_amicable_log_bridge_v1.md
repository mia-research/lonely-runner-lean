# RESULT — amicable log-bridge: the decidable sub-question is NULL (scoped magnitude bound) (v1, 2026-07-24)

**Spec:** `PREREG_amicable_log_bridge_v1.md`. The posed "transfer map" was refuted **pre-data** as
undecidable (§0: the full φ(n)-average is the trivial operator; the log coordinate is the discrete log;
`Hom = 0`). This run tests the registered decidable **sub-question**.
**Deviations:** `PREREG_amicable_log_bridge_v1_DEVIATIONS.md`.
**Script:** `amicable_log_bridge_v1.py`. Run: `amicable_bridge_discovery_run_v2.out`.

---

## 1. The registered sub-question

Does the μ₆-averaged cubic-character pairing between the **field-side** class
`F(P) = χ₃^{(p)}(y(P))` (built from public coordinates only) and the **partner-side** class
`g(d) = χ₃^{(n)}(d³+7)` show **amicability-specific** dependence, beyond matched non-amicable controls?

Statistic (exact `Z[ω]`, no float): `T = (n−1)Σ_d F(P_d)conj(g(d)) − Σ_F conj(Σ_g)` (double-centred),
`R = N(T)/((n−1)²n)`, per-unit rank `π(u)` vs NULL-A (μ₆-equivariant relabel of `F`), primary =
Mann-Whitney of `π` over the **amicable arm vs a matched non-amicable control arm**.

---

## 2. Result — NULL

```
frame (p < 50000): 90 amicable 2-cycle units, 189 non-amicable, 85 matched amic<->control pairs
forced rows (F(P_λd)=F(P_d), F(P_-d)=F(P_d), g(λd)=g(d)):  0 failures on every unit
PLANT (synthetic transfer, largest unit p=49549):  FIRES, eps_min = 1/25   [arm not void]

PRIMARY Mann-Whitney (amicable pi vs control pi):
  n_amic=85  n_ctrl=85   U=3786.5  E[U]=3612.5  z=+0.542     (|z|>2.58 to reject at 0.01)
  median pi:  amicable 0.438   control 0.534
  restricted to resolving units:  z = +0.26   (robust; no large-n signal diluted by tiny units)
```

**Pre-committed conclusion (§9 cell 3): the bridge hypothesis is FALSIFIED at the measured power.**

> The μ₆-averaged cubic-character pairing between the field-side `Z[ω]` class of `y` and the
> partner-curve `Z[ω]` class of the scalar shows **no amicability-specific dependence** above the
> detection floor **ε_min ≈ 1/25**, at `p < 50000`, `y²=x³+7`, 85 matched amicable/non-amicable pairs,
> α = 0.01. `z = +0.54`.

The faint hint (amicable median π 0.438 < control 0.534) is `< 1σ` and is **not** an effect; it does
not survive as significance at any unit-size cut.

**This is a scoped magnitude bound, not a closure.** The words *closed / no leakage / benign / generic
/ tautological / at-the-floor* are barred per the spec. What it bounds: amicability-specific coupling
in **this one** pairing (cubic order, `y`-coordinate, μ₆-averaged), at `ε_min ≈ 1/25`, `p < 50000`.

---

## 3. What the null does NOT cover (§10, restated)

- **No transfer map was built or tested** — §0b: the posed map contains the ECDLP in its construction.
  This tests a *dependence*, which requires `d` as an input, and licenses **no** statement about an
  observer holding `P` alone.
- **μ₆-anti-invariant effects are outside the statistic by construction** (`F` is forced μ₆-invariant),
  named and untested.
- **One character order (3), one coordinate (`y`).** Orders `k ≠ 3` were EXPLORATORY-only (not run);
  `χ₃^{(p)}(x(P))` is excluded because it is forced to 0 whenever `9 ∤ p−1` (§2 trap).
- **`Hom = 0` untouched.** Nothing here weakens or extends it.
- **Nothing at `2²⁵⁶`.** `p < 50000` is ~236 binary orders below secp. **No ECDLP/key/security claim.**

---

## 4. Deviations material to reading this

- **M = 2000, not the frozen 9999** (per-unit `π` only feeds the Mann-Whitney; decision unaffected,
  min attainable p = 1/2001 < 0.01). 
- **Replication (`50000 ≤ p < 200000`) and out-of-sample (`≥ 200000`) decades NOT run.** The null is
  therefore **discovery-scoped**; per §6.2 a *positive* would need those decades to be named, but this
  is a null bound, reported as discovery-scoped.
- **Tiny units carry no resolution** (`ε_min ≈ 3/√n`; at n=79, ≈0.34). The 85-pair pool mixes resolving
  and non-resolving units; the restricted-to-resolving cut gives the same null (z=+0.26), so this does
  not hide a signal.
- **§3.3 argument-sector / contingency structural readouts** were computed only as raw `T` values, not
  tabulated by sector. For a `<1σ` null this does not change the verdict, but the full shape readout is
  owed if the question is revisited.

---

## 5. Net

| object | status |
|---|---|
| posed φ(n)-bridge transfer map | **undecidable — refuted pre-data** (`RESULT_plays_1_and_4_refuted_predata_v1.md`) |
| decidable sub-question (μ₆-averaged cubic pairing, amicable vs control) | **NULL, z=+0.54**, scoped bound ε_min≈1/25, p<50000 |
| plant / forced rows | plant fires (ε_min=1/25); forced μ₆-invariance exact (0 failures) |

*Grade legend: PROVED · VERIFIED (exact) · EMPIRICAL (scoped null, controls fired) · REFUTED.*
