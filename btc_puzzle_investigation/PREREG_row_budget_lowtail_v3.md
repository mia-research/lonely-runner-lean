# PREREG v3 — the row budget and the low tail: calibrated gates, the constant test, and a correction

**File:** `PREREG_row_budget_lowtail_v3.md` **Date:** 2026-07-25 **Status: PRE-RUN (frozen).**
**Predecessors:** `PREREG_row_budget_lowtail_v1/v2.md`, `RESULT_row_budget_lowtail_v1/v2.md`.
**Calibration artifacts (all numbers below are computed, not asserted):**
`row_budget_v3_calib_v1.py`, `_v2.py`, `_v3.py` and their `.log` files.

Frontier **§XI.17**, twice abstained, zero verdicts. This spec exists to change that, and it starts by
correcting the predecessor's account of *why* it abstained.

---

## 0. GRADE CAPS AND CONTAMINATION LEDGER

Carried from v2 §0 **in full and unchanged** — every quantity v2 labelled SEEN stays SEEN. v3 adds
nothing to the unseen pool and **removes** items from it. No curve may be added; the frozen 10-prime
list is binding, so **Arm A still has no out-of-sample set and cannot acquire one.**

| quantity | status entering v3 | consequence |
|---|---|---|
| everything v2 §0 marked SEEN | **SEEN** | unchanged |
| all v2 control output: P-DET-A criteria 1–5, `C-SELFZ`, `C-DISP`, the 640 unplanted-carrier `z` and their per-prime `sd`/`max`/`frac` | **NOW SEEN** (printed in `RESULT_v2` §2–§3 and held in `row_budget_v2_rows.json`) | v2 called these UNSEEN; after v2's run they are not. **P-SIZE' and every gate in §5 was designed from first principles and its behaviour on these values is declared in advance (§4), not discovered after.** |
| A3 per-prime layer values at `p ∈ {163, 433, 991, 2089, 4159, 9319, 19231}` | **NOW SEEN** (`RESULT_v2` §3 table) | A3' confirmatory only on the complement |
| A3 per-prime layer values at `p ∈ {211, 349, 577}` | **UNSEEN** — not printed anywhere | **the only genuinely unseen Arm-A quantity in this spec** |
| Arm B test set `p ∈ {163, 211, 349, 433, 991}`, `c=0`/`b=0` | governed by **O-B4**; the D7 attestation does not exist | Arm B is **descriptive**, carried unchanged from v2. It is not re-litigated here. |

**Arm A maximum grade, unchanged:** `[EMPIRICAL — SEEN-DATA, CONTROL-REPAIRED; 10 model primes
163…19231, generic μ₆×conj stratum, `N_LOW` at `ρ<0.01`, nulls MN-μ6/MN-neg/MN-free]`.
**Nothing transfers to `p = 2²⁵⁶−2³²−977`.**

---

## 0b. ★ CORRECTION TO `RESULT_row_budget_lowtail_v2.md` §3 — load-bearing

v2's RESULT states: *"The second clause passes everywhere (`0.031…0.094`). The max-clause fails at
`p=211` (`4.04`) and `p=433` (`3.87`)."* **Recomputed from the run's own output
(`row_budget_v2_rows.json`, `row_budget_v3_calib_v3.py` Part A):**

| clause | v2's account | actual |
|---|---|---|
| `max\|z\| > 3` | fails at `211, 433` | **fails at `211, 433, 19231`** — and `p=19231`'s `4.8889` is the **largest** violation |
| `frac\|z\|>2 > 0.10` | *"passes everywhere"*, range `0.031…0.094` | **FAILS at `p=19231`** (`0.1406`); actual range `0.0312…0.1406` |

**This is not bookkeeping.** v2 concluded *"the null is calibrated, the criterion is not"* and the
whole v3 mandate followed from it. That conclusion is **correct pooled and wrong per-prime**:

```
SE of a sd from R=64 draws = 0.0891
p = 19231 : sd = 1.3679  ->  4.13 SE high   (m_p =  820, the smallest frequency list)
p =  9319 : sd = 1.1909  ->  2.14 SE high   (m_p = 1753)
all others:              -1.10 .. +1.14 SE
```

Dropping `p=19231`'s single largest draw leaves `sd = 1.2321`, still `2.6 SE` high — **it is not one
outlier**, and the deviation tracks `m_p` monotonically at the top end. The pooled `sd = 1.019` that
v2 rested on is a **proxy**; the per-prime spread is the **object**. Pooling 640 `z` hid a real defect
in exactly the way `CLAUDE.md` §2b warns (*"mechanical is not enough — it must be OBJECT-level"*).

⇒ **v2's criterion 5 failed for two independent reasons at once**: an incoherent gate (at `211, 433`)
**and** a genuinely over-wide null (at `19231`). v3 fixes both, separately.

---

## 1. THE QUESTION, THE STATISTIC, THE ARITHMETIC

**Object, statistic, threshold, symmetry table, orbit structure:** carried from v2 §1 and §3.1
**verbatim**. `ρ<0.01`; `N_LOW(f) = #{a ≠ 0 : |U(a,f)|² < 0.01(n−1)}`; paired per-frequency error model
`δ(f)`, `Δ̄(p)`, `SE(p) = sd_f(δ)/√m_p`; replicate rank `p`-value at `R=64`, floor `1/65`; pooled
Stouffer `Z` and 10-prime sign test, never a max over primes or frequencies. *"A different generator"*
may never be reported as a control.

**The live question, unchanged and still unanswered** (v2 §1.4(iv)):

> Does the character's own `d`-labelling give a different low-tail count from a `μ₆`-commuting
> relabelling of the same value multiset — and if so, which sub-layer (`λ` / `[−1]` / beyond) carries it?

**`H-BUDGET` remains settled by algebra, not measurement (v2 §1.4(iii), `[PROVED]`).**
`Σ_a|U(a,b,c)|² = n(n−1)` is Parseval for a unit-modulus sequence; **every arm of the ladder carries it
exactly**, so it contributes exactly `0` to `char − MN-μ6`. The frontier's framing — *"the one exact
conservation no random-target null satisfies"* — is accurate only about MC1/MC2, for which the
constraint is **vacuous, not violated**. This is not re-opened by v3.

**Exactness:** v2 §8 carried **verbatim**, including the float carve-out and `check_no_float.sh`.
**Additionally**, the gate-calibration scripts of this spec are declared: they consume only
distributional assumptions and already-printed summary statistics. **No curve, key, index or
coordinate quantity enters them**, and no verdict is decided by them — they decide how a gate is
*written*, before data.

## 2. FORCED STRUCTURE — carried, with one correction

**F1–F14 carried from v2 §2 by reference**, unchanged, including the corrected F7, `F9` parity, `F10`
(`b=0` has a different forced low-tail law, `8.0×` the generic rate), `F11`, `F12`, `F13`, `F14`.
Several are `[PROVED]` and they have held up across two runs; **F12 and F13 correctly predicted v1's
failure in advance.** They are graded independently of any run and no measured layer may borrow a
`[PROVED]` tag from them.

**Correction carried forward:** v2's `Δ_pred` response model is **confirmed** by v2's run (criteria
1–4 passed at every prime; measured vs predicted agree to well within the band). It is retained
unchanged and is **not** re-derived here.

## 3. ARMS — pass criteria and pre-committed conclusions

### 3.1 Arm A primary — `H-ALIGN`
Definition, nulls and pooling carried from v2 §3.1 verbatim. **Grade capped at SEEN-DATA (§0).**
Outcome cells **O-A1…O-A12 carried from v2 §9 verbatim**, with two amendments:

- **O-A9 amended.** v2: *"P-SIZE fires ⇒ Halt; every `z` void, including v1's."* v3: a **pooled**
  P-SIZE' failure (clauses i–iii) halts as before. A **per-prime spread failure (clause iv) does not
  halt** — it triggers the §4 deflation rule. Rationale: a halt-only gate converts a localized,
  measurable, correctable defect into a third abstention, and three abstentions on a frontier that has
  never been tested is a process failure, not rigor.
- **O-A13 (NEW).** *P-SIZE' clause (iv) fires at one or more primes.* → Report **both** raw and
  deflated `z_p`, the deflated governing; name the `m_p`-dependence of the carrier spread as a
  measured property of the instrument; **the arm proceeds.**

### 3.2 Arm A2 / `C-DISP` — carried unchanged
Gate `D_char/D_null > 1.5`; both inflated and uninflated printed, inflated governing. **Calibration
(§5) shows this gate is sound at the real `m_p` and it carries with no change.**

### 3.3 ★ Arm A3′ — the layer test, REDESIGNED (v2's A3 is withdrawn)

**Why A3 is withdrawn.** F11 predicts `layer(p) = −0.4950/(n−1)` (% of REF-RAY). v2 fitted
`log|layer|` on `log(n−1)` against a pre-committed slope `−1`, band `[−1.35,−0.65]`, and measured
`−0.500` ⇒ FAIL. **F11 is not falsified by that**: the target falls up to `12×` below the run's own
noise floor at the top of the range, and all three sign violations sit where `S/N < 0.8`. The floor is
**≈ constant in `p`** (the layer SE does not shrink with `n`) while the signal falls as `1/(n−1)`, so
a log–log slope fit is dominated by primes where the target is invisible. Restricting by `S/N` does not
rescue it — computed (`calib_v1` Part 4):

| `S/N ≥` | primes kept | log-range |
|---|---|---|
| 0.8 / 1.0 / 1.5 | `[163, 433, 991]` | 1.80 |
| 2.0 | `[433]` | — |

**≤ 3 points over < 2 decades at any defensible bar. A slope test is not supportable and v3 does not
attempt one.**

**A3′ — test the constant, not the slope.** F11 is equivalent to
```
C_p := (n−1) · layer(p) = −0.4950   for every p.
```
Statistic: the **inverse-variance-weighted mean** `Ĉ = Σ w_p C_p / Σ w_p`, `w_p = 1/((n−1)σ_p)²`,
tested against `−0.4950`. Inverse-variance weighting **downweights the below-floor primes
automatically**, so no prime is discarded by hand and no post-hoc range is chosen — which is precisely
the defect that made v2's post-hoc `p ≤ 991` restriction inadmissible.

Using v2's own implied `σ_p` (`calib_v1` Part 4): `SE(Ĉ) = 0.1595`, so `|C|/SE = 3.10` — **the constant
is resolvable where the slope was not.** Weight shares: `p=433` 51.1%, `p=991` 24.6%, `p=163` 16.9%,
`p=2089` 5.7%, and `4159/9319/19231` together **1.7%**.

- **Pass:** `|Ĉ − (−0.4950)| ≤ 3·SE(Ĉ)`, `SE` measured in-run, **and** `Ĉ < 0`.
- **Fail:** outside `3·SE`, or `Ĉ ≥ 0`. Then the fourth ladder entry is **not** the finite-`n`
  reference error and must be renamed (v2 O-A11 conclusion carries).
- **Contamination (§0):** the 7-prime layer values are SEEN. A3′ is therefore reported **twice** — over
  all 10 primes `[SEEN-DATA]`, and over the unseen `{211, 349, 577}` alone, which is the **only**
  version that may carry a confirmatory tag. The 3-prime version's power is **not** pre-computable:
  `σ_p` at those primes was never printed, so its SE is measured in-run and its power is reported
  post-hoc **as a scope statement, never as a verdict-strengthener**.

### 3.4 Arm B — carried unchanged, still descriptive
v2 §3.4 and cells **O-B1…O-B5 carried verbatim**. The D7 attestation does not exist, so **O-B4
governs: Arm B is descriptive only, no verdict.** v3 does not attempt to rescue it, does not re-use the
seen five primes as a test, and does not widen it.

### 3.5 Carried without change
`S1` (measured bound with power, not promoted), `S6`, `S7` fragility and cells **O-X1…O-X3**,
and the §3.7 threshold ladder (printed, never verdict-bearing).

## 4. CONTROLS — each with a computed false-failure rate and a demonstrated planted positive

**P-DET-A design (C-a)…(C-d), the 8 swept `ε` levels, and criteria 1–4 carry from v2 §4.1 verbatim.**
`C-SELFZ` (§4.2), `P-DET-C0`/`P-DET-B0` (§4.3) and the forced readout checks (§4.4) carry unchanged.

### ★ Criterion 5 replaced: **P-SIZE′**

Pooled over the `N = R × 10 = 640` unplanted-carrier `z`:

| clause | bound | computed as |
|---|---|---|
| **(i)** `\|mean\|` ≤ `0.1186` | `3/√640` | location |
| **(ii)** `\|sd − 1\|` ≤ `0.0839` | `3/√1280` | pooled spread |
| **(iii)** `max\|z\|` ≤ `3.9440` | `(2Φ(q)−1)^640 = 0.95` | **order-statistic-aware** tail |
| **(iv)** `\|sd_p − 1\|` ≤ `0.2673` **at every prime** | `3/√(2·63)` | **per-prime spread — the clause v2 lacked, and the one §0b shows was needed** |

**Design principle, stated because it is a choice.** The gate tests the two quantities that actually
**scale the verdict** — the null's location and its spread — plus a correctly-quantiled tail. A pooled
Anderson–Darling test of full distributional shape was computed and **rejected**: it fires on a
v2-like null with probability `0.159` (`calib_v1` Part 2) because it is sensitive to the observed skew
`−0.176`, which does **not** scale any verdict. **P-SIZE′ is preferred because it tests less, and
tests the right less.**

**False-failure rate under a perfectly calibrated null: `0.0783`** (12 000 sims, `calib_v3` Part C),
against **`0.8228`** for v2's frozen gate.

**Power — the planted positives** (`calib_v3` Part C; a control with no power is not a control):

| planted defect | power | | planted defect | power |
|---|---|---|---|---|
| `sd = 1.10` | 0.769 | | `sd = 0.85` | 0.997 |
| `sd = 1.15` | 0.986 | | mean shift `+0.15` | 0.807 |
| `sd = 1.20` | 1.000 | | mean shift `+0.25` | 0.999 |

**Against the defect actually present** (one prime wide, nine clean):
`sd=1.20 → 0.32`, `sd=1.30 → 0.63`, **`sd=1.37 → 0.82`**, `sd=1.50 → 0.96`.

**Declared-seen behaviour, stated in advance (§0).** On v2's own numbers P-SIZE′ gives
(i) PASS, (ii) PASS, (iii) **FAIL** (`4.889 > 3.944`), (iv) **FAIL at `p=19231`**. **P-SIZE′ still
fires on v2's data — for a real reason.** That is the point: the gate was recalibrated, not loosened.

### ★ The deflation rule (new — a gate that only halts is not enough)

> **If clause (iv) fires at prime `p`, that prime's verdict `z_p` is deflated by its measured carrier
> spread `sd_p`. Both raw and deflated are printed; the deflated governs.** Same structure `C-DISP`
> already uses. Clauses (i)–(iii) firing still **halts**.

Effect on v2's own numbers, **computed now so v3 cannot be accused of choosing after the fact**
(`calib_v3` Part D): only `p=19231` deflates (`z 33.10 → 24.19`); pooled Stouffer
`Z: +69.67 → +66.86`. **The deflation crosses no pre-registered boundary — it is a magnitude
correction, not a sign change**, and the result remains `[SEEN-DATA]`.

### Criterion 3 — carried, two calibrated adjustments

- **Tolerance band widened `3·SE → 4·SE`.** At `3·SE` the band's false-failure rate is `0.10–0.15`
  over 10 primes (`calib_v1` Part 3); at `4·SE` it is `< 0.01`.
- **Monotonicity clause restricted to the admissible sub-grid.** With the real level separations its
  false-failure rate is `0.0137` over 10 primes (`calib_v2` Part B) — far better than the generic
  estimate, but non-zero, and `p=349` alone contributes `0.0117`. The clause now applies only across
  levels whose `Δ_pred` separation exceeds `3×relsd`, inheriting the sub-grid rule the tolerance band
  already uses instead of applying to every adjacent pair.

## 5. ★ MANDATORY GATE-CALIBRATION TABLE

Required by `RESULT_v2` §5: *two consecutive frozen specs died on pass-criterion calibration, and both
would have been caught by this table.* Every gate, its behaviour under the null, computed before the run.

| gate | null distribution | false-failure rate (10 primes) | verdict |
|---|---|---|---|
| criterion 1 (`ε=1 ⇒ N_LOW=n−1`) | exact integer assertion | **0** by construction | CARRY |
| criterion 2 (chirp `⇒ N_LOW=0`) | exact integer assertion | **0** by construction | CARRY |
| criterion 3 band, `3·SE` | `N(0,1)` per level, 4–6 levels | `0.10 – 0.15` | **widen to `4·SE`** ⇒ `<0.01` |
| criterion 3 monotonicity | real `Δ_pred` separations + `relsd` | `0.0137` | CARRY, sub-grid-restricted |
| criterion 4 (`z(ε=0.20) > +6`) | positive control | n/a — power, not FFR | CARRY (v2 passed) |
| **criterion 5 P-SIZE (v2)** | `max` over 64 iid `N(0,1)` | **`0.8228`** | **WITHDRAWN** |
| **P-SIZE′ (v3)** | 4 clauses, pooled + per-prime | **`0.0783`** | **NEW**; power table §4 |
| `C-SELFZ` `\|z_split\|≤3` | `N(0,1)`, 10 primes | `0.0267` | CARRY |
| `C-SELFZ` LOO-sd `∈[0.7,1.4]` | LOO construction, `R=64` | `0.0000` (20 000 sims) | CARRY |
| `C-DISP` (`D_char/D_null>1.5`) | real `m_p ∈ [820, 26143]` | **`0.00175`** | CARRY unchanged |
| `C-EQ-int`, `C-BUDGET`, `C-PARITY`, `C-PREC` | exact / forced | **0** by construction | CARRY |
| Arm A3 slope band `[−1.35,−0.65]` | ≤3 usable points, <2 decades | underpowered by design | **WITHDRAWN** |
| **Arm A3′** (weighted constant) | `3·SE(Ĉ)`, `SE` measured in-run | `≈0.003` two-sided | **NEW** |
| Arm B `Z₅` bands | — | — | moot: **O-B4** governs |

**Pre-committed threshold:** any gate whose false-failure rate under a correct instrument exceeds
**`0.10`** over the 10 primes is a defect in this spec and must be rewritten before freezing. Two were
found by this table (`criterion 3` band at `3·SE`; `criterion 5`); **both are rewritten above.** No
gate in the frozen v3 exceeds `0.08`.

## 6. POWER AND SCOPE FOR THE PRIMARY

Carried from v2 §5 unchanged: cell budget `m_p = min(N_orb(p), cap)`, `R = 64`,
`T_p = m_p(n−1)q`, relative `SE = √((1−q)/T_p)·√(1+1/R)`, `×√2` on `c=0` (F9);
**pooled `ΣT_p = 1 057 895`, rel `SE = 0.0975%`, MDE @4σ = `0.390%`.**
**Scope banner (v2 §6, carried verbatim and mandatory on every reported number):** 10 model primes
`163…19231`, generic `μ₆×conj` stratum, `N_LOW` at `ρ<0.01`, nulls MN-μ6/MN-neg/MN-free.
**Nothing transfers to `p = 2²⁵⁶−2³²−977`.**

## 7. FALSIFICATION AND ABSTENTION

**`H-ALIGN` falsified if** pooled `|Z(char vs MN-μ6)| < 2` **and** the paired excess lies within the
pooled MDE `0.390%` **and** all P-DET-A criteria (1–4 + P-SIZE′), `C-SELFZ`, `C-DISP` and the forced
checks passed. Carried from v2 §7.

**Void — no verdict — if:** any of criteria 1–4 fails; P-SIZE′ clauses (i)–(iii) fire; the constant
target does not return `N_LOW = n−1` exactly; the chirp does not return `0` exactly; `C-EQ-int`,
`C-NULLSYM`, `C-SELFZ`, `C-PARITY` or `C-STRATREF` fails; or `C-BUDGET` drifts beyond `1e−12`.

**Explicitly NOT void:** P-SIZE′ clause (iv) alone (⇒ deflation rule, O-A13).

**Abstention rules, binding.** Abstaining on an arm is **not** closing a frontier. No outcome licenses
a closure or the words *safe / generic / nothing here / closed / no structure / benign / at the floor*.
A fired outcome cell's pre-committed conclusion is what gets reported; a post-hoc statistic computed on
the frozen window **may not override it** — the failure recorded in
`feedback_prereg_abstention_is_the_finding_2026_07_19`. The
**effect-in-an-unprojected-subspace clause of v2 §9 is carried verbatim and is mandatory**, including
its explicit list of what was not projected onto (which rows are low, the phases of `U`, the
autocorrelation, cross-frequency structure, other thresholds, `p > 19231`).

**Count only unforced hits.** `C-EQ-int` and `C-BUDGET` are forced instrument validation and carry
zero evidential weight. Any count reported must name what it counts and list the misses individually.

## 8. WHAT A PASS AND A FAIL EACH LICENSE

- **Arm A pass (O-A1):** `[EMPIRICAL — SEEN-DATA, CONTROL-REPAIRED]` + §6 scope. Reports the surviving
  layer `char − MN-μ6` with its paired excess, frequency-population SE, MDE, and the four-layer
  decomposition with the fourth entry relabelled per F11. **Does not close §XI.17** and does not
  upgrade either prior abstention into a discovery.
- **Arm A falsified (O-A2):** reported as a **bounded magnitude with its power number and scope** —
  never as an absence of structure. Bounds the ROW axis only; does not touch the `(b,c)` axis.
- **A3′ pass:** F11's `[PROVED to leading order]` grade is corroborated at the measured constant;
  the fourth ladder entry keeps its name. **A3′ fail:** the entry is renamed and F11's prediction is
  recorded as failed — a positive characterization either way.
- **P-SIZE′ clause (iv) fires:** the `m_p`-dependence of the carrier spread is reported as a **measured
  property of the instrument** and named as the next probe.
- **NEITHER licenses:** any statement about ECDLP, extraction, key recovery, or security; any
  `[PROVED]` tag on a measured layer; any statement without the §6 scope banner; any transfer to
  secp's `p`; or the conversion of an abstention into a closure.

## 9. DEVIATION DISCIPLINE

`PREREG_row_budget_lowtail_v3_DEVIATIONS.md`, opened **at the first deviation**, before it is acted on.
Every deviation names the frozen text it departs from and why. **The v2 `_DEVIATIONS` file was never
created** — that is itself recorded here as a process gap, since v2's run did deviate (its RESULT §3
mis-states its own criterion-5 outcome, §0b above).
