# PREREG — Locus of the sub-Rayleigh deficit in `|U(a₀,b,c)|`

**File:** `PREREG_harmonic_deficit_locus_v1.md`  **Date:** 2026-07-21  **Status:** PRE-RUN. No confirmatory per-partition deficit statistic computed. The exploratory `harmonic_deficit_locus_v1.py` (χ₃ proxy, 3 primes) is *scoping only* and may not be cited as evidence here.

**Scope, up front.** Enumerable model curves `E : y²=x³+7` over `F_p`, `p ≡ 1 mod 6`, prime order `n`. `p = 2²⁵⁶−2³²−977` is not enumerable; **nothing transfers to it** — every object needs a full sum over all `d`.

---

## 0. WHAT IS INPUT vs WHAT IS TESTED

- **Input (established, not re-scored here):** `RESULT_harmonic_support_pattern_v1.md` §2 — a `mean|U|` sub-Rayleigh deficit exists, one-directional at 7/7 primes, `−13.9σ` at `p=2089`, under the pinned `l²` budget `Σ|U|²=p²(n−1)`. This run does **not** re-litigate that the deficit exists.
- **Tested (the one open question, §5 of that RESULT):** does the deficit `D(b,c)` concentrate on a **publicly-computable locus** in frequency space, or is it uniform (a pure `l¹`-norm suppression with no locus)?
- **Why it matters and why it is NOT circular:** a locus that is a function of `(b,c)` alone would be a cheap, `d`-free descriptor of where the character departs from Gaussian — the first structural (not aggregate) handle on the deficit. The partition never reads the deficit it is scoring (guard §4).

---

## 1. OBJECT

`a₀=1`. `U(a,b,c)=Σ_{d=1..n-1} e_n(a d) e_p(b x_d + c y_d)` (FFT over the point set).
Random target: `g_r(d)` iid unit phase; `U_r` built identically. Over `R` targets,
```
D(b,c) = |U(1,b,c)| − (1/R) Σ_{r} |U_r(b,c)|       (per-harmonic deficit; exact nonneg magnitudes)
```
`Σ_{(b,c)≠0} D < 0` is the reproduced aggregate deficit (§5 control C0).

---

## 2. FORCED FACTS — contribute ZERO evidence

- **F1 — C2 equivariance `[VERIFIED 4e-13]`.** With the `(λ,β)` pair from the coordinates (`x_{λd}=βx_d` err 0, `y_{λd}=y_d`), `|U(1,βb,c)| = |U(λ⁻¹,b,c)|`. Hence `D` at `a₀∈{1,λ⁻¹,λ⁻²}` are exact β-shifts of one another — the **cross-a₀ equivariance of the deficit is forced**, so it is a readout, never evidence. The open question lives **within one a₀-slice**.
- **F2 — `l²` pinned `[VERIFIED machine-0]`.** `Σ|U|²=p²(n−1)`, char = random. No unitary basis change concentrates the total; the deficit is purely in `mean|U|` (`l¹`).
- **F3 — aggregate deficit reproduces `[VERIFIED, quick check]`.** Direct `mean|U|` deficit reconciles with the RESULT's `N_eff` via `N_eff ∝ (mean|U|)²` (p=163: 0.36% ↔ `N_eff` 0.72%). Existence is input (§0), not scored.

---

## 3. STATISTIC (frozen)

**Pre-committed partitions of frequency space**, each a function of `(b,c,p)` only:
`P1 χ₃(b)` (cubic class), `P2 χ₃(c)`, `P3 legendre(b)`, `P4 legendre(c)`, `P5 |b|-band` (fixed deciles), `P6 the axes {b=0}, {c=0}`, and `P7 within-β-orbit variance` (is `D(b)=D(βb)=D(β²b)` at fixed a₀ — a *non-forced* test, since F1's equivariance is across a₀-slices, not within one).

**Per-partition statistic:** for each class `s`, the mean deficit `⟨D⟩_s`.
**Null (locus-permutation):** shuffle `D` across the `(b,c)≠0` harmonics `K≥1000×`, preserving the `D` multiset, destroying locus. Integer-rank two-sided p-value `perm-p(s) = (#{|shuffled ⟨D⟩_s| ≥ |⟨D⟩_s|}+1)/(K+1)`.

**Replication gate (the lesson of the quick check).** A class is a **locus** only if it is extreme (`perm-p < 0.01`) on the **discovery** prime set AND replicates (same sign, `perm-p < 0.05`) on the **disjoint replication** set. A single-prime extreme that fails replication is reported as a chance pattern, never a locus. (Calibration target: the known `χ₃=2`@`p=163` spike, `perm-p=0.0025`, which dies at `p=349,577`, MUST be filtered out by this gate — it is the built-in negative control C3.)

---

## 4. TAUTOLOGY GUARD (code-level)

Each partition function has signature `part(b, c, p)` only; `inspect.signature` asserts args ⊆ `{b,c,p}` — never `a₀`, `d`, `xs`, `ys`, `U`, or `D`. A violation aborts. `D` is computed in a separate path and passed to the scorer, never to a partition.

---

## 5. CONTROLS (all must fire; no result if any fails)

- **C0 — aggregate deficit sign.** `Σ D < 0` on every prime (reproduces F3).
- **C1 — C2 equivariance** (F1) to `<1e-6` on every prime.
- **C2 — PLANT (must fire AND replicate).** Inject `−δ` into one partition class on the discovery set only; the scorer + replication gate must flag it as a locus. If it does not, no result.
- **C3 — negative control (must be filtered).** The `χ₃`@`p=163` chance spike must be classed as chance (fails the replication gate). If the gate reports it as a locus, the gate is miscalibrated → no result.
- **C4 — floor.** Deficit of one random target vs the ensemble mean is `≈0` and uniform across all partitions.

---

## 6. POWER & SCOPE

- **Primes (frozen):** discovery `{163, 211, 349}`; replication `{433, 577, 991, 2089}`; extension (report, not gated) `{4099, 8209}` where `σ` grows. `m` need not be selected — `a₀=1` and the deficit are defined for every prime-order curve.
- **Power:** `K≥1000` → perm-p resolution `≤0.001`. Smallest detectable per-class mean deficit ≈ the locus-permutation spread at each `|class|` (printed per run, not assumed). The replication gate costs power by design — it is the price of not naming a chance pattern.
- **Scope:** model primes only; `a₀=1` slice; the 7 pre-committed partitions; no `p ~ 2²⁵⁶`. A partition coming back uniform is a scoped null (method+sample+floor+partition-list), not "no locus exists".

---

## 7. FLOAT / EXACTNESS CARVE-OUT

Curve/group arithmetic and the `(b,c)` grid are exact int. Float only in the complex exponentials / FFT (`|U|`, analytic-size). All decisions are integer-rank permutation p-values; no float threshold decides a verdict (the `1e-6` C1 check is a forced validation).

---

## 8. PRE-COMMITTED OUTCOME TABLE (no dismissal language)

| Case (from printed output) | Reported as |
|---|---|
| A partition class extreme on discovery AND replicates | "The deficit concentrates on the publicly-computable locus [partition/class] across primes: magnitude `X`, power `Y`, scope model-only, `a₀=1`. Next probe: whether the locus is `d`-predictive (its own prereg). Not a transfer to `2²⁵⁶`." |
| Extreme on discovery, fails replication gate | "A single-prime pattern at [class/prime], perm-p `X`, that does not replicate — a chance pattern (as the built-in `χ₃`@163 control confirms), not a locus." |
| No partition extreme + replicating | "The deficit is uniform across the 7 tested publicly-computable partitions of the `a₀=1` frequency slice — a bounded, structureless `l¹`-norm suppression of `mean|U|`, not a locus. This is a clean characterization: the live item is a global magnitude, and it does not live in any tested cheap locus. Untested: finer/non-listed partitions, other a₀, higher `p`, non-linear readouts." |
| C2/C3 miscalibrated or C0 fails | **No result reported.** Debug; re-run. |

---

## 9. OUTPUT TYPE (pre-committed)

A **bounded characterization** of where (if anywhere) the sub-Rayleigh deficit lives, anchored on the forced facts (F1–F3). Never a verdict about ECDLP, extraction, security, or a gate. Nulls are conditional (method+sample+floor+partition-list). A uniform result is a magnitude located in the `l¹` norm, not an absence of structure.

---

## Files this run will produce
- `harmonic_deficit_locus_v2.py` (frozen; extends the exploratory v1 with the 7 partitions, discovery/replication split, `K≥1000`; reuses `t_y_maxbound_v1`, the C2 `(λ,β)`-from-data derivation, the plant + negative controls).
- `harmonic_deficit_locus_v2.log` — every §8 row decidable from it.
- `RESULT_harmonic_deficit_locus_v1.md` — characterization + bounds.
- `PREREG_harmonic_deficit_locus_v1_DEVIATIONS.md`.
