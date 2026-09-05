# ANALYSIS — structure of the P0′ low-mode excess

**Scope.** Follow-on characterization of the `[EMPIRICAL]` positive from
`RESULT_coherent_pool_P0prime_v1.md`: the CM curve `y²=x³+7` concentrates ~7% more
low-ρ character-sum modes (`N_LOW`, ρ<0.01) than the MN-μ6 null. This doc probes
*where that excess lives*. No leakage/ECDLP claim; exact `N_LOW` counts, float
FFT/χ² reported as exploratory statistics. Drivers: `p0prime_s5_localization_v1.py`,
`p0prime_ap_law_v1.py`, `p0prime_freq_sextic_v1.py`.

Grades: `[MEASURED]` exact/reproduced; `[REFUTED]` hypothesis tested and rejected;
`[RETRACTED]` claim failed its firing control; `[OPEN]` live thread.

> **CORRECTION (firing control run after the fact).** Cuts 3 and 4 below claimed a
> sextic localization of the excess (χ² class-uniformity z=8–28). That χ² has
> expected cells `E_k ∝ total excess`, so its null is undefined and it fires on the
> per-class count variation already present in the null. A proper permutation test
> (`p0prime_sextic_control_v1.py`: real per-class rate-variance vs the same on
> exchangeable null replicates) gives **p = 0.55 (p=163), 0.27 (p=9319)** — the
> real char is NOT an outlier. **The sextic localization does NOT survive its firing
> control and is RETRACTED**, along with the rotation-law thread built on it. What
> survives is Cut 1 (no index localization), Cut 2 (a_p refuted), and the parent
> result's **aggregate ~7% excess**, which passed its own NULL-vs-NULL control.
> Lesson: the χ² z-scores were believed before the control row was checked.

---

## Three cuts, one picture

### Cut 1 — index (a) space: DISTRIBUTED `[MEASURED]`
S5 (μ6-orbit occupancy of the low set `{a : ρ(a)<0.01}`), char vs scaled null
shape: `z_shape = +1.6, +0.1, +1.2, −0.7` (p=163,211,349,433). No significant
reshaping (at p=433, χ²=57 < df=65). The excess is **spread across μ6-orbits of
the index a** — not localized there. Top-orbit z (3–4, growing with the frequency
budget) is a power artifact; top-10% share *shrinks* toward uniform as p grows.

### Cut 2 — the a_p law: REFUTED `[REFUTED]`
Motivated by the a_p=37 twin (p=349,433 → matching excess), tested `excess = f(a_p)`
over all 21 primes (10 discovery + 11 held-out). Spearman: **excess vs a_p =
−0.20, vs |a_p| = −0.10, vs a_p/2√p = −0.18** — all weak. The strong `−0.90` at
p<600 does **not** generalize (small-sample/confound). A single Frobenius number
does **not** govern the magnitude. (Internal check: p=991, in both sets via
different freq-lists, gives excess 7.49% vs 7.08% — mostly a curve invariant, with
a ~0.4pp freq-list dependence that pointed to Cut 3.)

### Cut 3 — frequency (b,c) space: sextic localization `[RETRACTED — failed firing control, see top]`
Per-frequency excess `charN_LOW(b,c) − meanNull(b,c)`, binned by the sextic
character class `χ₆(b)=b^((p−1)/6)`, `χ₆(c)` (the natural CM feature for j=0):

| p | top-10% freq share of +excess | χ₆(b) class-uniformity z | χ₆(c) z |
|---|---|---|---|
| 163 | 46.2% (unif 10%) | **+17.0** | **+25.8** |
| 211 | 46.7% | +8.7 | +8.0 |
| 349 | 45.2% | +15.5 | +22.5 |

The excess **concentrates on sextic classes of the frequency**. p=163, χ₆(c):
class 2 → −0.16% (null), classes 4,5 → +11.7%, +12.7%. Clean char-vs-null (the
null is subtracted per-frequency, same value multiset), so the class dependence is
in the **arrangement**, not the values.

### Cut 4 — rotation law `[RETRACTED — premised on the Cut-3 artifact]`
The "persistence" here was the same uncontrolled χ² measured at more primes; it
inherits the Cut-3 defect. A_p ≡ 1 mod 6 for all primes (a genuine congruence) and
the a_p-law refutation stand; the rest of this cut is void.
Tested whether the per-prime excess-by-class 6-vector is one common shape cyclically
shifted by a Frobenius invariant (`p0prime_rotation_law_v1.py`, 6-point DFT of the
excess vector, orientation = arg of the fundamental).
- **No clean rotation law.** The orientation `arg(Vhat[1])` is not a function of
  `a_p mod 6` (degenerate — `a_p ≡ 1 mod 6` for ALL 10 primes, a real CM congruence)
  nor of `χ₆(7)`; the dominant harmonic itself varies per prime (1↔3). So the
  *orientation* is not fixed by a simple scalar Frobenius invariant.
- **But the localization PERSISTS and stays highly significant at large p** (this
  corrects a premature "finite-size washout" read off the shrinking spread):

  | p | 2089 | 9319 | 19231 |
  |---|---|---|---|
  | χ₆(b) class-uniformity z | +15.9 | +25.8 | **+28.5** |
  | per-class spread (max−min) | 0.8pp | 1.4pp | 1.6pp |

  The **amplitude** (rate spread) decays with p (13.6pp at p=163 → ~1.5pp at
  p≈2×10⁴) but the **structure does not** — z stays 16–28. The excess is
  definitively sextic-localized across two orders of magnitude in p.
- **χ₆(b) is the robust axis** (z 16–28 everywhere); χ₆(c) is noisier (z 4–25).
  This fits the CM: the order-6 automorphism acts on x (coefficient b) via ω, on
  y (coefficient c) only via ±1.

---

## Reading (after the firing control)

What survives all three cuts plus a control:
- **Cut 1:** no localization in the index a.
- **Cut 2:** the magnitude is not a function of `a_p` (and `a_p ≡ 1 mod 6` is forced,
  so a_p carries little mod-6 information for this family).
- **Cut 3/4 control:** no localization in frequency (b,c) space either — the sextic
  χ² did not survive a permutation firing control (`p = 0.55, 0.27`).

So across the axes tested, the ~7% excess is a **diffuse aggregate effect with no
localization detected** — uniform in the index, and not sextic-structured in the
frequency once controlled. The only claim with a passing control is the parent
result: the curve carries ~7% more low-ρ modes than the μ6 null in aggregate
(NULL-vs-NULL clean, held-out). Everything about *internal structure* of that
excess is, so far, either refuted (a_p) or a control artifact (sextic).

This is a scoped negative on the structure-hunt, not on the aggregate excess. It
does not license calling the aggregate "generic" — that would itself need a control
(a matched non-CM curve family) that has not been run.

---

## Open threads (ranked, post-control)

1. **`[OPEN]` Is the aggregate ~7% CM-specific?** The controlled finding is the
   aggregate excess. The test that would place it: run the same aggregate excess +
   NULL-vs-NULL on a **matched non-CM curve** (generic j) at the same p's. If non-CM
   shows ~0 excess and CM shows ~7%, the excess is a CM signature; if non-CM also
   shows it, it is a generic character-sum-vs-relabel artifact. This is the control
   that decides what the ~7% *is*, and it has not been run.
2. **`[OPEN]` Re-examine every earlier "structure" claim's control.** Cut 3 fired an
   uncontrolled χ². Audit whether any surviving statistic (including the pool's own
   framing) rests on a control that was actually checked to fire on null.
3. **`[CLOSED-for-now]` Sextic / rotation / a_p localization** — no signal survives
   control; do not re-open without a new statistic that passes its firing control
   first.

---

## Provenance
- Parent: `RESULT_coherent_pool_P0prime_v1.md`, `PREREG_coherent_pool_P0prime_v1.md`.
- Drivers: `p0prime_s5_localization_v1.py` (Cut 1), `p0prime_ap_law_v1.py` (Cut 2),
  `p0prime_freq_sextic_v1.py` (Cut 3). All pass `check_no_float.py` except reported
  exploratory float statistics (marked `# noqa: float`).
- Sextic-reciprocity context: `secp256k1_arithmetic_v4.md` (memory
  `secp256k1_pure_arithmetic_study_2026_07_11`).
