# RESULT — twist-orbit multiplicative-spectrum test (`PREREG_twist_orbit_spectrum_v2.md`)

*2026-07-26. Frozen run, SHA `7cde99fe…`. Grades: the primary is `[EMPIRICAL — SCOPED,
out-of-sample, controls fired]`; the Arm II dissolution is `[PROVED — forced identity, exact]`;
C-JZERO is `[VERIFIED — exact + empirical]`. No leakage / key-recovery / ECDLP claim. Output is a
characterization + a bounded magnitude, per [[feedback_anomaly_drill_protocol_2026_07_17]] — **not** a
verdict on the avenue.*

**One line:** the twist-orbit arrangement `a↦V(a)` carries **no single-character multiplicative
concentration beyond its forced `μ₃`+odd symmetry**, at 12 out-of-sample primes `p∈[823,2731]` — a
scoped magnitude bound. Two structural facts fell out that are worth more than the null: **Arm II's
frame object is a forced `nI−J`** (the curve signal lives in the *values*, not the frame), and the
`μ₃`-invariance is **CM-specific** (j=0: 100% of spectral energy; j≠0: ~⅓).

---

## §1 — Primary: no single-character concentration beyond `μ₃`+odd, out-of-sample

`T(p)=max_{χ admissible}|V̂(χ)|²`, admissible = the `L=(n−1)/6` odd, `μ₃`-trivial characters; p-value
from the signed-value permutation null (`R=3000`).

| p | n | L | perm p-value | max-χ order |
|---|---|---|---|---|
| 823 | 829 | 138 | 984/3001 = 0.328 | 276 |
| 907 | 967 | 161 | 1192/3001 = 0.397 | 46 |
| 967 | 907 | 151 | 649/3001 = 0.216 | 302 |
| 991 | 1009 | 168 | 2275/3001 = 0.758 | 336 |
| 1051 | 1093 | 182 | 2089/3001 = 0.696 | 364 |
| 1303 | 1249 | 208 | 1781/3001 = 0.593 | 416 |
| 1831 | 1753 | 292 | 2983/3001 = 0.994 | 584 |
| 2143 | 2089 | 348 | 2488/3001 = 0.829 | 696 |
| **2251** | 2341 | 390 | **86/3001 = 0.029** | 260 |
| 2503 | 2557 | 426 | 2133/3001 = 0.711 | 852 |
| 2647 | 2677 | 446 | 3001/3001 = 1.000 | 892 |
| 2731 | 2689 | 448 | 387/3001 = 0.129 | 896 |

**Reading (pre-committed, §5 of the prereg).** The 12 p-values are consistent with Uniform[0,1]
(sorted: 0.029, 0.13, 0.22, 0.33, 0.40, 0.59, 0.70, 0.71, 0.76, 0.83, 0.99, 1.00; mean 0.57 — if
anything *above* ½). The single low value, **p=2251 at 0.029**, is transparently reported and is
**within multiple-testing expectation**: `P(min of 12 uniforms ≤ 0.029) ≈ 0.29`, and it is far above
the Bonferroni gate `0.05/12 ≈ 0.004`. The "most concentrated" character's order varies with no
cross-prime consistency (276, 46, 302, …, 260, …, 896) — the signature of noise, not a law. **No
admissible character rises above the band ⇒ no single-character concentration detected beyond the
forced symmetries** (at this statistic, sample, and power).

**POWER.** PLANT-POS (a single admissible character at empirical magnitude) fires at **4.1× / 4.5× /
6.3×** the null band (in-sample calibration primes 127/163/211); the pre-run power analysis
(experiment-designer sign-off) puts the detectable single-character energy fraction at **≈6%**. So a
character carrying ≳6% of the arrangement energy would have fired at >95% — none did. The null is
**scoped-real, not a power failure**. PLANT-NEG (empirical values, random arrangement) sits in-band, as
required.

**SCOPE.** `p∈[823,2731]` (12 primes), `p≡7 mod 12`; the `χ₂(y)` channel; `μ₆`-classes; the
**single-character (multiplicative) concentration** statistic. **Bounds nothing about:** 2-point / joint
arrangement statistics, additive or short-scalar arrangements, or secp scale (`p≈10³` vs `2²⁵⁶`).

---

## §2 — Arm II dissolved into a forced identity (the positive finding)

Hyp II ("frame-coercivity") asked for the Gram of `f_a(P)=χ₂(y_P)ζ_n^{a d(P)}`. Exactly, and
**curve-independently** (`gram_direct.py`, `p=67`, 400 pairs; agent reconfirmed `p=43`):
`⟨f_a,f_b⟩ = Σ_{k=1}^{n−1} ζ_n^{(a−b)k} = nI − J`. The `χ₂` sign — the whole curve signal — is
annihilated by `|f_a(P)|=1`. **So Hyp II's literal statistic carries zero curve information; the curve
signal lives in the *values* `V(a)`, which is what the primary reads.** Same for the disclosed
Parseval constant `Σ_{a∈(ℤ/n)^×}|V(a)|²=n(n−1)` (verified 6 primes) — a forced normalization, not
evidence. This is the useful residue of Arm II: it **located** the object.

---

## §3 — C-JZERO: the controlled-for `μ₃` structure is CM-specific

Fraction of `V`'s multiplicative-spectral energy on `μ₃`-trivial characters (`cjzero_check.py`):

| curve | p | `μ₃`-trivial energy |
|---|---|---|
| **j=0** `x³+7` (ours) | 823 / 907 / 967 | **1.0000 / 1.0000 / 1.0000** (forced) |
| j≠0 `x³+x+7` etc. | 823 / 907 / 967 / 991 / 1051 | 0.330 / 0.355 / 0.339 / 0.260 / 0.312 (≈ ⅓, generic) |

The `μ₃`-invariance is a genuine **CM property of `y²=x³+7`** (absent on `j≠0`), so the primary's null
is a real statement about structure *beyond* the CM-forced symmetry — not an artifact of the class
machinery. (The full `j≠0` re-test of a *fired* character is triggered only by a positive; the primary
was null, so it was not required.)

---

## §4 — What is now bounded, and the next probes (pre-committed)

**Bounded** `[EMPIRICAL — SCOPED]`: single-character multiplicative concentration of the signed
twist-orbit sequence, `p∈[823,2731]`, `χ₂(y)` channel.

**Named next probes** (prereg §5/§6, none run here — each needs its own prereg):
1. the **2-point arrangement** statistic `(ρ_a, ρ_{ab})` — a concentration null does not exclude
   pairwise/autocorrelation structure (the arrangement's higher-order shape);
2. the **additive / short-scalar** arrangement (every statistic here is a complete-orbit object);
3. the **multiplicativity** residue `V(a)V(b)/V(ab)` in `ℤ[ζ_n]` (prereg §6 secondary, deferred rather
   than half-run);
4. optional: retest **p=2251**'s max character at a fresh out-of-sample prime — cheap, and the honest
   way to confirm the 0.029 is the expected fluctuation it appears to be (not required for the verdict).

⚠ Per [[feedback_negative_bias_enlarge_nulls_2026_07_17]] this is a **magnitude bound, not a closure**:
the arrangement's structure, if any, lives in the higher-order statistics (1–2) that this
single-character test does not see.

---

## §5 — Provenance

- **Prereg:** `PREREG_twist_orbit_spectrum_v2.md` (v1 → v2 correction: `V` is `μ₃`-invariant + odd, not
  `μ₆`-invariant — caught by `experiment-designer`; both v2 fixes re-signed-off). Deviations:
  `PREREG_twist_orbit_spectrum_v2_DEVIATIONS.md`.
- **Freeze:** `twist_orbit_spectrum_FREEZE_v2.json`, SHA-256
  `7cde99fec08891ac0e558d11458024ddac5261c6722e2be28953c727fa37bd6e` (written before the gate run).
- **Controls all fired:** C-ODD `V(−a)=−V(a)` (exact, every cell), C-PARSEVAL `Σc²=n−1` (exact),
  rebuild_err ≤ `1e-13` (forced-symmetry indexing), C-NOFLOAT (`check_no_float.sh` OK — exact signal
  path; float only in the FFT statistic, ranked against the permutation null), C-CROSS (independent
  enumeration), PLANT-POS (fires 4–6×), PLANT-NEG (in-band), C-JZERO (§3).
- **Code:** `twist_orbit_spectrum_run_v1.py` (signal-path exact), `cjzero_check.py`,
  `gram_direct.py`, `verify_symmetry.py`.
