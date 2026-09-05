# RESULT — magnitude channel `|V(a)|²` (`PREREG_twist_orbit_magnitude_v1.md`)

*2026-07-26. Frozen run, reused SHA `7cde99fe…`. Grade: `[EMPIRICAL — SCOPED, out-of-sample, controls
fired]`. `experiment-designer` signed off (the "is `|V|²` forced?" risk cleared: 0 of 90/150 non-DC
coefficients forced-zero). No leakage/ECDLP claim. Characterization, not an avenue verdict.*

**One line:** the magnitude arrangement `|V(a)|²` over `Q=(ℤ/n)^×/μ₆` shows **no single-character
concentration** beyond `μ₆`, out-of-sample at 12 primes `p∈[823,2731]` (at the stated power). This is
the second of the two free 2nd-order channels; with the signed null and the forced identities, **the
low-order arrangements examined so far are either null (the two single-character channels) or forced —
this does not exhaust "2nd-order structure", only the specific statistics tested.**

## §1 — Result

`Tmag(p)=max_{j≡0 mod6, j≠0}|Ê(χ_j)|²`, class-energy permutation null, `R=3000`.

| p | n | L | perm p-value | max-χ order |
|---|---|---|---|---|
| 823 | 829 | 138 | 950/3001 = 0.317 | 300 |
| 907 | 967 | 161 | 1065/3001 = 0.355 | 258 |
| 967 | 907 | 151 | 1791/3001 = 0.597 | 234 |
| 991 | 1009 | 168 | 1124/3001 = 0.374 | 210 |
| 1051 | 1093 | 182 | 2293/3001 = 0.764 | 504 |
| 1303 | 1249 | 208 | 2732/3001 = 0.910 | 42 |
| 1831 | 1753 | 292 | 2066/3001 = 0.688 | 240 |
| 2143 | 2089 | 348 | 2806/3001 = 0.935 | 492 |
| 2251 | 2341 | 390 | 1625/3001 = 0.541 | 648 |
| 2503 | 2557 | 426 | 2002/3001 = 0.667 | 708 |
| **2647** | 2677 | 446 | **149/3001 = 0.050** | 1692 |
| 2731 | 2689 | 448 | 2062/3001 = 0.687 | 162 |

**Reading (pre-committed):** p-values consistent with Uniform[0,1] (mean 0.57); min **0.050 at p=2647**
is far above the Bonferroni gate `0.05/12 ≈ 0.004`; the max-character order is prime-specific noise
(300, 258, …, 1692, 162 — no consistency). **No even character rises above the band ⇒ no
single-character concentration detected in the magnitude arrangement beyond `μ₆`** (at this statistic,
sample, and power).

**★ Cross-channel check (strengthens both nulls).** The signed channel's one low prime was **2251**
(0.029); the magnitude channel's is **2647** (0.050) — **different primes**. At 2251 the magnitude
p-value is 0.541; at 2647 the signed p-value was 1.000. So neither low value is a persistent structure
at that prime — they are **independent fluctuations across two spectrally disjoint objects**, exactly
what the null predicts, and precisely what a real structure would NOT do.

**POWER.** PLANT-POS (even char at empirical amplitude) fires **4.9× at L=138 → 10.9× at L=348** (margin
grows with L, per sign-off) ⇒ a comparably concentrated even character would have fired across all of S;
none did. Scoped-real, not a power failure.

**SCOPE.** `p∈[823,2731]`, `p≡7 mod12`; the `|V(a)|²` energy arrangement; single-even-character
concentration. Bounds nothing about 4th-order or additive-cross objects, or secp scale.

## §2 — The 2nd-order picture is complete

| object | verdict |
|---|---|
| signed power spectrum (odd chars on `V`) | **NULL** out-of-sample (`RESULT_twist_orbit_spectrum_v1.md`) |
| magnitude spectrum (even chars on `\|V\|²`) | **NULL** out-of-sample (this file) |
| 2-pt additive autocorrelation | **FORCED** `= n(nδ−1)` (`..._forced_landscape_v1.md`) |
| 3-pt multiplicative bispectrum | **FORCED** `≡ 0` (odd parity) |
| 2-pt multiplicative autocorrelation | WK-dual of the signed null |

**⇒ In the tested channels, no curve-specific arrangement structure was detected through 2nd/3rd
order** — the two free channels are null out-of-sample (at the stated power) and the other low-order
arrangements are forced by the `μ₃`+odd+purity symmetry. This is a scoped *where-it-was-not-detected*
result ([[feedback_negative_bias_enlarge_nulls_2026_07_17]]), **not** a blanket "no structure": it is
bounded by the specific statistics (single-character concentration), the sample (`p≤2731`), and the
power (PLANT fires at 4.9–10.9×).

## §3 — Named frontier: 4th order (monodromy type)

The odd parity that forced the 3-pt bispectrum to zero does **not** force the 4-pt object (odd⁴ = even).
Its 1-point shadow is `E[u⁴]`, the record's **SU(2)-vs-reduced monodromy discriminator**
(`E[u⁴]=1/8 ⟺` full SU(2), Catalan `C₂=2`). That is a **symmetry-TYPE** question — the monodromy group
of the `χ₂(y)` Kummer sheaf — and is the natural next prereg. It is the first object where the forcing
that flattened everything below does not apply.

## §4 — Provenance

- Instrument `twist_orbit_magnitude_run_v1.py` (C-NOFLOAT OK; exact `V∈ℤ[ζ_n]`; float only in the
  FFT statistic, ranked against the permutation null). Freeze reused: `twist_orbit_spectrum_FREEZE_v2.json`,
  SHA `7cde99fec08891ac0e558d11458024ddac5261c6722e2be28953c727fa37bd6e`.
- Controls all fired: PLANT-POS (4.9–10.9×), PLANT-NEG (in-band), C-PARSEVAL (`DC=n(n−1)`), C-CROSS,
  C-NOFLOAT. Sign-off: `experiment-designer` (fresh `p=547,967`).
- Prereg `PREREG_twist_orbit_magnitude_v1.md`; deviations `PREREG_twist_orbit_magnitude_v1_DEVIATIONS.md`.
