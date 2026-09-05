# RESULT — ITEM 2: two of the four RMT statistics were already measured; the other two are now run and NULL

**Date:** 2026-08-01. **Script:** `rmt_delta3_twopoint_v1.py`. **Grade:** `[EMPIRICAL — SCOPED NULL]`.

## 1. The table was stale

`SYNTHESIS_brainstorm_seven_cycles_ADDENDUM_1_v1.md` §4 (**dated Jul 26**) lists four random-matrix
statistics as never measured on `{θ_a}`. `RESULT_semicircle_null_and_verification_v1.md`
(**dated Jul 30**) ran two of them — **level spacing (KS)** and **number variance `Σ²`** — against
the cap-respecting semicircle null at 17 primes + 15 OOS, both NULL.

**The addendum's own answer post-dates it by four days.** This is the recurring pattern the record
already logs twice (`MASTER_v4` predating its own answer; item 2's 2026-07-24 verdict vs the
2026-07-25 identity). **Check dates before running anything marked OPEN.**

Genuinely unrun, and run here: **spectral rigidity `Δ₃`** and the **two-point correlation**.

## 2. Result — NULL

14 primes (`p ≡ 3 mod 4`, `p ≡ 1 mod 3`, cyclic prime-order `j=0` curves, `p = 823…3343`),
`R = 400` semicircle draws, statistics on the `L = (n−1)/6` free class representatives:

| statistic | cells with two-sided `p ≤ 0.05` | min p |
|---|---|---|
| `Δ₃` spectral rigidity | **0/14** | 0.180 |
| `K(0.05)` form factor | **0/14** | 0.070 |
| `K(0.10)` form factor | 2/14 | 0.045 |
| `K(0.20)` form factor | 2/14 | 0.005 |
| short-range pair correlation | **0/14** | 0.115 |

**70 cells, 4 hits at `p ≤ 0.05`, 3.5 expected.** Consistent with the null; the two `K` columns are
Fourier-adjacent and not independent. No structure.

## 3. Control — and its limit, stated

**C-PLANT.** A **rigid picket-fence** spectrum is detected by all five statistics (`Δ₃` at
`p = 0.005`). A **clustered two-clump** spectrum is detected by the pair correlation (`p = 0.005`)
and `K(0.10)` (`p = 0.040`) but **not by `Δ₃`** (`p = 0.070`).

So `Δ₃` has real power against **rigidity** — the alternative it exists to test, and the one
GUE/Katz–Sarnak structure would produce — and **limited power against clustering**. Scope stated
rather than assumed.

## 4. An instrument defect — mine, not the record's

`u_free` computes `(V/(2i√p)).real`. At `p ≡ 1 mod 4`, `ε = χ₂(−1) = +1`, so `c(−d) = +c(d)`: the
signal is **even**, `V` is purely **real**, and `.real` of `V/(2i√p)` is **identically zero**.

My first run included `p = 2089` (`≡ 1 mod 4`) and it returned **all five statistics at the floor
(`p = 0.005`)** — 356 tied values, `max|u| = 0`, `E[u²] = 0` against the forced `1/4`. Five
independent statistics maxing out together is a broken cell, not a signal, and diagnosis confirmed it.

**This is not a defect in the record.** `twist_orbit_spectrum_run_v1.py`'s header documents the
requirement (*"`V(−a) = −V(a)` (`χ₂(−1) = −1` at `p ≡ 3 mod 4`)"*), and the semicircle run's
`E[u²] ∈ [0.2394, 0.2600]` control would reject a degenerate cell. **I omitted the guard the record
already had.**

> **STANDING GATE for anything built on `u`:** require `p ≡ 3 mod 4`, `E[u²] ∈ [0.20, 0.30]`, no tied
> values, and `max|u| ≤ 1`. secp256k1 has `p ≡ 3 mod 4`, so the framework is valid there.

## 5. What remains of item 2

The `|T(a,b)|²` **intensity** object is a **different object** from `{θ_a}`. Porter–Thomas was
measured on it (`[EMPIRICAL, p ≤ 2089]`, `masked_structure_findings_v18.md`); spacing, `Δ₃`, `Σ²`
and the two-point correlation on **that** object were never run and are not covered here.

## 6. Scope

`p ≤ 3343`, 14 primes, `j = 0`, prime-order cyclic, `p ≡ 3 mod 4`; iid-semicircle null (= the
Katz–Sarnak/Sato–Tate prediction); `R = 400`; free class representatives only. Power: detects a
picket-fence rigid spectrum at `p = 0.005`; weaker against clustering.
