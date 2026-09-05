# RESULT — the twist orbit's low-order arrangement is forced or null (a characterization)

*2026-07-26. Grades: the forced identities are `[PROVED — exact, verified]`; the magnitude-channel
preview is `[EMPIRICAL — in-sample, design-only]` (out-of-sample verdict pending
`PREREG_twist_orbit_magnitude_v1.md`). Exact signal path; float only in FFT diagnostics. No
leakage/ECDLP claim. Output = characterization, per [[feedback_anomaly_drill_protocol_2026_07_17]].*

**One line:** chasing the signed null "down" shows that every natural 2-point/3-point *multiplicative*
arrangement examined is either **FORCED** (the unit-modulus / Parseval identities, and the odd-parity
bispectrum zero — structure provably absent there) or **already null** (the signed power spectrum,
scoped/empirical) — so no *additional* low-order multiplicative-arrangement structure was found beyond
the forced symmetry. The natural next object the parity argument does **not** settle is **4th order**.

---

## §1 — The forced landscape (exact)

`V(a)=Σ_k c_k ζ_n^{ak}`, `c_k=χ₂(y_{[k]G})∈{±1}` (`k≠0`), `c_0=0`. Three of the four natural low-order
arrangement statistics are **forced, carrying zero curve information:**

| object | value | forced by | verification |
|---|---|---|---|
| **2-pt additive autocorrelation** `Σ_{a∈ℤ/n} V(a)\overline{V(a+b)}` | `n(n·δ_b − 1)` (so `n(n−1)` at `b=0`, `−n` else) | `\|c_k\|²=1` (`k≠0`): the sum `= n·Σ_k\|c_k\|²ζ_n^{−bk}` | **exact**, `p∈{127,163,211,349,547}` (A0=`n(n−1)`, A₁=A₂=`−n` to the integer) |
| **3-pt multiplicative bispectrum** `V̂(χ₁)V̂(χ₂)\overline{V̂(χ₁χ₂)}` | `≡ 0` | **odd parity** `V(−a)=−V(a)` ⇒ `V̂` supported on ODD χ; `χ₁,χ₂` odd ⇒ `χ₁χ₂` even ⇒ `V̂(χ₁χ₂)=0` | even-char mass of `V̂` `= 1e-16` (machine zero), 5 primes |
| **2-pt multiplicative autocorrelation** `Σ_a V(a)\overline{V(ab)}` | Wiener–Khinchin dual of the signed power spectrum | Fourier duality | the power spectrum was measured NULL (`RESULT_twist_orbit_spectrum_v1.md`), so its dual is too — **not an independent object** |
| **signed multiplicative power spectrum** `max_χ\|V̂(χ)\|²` | FREE | — | measured, **NULL** out-of-sample (12 primes) |

The three forced identities all trace to the same source as the `nI−J` frame Gram: **`\|·\|=1`
pointwise + odd parity.** They are the arrangement-level analogues of the forced `e₃,e₄` of the 120°
prereg — instrument facts, never evidence.

---

## §2 — The one free 2nd-order object: the magnitude arrangement

`E(a)=|V(a)|²` is `μ₆`-invariant, so it is a genuine function on the `L=(n−1)/6` classes; its spectrum
lives on the **even, `μ₃`-trivial** characters (`j≡0 mod6`), DC excluded (DC `=n(n−1)`, forced,
Parseval). This is **free** (`Tmag` varies with the curve, permutation null non-degenerate — verified).

**Preview** `[EMPIRICAL — in-sample, design-only]` (`forced_landscape_v1.py`): null-ish at 5 in-sample
primes (perm-ranks 40–506/600; `Tmag < p95` everywhere). The **out-of-sample verdict** is deferred to
`PREREG_twist_orbit_magnitude_v1.md` (arms held pending sign-off), which reuses the frozen S.

---

## §3 — ⚠ Erratum on the SIGNED run's in-sample reference set

`PREREG_twist_orbit_spectrum_v2.md §3` listed in-sample reference `I={13,43,127,163,211,349,397,433,547}`.
**Four of these (`13,349,397,433`) are `p≡1 mod 12`** (COS stratum), where `χ₂(−1)=+1` makes `V`
**EVEN**, not odd — so the odd-channel statistic is mis-specified there and those reference rows are not
interpretable. The valid SIN in-sample primes are `{43,127,163,211,547}`. **The out-of-sample stratum
S is entirely `p≡7 mod 12` (SIN) and is UNAFFECTED**; the primary verdict stands. The magnitude channel
(§2) is immune (magnitude ignores the sign) and is well-defined on both strata. Logged in
`PREREG_twist_orbit_spectrum_v2_DEVIATIONS.md`.

---

## §4 — Synthesis and the named frontier

**Characterization:** through 2nd/3rd order the twist orbit's arrangement splits into two kinds of
statement, which must not be conflated. **FORCED** `[PROVED — exact]`: the additive autocorrelation and
the multiplicative bispectrum are fixed by the `μ₃`+odd+purity symmetry — structure is provably absent
*there*. **NOT DETECTED** `[EMPIRICAL — SCOPED]`: the signed single-character power spectrum is null
out-of-sample, and its autocorrelation dual with it — but only at the tested statistic, sample
(`p≤2731`), and power. The forced rows are exact; the null rows are bounded, **not** a blanket "no
structure" ([[feedback_negative_bias_enlarge_nulls_2026_07_17]]). Together they map where arrangement
structure is *constrained*, not a claim that none exists.

**Within the multiplicative hierarchy, the next object the parity argument does not force is 4th
order.** (Other 3rd-order objects — the additive bispectrum, the additive-multiplicative cross — are
separate and untested.) The odd parity that zeroed the 3-pt bispectrum does NOT zero the 4-pt object
(odd⁴ = even; four odd characters with `χ₁χ₂=χ₃χ₄` give a nonzero trispectrum
support). Its 1-point shadow is the **4th moment `E[u⁴]`**, the record's own SU(2)-vs-reduced
**monodromy discriminator** (full SU(2) ⇒ Catalan `C₂=2` ⇒ `E[u⁴]=1/8`). That is a **symmetry-TYPE**
question — what is the monodromy group of the `χ₂(y)` sheaf — which is exactly the kind of object the
Anomaly-Drill protocol aims at, and it is the natural next prereg after the magnitude channel closes
the 2nd-order picture.

---

## §5 — Provenance

- `forced_landscape_v1.py` (exact forced identities + magnitude preview), `twist_orbit_magnitude_run_v1.py`
  (magnitude instrument; C-NOFLOAT OK; PLANT fires 6.5–9.3×).
- Builds on `RESULT_twist_orbit_spectrum_v1.md` (signed null) and `PREREG_twist_orbit_spectrum_v2.md`.
- Forced identities verified `p∈{127,163,211,349,547}`; magnitude out-of-sample pending
  `PREREG_twist_orbit_magnitude_v1.md` on the frozen S (SHA `7cde99fe…`).
