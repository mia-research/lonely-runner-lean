# DEVIATIONS — `PREREG_kden_ramanujan_comb_v1.md`

Disclosed per §1.2 of the frozen spec.

---

## D1 — W1-plant did not fire as first implemented; plant corrected (not the hypothesis)

**Detected:** first execution on configurations T1, T2.

**What happened.** §4.1 requires each wrong-prediction control to produce `mismatch > 0`, else the
H2 arm is VOID. The first implementation of **W1-plant** ("drop the coprimality filter — intervals at
*all* `j ∈ [0,q)`") returned `mismatch = 0` on both configurations:

```
PLANT W1-plant(all j)   mismatch = 0   *** FAILED -> VOID ***
```

**Cause.** The plant reused the §0.4 closed-form half-widths at each centre. At a **non-primitive**
centre `j/q` (`gcd(j,q) = g > 1`) there exists `d ≤ M`, `q ∤ d`, with `u_d = (d·j) mod q = 0`, which
drives the derived half-width to `0`. Every non-primitive interval therefore came out **empty**, and
the plant silently reproduced the primitive (HYP-G) prediction instead of contradicting it. It was
not a wrong prediction, so it could not act as a control.

**Fix.** In `all_j` mode every centre is given the half-width of a *primitive* centre
(`jb = j if gcd(j,q)==1 else 1`), so the plant genuinely predicts `q` intervals rather than `φ(q)`.
After the fix it fires on every configuration in `C` (`mismatch` ranging `481 … 63406`).

**Scope of the change.** The fix touches **only the wrong-prediction control**. The prediction module
used for H2b/H2a (`centre_mode='primitive'`) is byte-identical before and after, and the endpoint
tables and their SHA-256 hashes in `kden_endpoint_hashes.txt` are unchanged. No hypothesis,
statistic, null, or falsification condition was altered.

**Worth recording as content, not only as a bug.** The mechanism that broke the plant *is* the
derivation's own account of why the count is `φ(q)` and not `q`: a non-primitive centre admits a
competitor `d` with `u_d = 0` — i.e. `q/g` beats `q` there — so the interval has zero width. The
coprimality filter is not imposed on the geometry; it falls out of it.

---

## D2 — H3 (spectral arm) not yet run

The confirmatory run covers **H2b (PRIMARY) and H2a** only. The H3 spectral arm (§2.5–2.6:
`R2_ram`, `ΔR2`, `Δ_HC`, `TOP3_pred`, `H3-legacy`, PC-comb / PC-comb-α / PC-neg) has **not** been
executed. Per §6 this is a disclosed deviation naming the arm, not a silent filter.

Consequence for reading the result: under Branch A of §7 the H3 arm is **characterization only**
regardless of outcome, so its absence does not weaken the H2b conclusion — but no statement about
the `|f| = 12/24/24` top mode, about highly-composite frequency concentration, or about the
`M = 100` vs `M = 101` cutoff contrast may be made until it is run. Those remain open.

---

## D3 — `q = 1` special-cased in the endpoint derivation (gap in the frozen §0.4)

§0.4 derives the interval bounds from `u_d = (d·j) mod q ∈ {1,…,q−1}`, having observed that
denominators `d = m·q` never bind. **At `q = 1` every `d` is a multiple of `q`**, so the constraint
set is empty and the derivation returns nothing — a gap in the frozen text, not in the data.

**Closed in the same closed form, before any comparison was run.** With `θ = η` near `0`,
`‖dη‖ = d|η|` while `d|η| ≤ 1/2`, so `q = 1` wins until `η = 1/(M+1)`; the binding competitor is
`d = M > q`, hence the comparison is **non-strict** and the endpoint belongs to `q = 1`. Implemented
as an explicit branch of `_bounds`.

This is a derivation completion, **not** a fit to observed data: it is determined by `M` alone, it was
written before `k_den` was computed for any configuration, and `q = 1` is excluded from every
informative tally by §0.3 F-2 in any case.
