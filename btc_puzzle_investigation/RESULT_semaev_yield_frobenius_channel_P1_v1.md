# RESULT — P1: per-prime CM Semaev yield modulation does NOT track Re(J(χ₆,χ₆)) (Outcome C, scoped null). Phase/imaginary channel is a live lead; cross-twist axis unsampled.

**Date:** 2026-08-14. Executes `PREREG_semaev_yield_frobenius_channel_P1_v1.md` verbatim (spec frozen before
computation). **Grade:** `[EMPIRICAL — SCOPED NULL, plant fired → informative; Outcome C]`. Existing R1 data
only (no new Semaev runs). Script: `p1_run.py` (+ `p1_secondaries.py`, `eisenstein_frobenius.py`, all validated).
**Not a closure of the Frobenius/Weil mechanism** — see §3. **No secp/ECDLP claim.**

---

## 1. Instrument validity (both required, both hold)

- **Firing plant** `W_synth = rank(T1pool)+η` calibrated to `Spearman=+0.607`: **perm_p = 0.00207 → FIRES.**
- **Negative calibration** (1000 iid-random invariants): fire rate **0.054** at α=0.05 — no inflation.
- Confound layer (pre-run, from `(p,b)` only): all 24 j0 cells are `y²=x³+1` (b=1); `W=2Re(J(χ₆,χ₆))` is
  exact-integer, generator-independent, and `Spearman(W,#E)=+0.11`, `Spearman(W,p)=+0.10` (independently
  reproduced here: **the same trace t=8 gives W=35 at p=523 vs W=8 at p=691** — W is not #E in disguise).

## 2. Primary result — NULL, scoped

`T1pool[p] = mean over |V|∈{6,7,8} of T1(j0)[p]` (24 primes) vs `W[p] = 2Re(J(χ₆,χ₆))`:

| quantity | value |
|---|---|
| Spearman(W, T1pool) | **−0.160** |
| perm_p (two-sided, integer S, 200 000 relabelings, seed 20260814) | **0.455** |
| partial Spearman(T1pool, W \| #E, p) | −0.165 |
| diagnostic Spearman(T1pool, #E) | −0.033 |

Primary `p=0.455 > 0.05` with the plant fired ⇒ **Outcome C.** The per-prime yield modulation is **not** a
monotone linear-in-`Re(J)` effect at the design's power (MDE `ρ_s ≈ 0.56`; the test cannot resolve
`|ρ_s| ≲ 0.4`).

## 3. What Outcome C does and does NOT establish (per pre-commitment §6-C)

**Scoped null:** no monotone `Re(J)` association of size `ρ_s ≳ 0.56`, at `p∈[523,823]`, `m=3`, `|V|∈{6,7,8}`,
**single twist b=1**. This is a magnitude bound, **not** "no Frobenius mechanism." Explicitly untested:

- **Higher sextic moments** `Re(Jᵏ), k≥2`.
- **The oriented phase / imaginary channel** — and here the secondaries give a **live lead** (exploratory,
  Bonferroni α=0.0125, never a verdict): `Im(J)/√p` **ρ=+0.435, p=0.036** (below .05, above Bonferroni);
  folded angle ρ=+0.38, p=0.067; `arg(π)%60` ρ=+0.27 (null); `arg(J)%60` ρ=+0.05 (null). The signal, if
  any, sits in the **phase/imaginary** part, not the real part the primary tested. **A dedicated
  pre-registration of the oriented-phase channel is the named next probe** — not a claim here.
- **The entire cross-twist sextic modulation.** Because b=1 is fixed across all 24 cells, R1 sampled the
  μ₆ sextic axis **only through p**. The largest unexplored dimension of the mechanism is untouched.

**Also note:** P1 tested the per-prime *heterogeneity* of T1, not the *mean* CM>non-CM excess (R1's
headline). The mechanism of the mean excess is uncharacterized by P1 either way.

## 4. Net (for the re-opened R1 lever enquiry)

The yield modulation is **not** carried by the real part of the sextic Jacobi sum at this power/scope. That
neither confirms nor refutes the Frobenius/Weil mechanism — it **relocates** where to look: the oriented
phase/imaginary channel (a marginal lead) and, more importantly, the **cross-twist axis** the b=1 schedule
never varied. Two named next probes: (P1′) oriented-phase channel, own prereg; (P1″) a cross-twist R1 run
(vary b over the six sextic classes) to sample the μ₆ axis directly. The lever question (does the yield
advantage lower total prime-field cost) remains open and separate — this result is about the *mechanism of
the modulation*, not the cost.
