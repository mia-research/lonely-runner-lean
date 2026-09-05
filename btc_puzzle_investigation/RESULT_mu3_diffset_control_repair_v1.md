# RESULT — μ₃ difference-set channel, repaired control

**Date:** 2026-07-30 · **Spec:** `PREREG_mu3_diffset_control_repair_v1.md` (frozen before the run)
**Scripts:** `mu3_diffset_forced_zero_reproduce_v1.py` (gates 1–2),
`mu3_diffset_run_gates345_v1.py` (gates 3–5) · **Log:** `mu3_diffset_gates345_run_v1.log` (2043 s)
**Deviations:** `PREREG_mu3_diffset_control_repair_v1_DEVIATIONS.md` (7 recorded, D2 and D6 material)

---

## 1. Headline

**Cell A (real-82) — the pre-committed §9.2 row-1 conclusion, now earned:**

> The μ₃ weight-1 channel of the **group-law** difference multiset of the 82 solved keys carries
> **no cubic-class concentration above ε = 0.0415** (dominant class 36.10% vs 33.33%), at 80% power,
> at secp256k1's `p`, with `m = 82` / `n_p = 3321`. `[EMPIRICAL, powered, control fires]`

Measured: classes `[1093, 1110, 1118]`, `E3x = 489` in region `[84, 12537]`; `E3xy = 543` in
`[84, 12369]`. Both **inside**. `E3x/U = 0.04`, one-sided p ≈ 0.86. Dominant-class excess
`ε̂ = 0.0050`, i.e. **8× below** the detection threshold.

**This replaces** v32's "difference sets are generic" and "the xy harmonic adds nothing" with a
bounded magnitude carrying power and scope. It is **not** a closure — §9.4 of the prereg lists what
this statistic cannot see, and `E3` is a function of the marginal class counts only.

**Cell B (constructed-160) — no conclusion. The cell is ill-posed; see §4.**

---

## 2. Gates

| gate | result |
|---|---|
| 1–2 (§10 R1–R4 reproduction) | **38 PASS / 0 FAIL** |
| 3 (frozen nulls + F4) | **PASS** both cells |
| 4 (PC-A, PC-B, F1/F2/F3/F6/F7) | **PASS** all 10 recorded checks |
| 5 (studied sets) | ran; cell A decided, cell B void |

**F4 — the null is the assumed shape, and the prereg's analytic reference was good.**

| cell | n_p | measured mean | measured region | analytic `[L, U]` | U agreement |
|---|---|---|---|---|---|
| A | 3,321 | 3,340 | `[84, 12537]` | `[84, 12251]` | 2.3% |
| B | 12,720 | 12,321 | `[279, 46764]` | `[322, 46923]` | 0.3% |

**PC-A reproduces the analytic power table within MC error** (10,000 realizations/rung):

| ε | cell A measured / analytic | cell B measured / analytic |
|---|---|---|
| 0.010 | 0.054 / 0.058 | 0.193 / 0.189 |
| 0.020 | 0.190 / 0.196 | 0.748 / 0.742 |
| 0.030 | 0.470 / 0.468 | 0.987 / 0.987 |
| 0.050 | 0.941 / 0.938 | 1.000 / 1.000 |

**PC-B — the end-to-end pipeline fires, with margin.** `ε̂` tracks its target at every rung
(cell A: 0.0003 / 0.0139 / 0.0211 / 0.0311 / 0.0413 / 0.0492 against 0 / 0.0141 / 0.0211 / 0.0311 /
0.0415 / 0.0500):

| gate | required | measured |
|---|---|---|
| fire rate at ε≈0.05, cell A | ≥ 0.95 | **1.00** |
| fire rate at ε≈0.05, cell B | ≥ 0.95 | **1.00** |
| margin `E3/U`, cell A | ≥ 2.0 | **2.22** |
| margin `E3/U`, cell B | ≥ 5.0 | **8.65** |
| min-detectable, cell A at ε≈0.0415 | ≥ 0.80 | **1.00** |
| min-detectable, cell B at ε≈0.0212 | ≥ 0.80 | **1.00** |
| F2 plant above multiplicity surrogate | — | **0.99 / 1.00** |

**F7 (PC-A vs PC-B agreement) — clean, but read PC-A.** The 0.8-crossings differ by less than one
ladder rung (cell A: PC-A ≈ 0.042, PC-B ≈ 0.036; cell B: 0.021 vs 0.018). PC-B fires at a *lower* ε̂
than PC-A because the servo pins `ε̂` with low variance, whereas a natural effect fluctuates like
PC-A's plant. **The headline bound therefore quotes the analytic/PC-A number ε₈₀ = 0.0415, not
PC-B's 0.036** — the conservative choice.

---

## 3. Two results the prereg required to be measured, not assumed

- **`corr(E3x, E3xy) = +0.003`** (cell A, N=10,000) and **+0.012** (cell B, N=2,000). S5 proves the
  xy readout is a function of `x` alone, so the two cells are **not algebraically independent** —
  but they are **empirically uncorrelated**. Both statements hold; neither substitutes for the other.
  The ×4 family-wise correction is therefore close to honest rather than over-conservative.
- **Multiplicity is asymmetric between the cells.** **7042/10000** cell-A null sets contain at least
  one repeated difference (bit-lengths 1..82 include keys small enough to collide) against
  **2/2000** in cell B. The multiplicity surrogate is load-bearing for cell A specifically. Cell A's
  studied value sits inside its surrogate (97.5% = 12027), so multiplicity is not masking anything.

---

## 4. Cell B is void — studied draw ≡ null draw

`mu3_diffset_run_gates345_v1.py:361` defines `drawB`; line 369 uses it to build cell B's null and
line 416 uses **the same function on the same RNG stream** for the "studied" constructed-160 set.
The studied draw is therefore a sample from its own null distribution, and the cell has no
hypothesis: any uniform 160-subset of the pool is exchangeable with the null.

Its raw numbers, recorded and **not interpreted**: classes `[4181, 4390, 4149]`, `E3x = 51393`
against region `[279, 46764]` — outside, `E3x/U = 1.10`, outside its multiplicity surrogate (46272).
`E3xy = 3648`, inside. Dominant-class `ε̂ = 0.0177`.

Taken at face value this is a 2.5%-tail excursion: one-sided p ≈ 0.018, **×4 family-wise p ≈ 0.070**
— not significant even before accounting for the degeneracy. Its `ε̂ = 0.0177` is also *below* cell
B's own `ε₈₀ = 0.0212`, i.e. inside the regime the prereg pre-declared underpowered.

**Per §9.2 this is not reported as a fired cell.** A cell whose studied draw and null share a
distribution cannot fire *for a reason*; calling it a finding would be the "fired cell" row applied
to an artifact. The defect is in the spec, not only the code: §3.1 specifies cell B's *null* as
"m = 160 drawn uniformly from the whole pool" without giving the studied draw a different provenance.

**What cell B would need to be a test.** A null from a *different source* than the studied set —
uniform random scalars mod `n`, or the non-CM curve `E′` — so that "the constructed pool carries
cubic-class structure" becomes a contrast rather than a tautology. Recorded as the next probe. Note
cell A does not have this problem: its studied set is the actual 82 solved keys and its null is
bit-length-matched draws from the 100k known-MT19937 pool — a genuine real-vs-known-generator contrast.

---

## 5. What this does not license

- **No closure.** `[NO VALIDATED POWER]` is lifted for cell A and replaced by a bound. A bound is a
  magnitude, not an absence: anything below `ε = 0.0415` at `m = 82` is **not measured**, and no
  statement about it may be made.
- **No statement about the μ₃ channel generally.** `E3` reads the marginal cubic-class counts of the
  group-law difference multiset. It is blind by construction to phase structure, to any effect living
  in a subspace it does not project onto (§9.4), and to the field-difference object
  (`{x_i − x_j}`), which is a separate ledger with its own prereg and its own region.
- **The forced-zero cell remains an instrument assertion, not evidence.** `E3x = E3xy = 0` exactly on
  λ̂-closed sets tests the code path. It says nothing about the hypothesis.
- **Cell B's numbers are not evidence in either direction.**
