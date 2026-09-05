# The quadratic-phase ("chirp") plane: a new object, its one dark fringe, and a scoped null

**Date:** 2026-07-30. Script: `chirp_hologram_scan_v1.py` (+ `chirp_hologram_scan_v1.json`).
**Grade: `[EXPLORATORY — EMPIRICAL, scoped, out-of-sample retest run]`.**
No leakage claim. No closure. No grade moves on any other item.

⚠ **DISCIPLINE DISCLOSURE, up front.** This run has **no `experiment-designer` pre-registration.**
That gate was deliberately relaxed by the user for this line of enquiry ("if we make things too tight
too early we might miss the thing we're looking for"), on the stated understanding that a phase 2
corrects false positives. This is a **user-authorised exception, not an unavailability** (CLAUDE.md
§2a's branch does not apply). The mitigation actually used: the forced-structure controls and the
plant were fixed before the real-data numbers were read, and the one cell that popped was retested
out-of-sample on fresh primes (§4). **No number here may move a grade** until a gated replication runs.

---

## 1. The object (new to this record)

    H(k,a) = Σ_{d ∈ ℤ/n} c(d) · e_n(k·d² + a·d),      c(d) = χ₂(y of [d]G)

**The record's entire twist-orbit programme is the `k = 0` LINE of this plane** — `H(0,a) = V(−a)`.
Magnitude spectrum, additive/multiplicative autocorrelation, bispectrum, monodromy moments are all
built from that one line.

**Why the plane is not covered by the record's own bounds:**
- `spectral_concentration_closure_v1.md` bounds `Corr_F(a) = (1/n)Σ_d F([d]G)e_n(−ad)` — a **linear**
  phase, i.e. a character of `ℤ/n`. **`e_n(kd²)` is not a character of `ℤ/n`**, so that estimate says
  nothing for `k ≠ 0`.
- The Wiener route is vacuous. The record **already proved** the chirp's spectrum is flat at `√n`
  (`PREREG_row_budget_lowtail_v1.md` F8: `|Ĝ(a)| ∈ [√n−1, √n+1]`, used there as a *control target*,
  never as a detector). Hence `‖chirp‖_A = √n`, and
  `|H(k,a)| ≤ ‖chirp‖_A · max|V| ≤ √n·2√p ≈ 2p` against a **trivial bound of `n ≈ p`.**
- **★ The chirp is the record's own named escape hatch, instantiated.** The standing statement is that
  the last single-point escape needs *"a `d`-side function with `‖·‖_A ≳ √p`, which must be CHEAP"*,
  and that *"constructing one requires knowing the spectrum you are matching."* A chirp attains
  `‖·‖_A = √n` **exactly, for free, knowing nothing** — one modular multiplication to evaluate.
- A quadratic-phase sequence has a **flat magnitude spectrum and a delta autocorrelation** — the exact
  fingerprint the record reports as *"maximally structureless subject to `μ₃`+odd+purity."* A chirp is
  invisible to every statistic in the record.

## 2. Forced structure of the plane (exact; controls, not findings)

| | law | check |
|---|---|---|
| F1 | `c(n−d) = −c(d)` ⇒ `H(k,−a) = −H(k,a)`, `H(k,0) = 0` ∀k | `C_ODD` **True**, all primes |
| F2 | `c(λd)=c(d)`, `λ³=1` ⇒ `H(kλ², aλ) = H(k,a)` | plane residual **≤ 1.3e−14**, all primes |
| F3 | `k=0` line is `V` ⇒ `max_a|H(0,a)| ≤ 2√p` | `C_CAP_k0` **True**, all primes |

F2 ⇒ effective independent cells `≈ n²/6`. Both nulls preserve F1 (+F2 for the class null), so the
max-comparison is like-for-like.

## 3. Readout `R(k) = max_a |H(k,a)|²/n`

**★ POSITIVE CHARACTERIZATION — the `k=0` line is the DARKEST line in the plane, at every prime.**

| p | n | R(0) | cap `4p/n` | min over `k≠0` | median `k≠0` | percentile of R(0) |
|---|---|---|---|---|---|---|
| 823 | 829 | 3.663 | 3.971 | 4.72 | 6.44 | **0.00 %** |
| 1303 | 1249 | 3.973 | 4.173 | 4.99 | 6.97 | **0.00 %** |
| 1831 | 1753 | 4.137 | 4.178 | 5.08 | 7.14 | **0.00 %** |
| 2251 | 2341 | 3.804 | 3.846 | 5.25 | 7.57 | **0.00 %** |
| 2731 | 2689 | 3.916 | 4.062 | 5.36 | 7.58 | **0.00 %** |

**All `n−1` other chirp rates have a strictly higher max than the linear one**, and `R(0)` sits just
under its `2√p` ceiling. This is the proved cap **made visible as a dark fringe**: the record's line is
the one place in the plane where the amplitude is suppressed. It is a re-presentation of a known
theorem, **not** a new law — but it is the first picture of what the cap looks like from outside its
own line, and it says the suppression is specific to linear phases (the 4-dim Weil bound applies to
characters; `k≠0` lines are not bounded by it and indeed run ~2× higher).

**NULL — off the `k=0` line the plane is at the null level, everywhere.**

| p | data max `k≠0` | null(class) mean / max | draws ≥ data |
|---|---|---|---|
| 823 | 11.86 | 11.15 / 14.13 | 4/12 |
| 991 | 11.16 | 11.34 / 13.62 | 6/12 |
| 1303 | 11.88 | 12.48 / 14.25 | 9/12 |
| 1831 | 13.69 | 12.84 / 15.04 | 3/12 |
| 2251 | 12.47 | 12.94 / 14.58 | 8/12 |
| 2731 | 13.10 | 14.06 / 16.95 | 10/12 |

Profile-wise the agreement is exact, not just at the max (p=2731: data med 7.58 / null 7.56; p95 9.87 /
10.20). **QR/NQR split on `k`: null** (7.703/7.732 vs null 7.866/7.764 at p=2731) — no Gauss-sum sign
effect.

## 4. The one cell that popped, and its death out-of-sample

Exploration flagged `k = t` (Frobenius trace) at **p=2731: 98.8th percentile** (R=11.21 vs median 7.58);
in-sample profile across 5 primes was 85.3, 67.8, 43.3, 50.5, 98.8.

**OOS retest, 12 fresh primes `p ≡ 7 mod 12`, none reused** (1051…4831):
mean percentile **52.8 %** (null 50), max **89.8 %**, **0 above the 95th**, 0 above the 90th.
`P(≥1 of 12 above the 95th | null) = 0.46`.

**⇒ dead.** A third chance pattern for the ledger, killed by the pre-committed OOS rule before it was
named. Recorded because the protocol says to record it, not because it was ever a finding.

## 5. POWER — the honest headline, and why it is modest

`C-PLANT` = the **matched odd chirp** for a cell, mixed in at fraction `frac`:

| p | frac 1.0 | 0.5 | 0.25 | 0.12 | detection floor |
|---|---|---|---|---|---|
| 823 | 12.0× ✓ | 2.3× | 0.7× | 0.8× | 1.0 |
| 1303 | 17.3× ✓ | 4.6× ✓ | 0.5× | 0.5× | 0.5 |
| 1831 | 23.3× ✓ | 4.2× ✓ | 1.4× ✓ | 0.6× | 0.5 |
| 2251 | 29.3× ✓ | 7.1× ✓ | 2.0× | 0.8× | 0.5 |
| 2731 | 29.9× ✓ | 8.3× | 2.2× ✓ | 0.7× | 1.0 |

(✓ = peaks at the planted `κ`. Ratio vs null-class mean.)

**★ A structural fact found while fixing the control (the v1 plant did NOT fire — logged).**
Because `c` is forced **odd** and real `±1`, and `e_n(kd²)` is **even** in `d`, a sequence cannot track
a quadratic phase — the sign is all it has. Pairing `d ↔ −d`:
`H(k,a) = Σ_{d=1}^{(n−1)/2} c(d)·e_n(kd²)·2i·sin(2πad/n)`, so the best real odd `±1` alignment captures
only the real part, `≈ 0.16n` against a trivial `n`. **The forced oddness itself suppresses chirp
alignment by a constant factor** — the naive `sign(Re e_n(kd²+a₀d))` plant is not the matched one, and
using it (the v1 bug) makes the control fail to fire.

**SCOPE of the null, stated as a bound:** a single-cell quadratic-phase component aligned at `≳50 %`
of the matched-odd optimum would have been detected at `p ∈ [1303, 2251]`. **Below ~25 % alignment,
and at these `n`, the scan is blind.** Null grows like `≈ 4 ln n`; a full plant grows like `0.16n` —
so **power improves with `n`**, and the natural next move is larger primes, not more primes.

## 6. What this does and does not say

- **Does:** the quadratic-phase plane exists, is measurable, is not covered by the record's bounds,
  and is **flat at the null level at 11 primes + 12 OOS primes**, at the stated power. The `k=0` line
  is its unique dark fringe.
- **Does NOT:** close the quadratic-phase route. Untested and named: alignment below ~25 %; larger `p`
  (where power grows); **cubic and higher phases** `e_n(kd³)`; **multiplicative chirps** (quadratic in
  the discrete log rather than in `d`); joint `(k,a)` structure beyond a single bright cell; and the
  `j≠0` mechanism control (not run here).
- **Does NOT** re-open or move `spectral_concentration_closure_v1.md`. That closure is about linear
  phases and stands exactly as written; this is a different object that it never covered.
