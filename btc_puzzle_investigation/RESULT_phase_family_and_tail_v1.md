# Phase families beyond the chirp, and the first tail-instrument pass

**Date:** 2026-07-30. Scripts: `phase_family_scan_v1.py`, tail pass in scratchpad.
**Grade: `[EXPLORATORY — EMPIRICAL, scoped]`.** No verdict, no closure, no grade moves.
⚠ Same user-authorised gate relaxation as `RESULT_chirp_hologram_plane_v1.md` — **no
`experiment-designer` prereg; no number here may move a grade.**

---

## 1. Four phase families, not one

`H(k,a) = Σ_d c(d)·e_n(φ_k(d) + a·d)`, `k=0` always the record's line.

| fam | `φ_k(d)` | parity | R(0) pctile | data max `k≠0` | null mean/max | ge |
|---|---|---|---|---|---|---|
| **Q** quadratic | `k d²` | even | **0.00 %** | 11.86 / 11.88 | 11.06 / 11.73 | 2–3/6 |
| **C** cubic | `k d³` | odd | **0.00 %** | 25.61 / 25.68 | 29.89 / 37.49 | 3–6/6 |
| **I** inverse | `k d⁻¹` | odd | **0.00 %** | 20.11 / 21.07 | 21.86 / 21.55 | 3–5/6 |
| **M** mult. chirp | `k m²`, `d=g^m` | even | 71–82 % | 48.84 / 59.37 | 54.23 / 64.12 | 4–5/6 |

(p = 823 and 1303; each family against its own class-permutation null.)

**All four NULL.** Data max is at or below the null mean in every family at both primes.

**★ The `k=0` dark fringe is NOT an artifact of the quadratic family — it holds for Q, C and I
alike (0.00 percentile, i.e. every one of the `n−1` other rates is brighter).** It does **not** hold
for M (71–82 %), and that is the expected discriminator: M's `k=0` line is the *multiplicative*
spectrum, which the `2√p` Weil cap does not constrain in the same way. So the fringe tracks the cap,
as it should.

## 2. A prediction I made, and how it actually came out

I predicted that because `c` is forced **odd**, an **odd** phase would allow ~4× better alignment
(`≈0.64n` vs `≈0.16n`) and therefore ~16× the power. **Half right, and the half that failed is
informative.**

- **Alignment:** confirmed directionally but weaker than predicted — cubic full-plant absolute
  `R ≈ 323` vs quadratic `≈ 134`, a factor **2.4×**, not 4×.
- **Power:** **no gain for C.** The cubic *null* is inflated by almost exactly the same factor
  (29.9 vs 11.1), so the ratio does not improve; detection floor stays at `frac = 1.0`.
- **Why:** `n ≡ 1 mod 3` is **forced** in this setting (L3), so `d ↦ d³` is **3-to-1**, not a
  bijection. The cubic phase takes each value three times, which inflates the null's fluctuations by
  the same factor it inflates the signal. The parity argument was right about the numerator and blind
  to the denominator.
- **The bijective odd family behaves as predicted:** **I (inverse) is the best-powered lens tested** —
  floor `0.5`, and it still peaks at `κ` at `frac = 0.25` (and at 0.12 at p=823). Roughly **2–4× the
  sensitivity of the quadratic scan.**

⇒ **For future lenses the selection rule is: odd phase AND a bijection.** `d⁻¹` qualifies; `d³` does
not at these `n`.

## 3. First pass with the tail instrument class (P5)

The record's standing note: *"every statistic is MEAN-based; LLL/HNP live in the TAIL"*, and
extreme-value statistics have never been used. Two readouts on `|V(a)|/√p`, 5 primes:

**(a) Small-ball exponent `P(|V|<ε) ~ ε^β`.**
Data `β` = 0.54, 1.05, 1.01, 1.26, 0.90. Null `β` = 1.01, 1.23, 0.90, 1.03, 1.08 (±0.21–0.45).
**Data ≈ null ≈ 1 at every prime. No low-tail anomaly.**
**★ But it confirms the record's suspicion mechanically:** `β = 1` is **forced** because `V` is purely
imaginary (a 1-dimensional object). A **Rayleigh / complex-Gaussian null predicts `β = 2`**, so any
near-zero test run against Rayleigh on this object manufactures a large spurious excess of near-zeros
— *without any structure being present*. This is the concrete version of the flagged
*"#17's Rayleigh null is likely the WRONG null"*, now measured rather than argued.

**(b) Upper tail — and a defect in my own null, caught by a proved constraint.**
Data `max|V|/√p` = 1.921, 1.952, 1.990, 1.989, 1.964 — **always just under the proved cap of 2**, at
every prime (the cap nearly saturated, consistent with the record's ½-saturation).
My **signal-domain** class-permutation null gives top-5 means of **2.74–3.25 — it exceeds the cap.**

**⇒ Two nulls, and neither can test the tail of `|V|`:**
1. My signal-domain null (permute `c`'s class values) **is not cap-respecting** — it generates
   configurations the real object provably cannot reach, so any upper-tail comparison against it
   reports a forced, artifactual "deficit". **Invalid for tail statistics on `V`.** (Caught only
   because a proved constraint was available to check against — the cap earning its keep as an
   instrument check.)
2. The twist-orbit pipeline's **frequency-domain** null (permute `ρ = V(g^c)`) *is* cap-respecting,
   but it permutes `V`'s own values, so **the `|V|` multiset is invariant by construction** ⇒ it has
   **exactly zero power** against any statistic that depends only on the `|V|` marginal — which is
   every tail and extreme-value statistic on `|V|`.

**★ Therefore: the upper tail of `|V|` has never had a valid null in this record.** Not "tested and
null" — **untested, for a structural reason.** Constructing a cap-respecting, marginal-varying null is
a prerequisite for any caustic/tail probe, and it is the concrete next obstacle on Wall 2 of
`ANALYSIS_destructive_interference_frame_v1.md`.

## 4. Status of the phase-family route

- **NULL** across Q/C/I/M at p ∈ {823, 1303}, at the stated power (floor `0.25–1.0` alignment
  depending on family). Not a closure — a bounded magnitude on single-cell phase alignment.
- **Untested and named:** larger `p` (null grows `≈4 ln n`, plant grows `≈0.16–0.64 n`, so **power
  improves with `n`** — the efficient move is bigger primes, not more primes); the `I` family at large
  `p` where its floor may reach `0.12`; joint/multi-cell structure; the `j≠0` mechanism control.
