# RESULT v3 — H-CAP survives OUT-OF-SAMPLE; convergence is R-INDET by the spec's own clause

*2026-07-24. Executes `PREREG_n1_phase_cap_v2.md` on a frozen, previously-unread holdout.
Supersedes `RESULT_n1_phase_cap_v2.md` (the re-graded seen-data run). Deviations:
`PREREG_n1_phase_cap_v2_DEVIATIONS.md` (**6 — read them**). Scripts: `n1_phase_cap_v2_freeze.sage`,
`_run.py`, `_controls.py`, `_nullfix.py`, `_pdose.py`.*

**No leakage, key-recovery or ECDLP claim. Nothing reaches `p = 2²⁵⁶−2³²−977`.**

---

## 1. `C-FREEZE` — the holdout was frozen and hashed before any `V(a)` existed

| | |
|---|---|
| rule | 10 log-spaced bands `[10^4.50, 10^6.00)`, first 6 accepted primes per band per stratum |
| result | **120 primes** (60 ODD `p≡7 mod 12`, 60 EVEN `p≡1 mod 12`), `p ∈ [31627, 711577]` |
| cells | **4,735,158 distinct μ₆ configurations** |
| rejects | 1220 composite `n`, 0 Hasse failures, 0 `p≢1 mod 3` |
| SHA-256 | `3c24e9ee660f9789a54b06fc27f1484a258ee09d680f92a241f56193eba77527` |

**All of it is `p > 30000`, which no statistic had ever touched.** This is a genuine holdout — unlike
the strata arm earlier this session, where I had to attest that the proposed holdout did not exist.

## 2. Every control fires

| control | result |
|---|---|
| **P-CEIL** (must-fire ceiling witness) | predicted **from `n` alone before any readout**, matched to **`2.5×10⁻¹⁶`** relative; `S = 56.1 … 189.6` — **`≫ 2`**. This is precisely what v1 could not show (its D3). |
| **P-FLOOR** (must-fire floor witness) | `h = χ_n` lands **exactly** on the Parseval floor `√(n/p)`, rel dev `1.9×10⁻¹⁵`, spread across all `a` `3×10⁻¹⁵` (a Gauss sum: `|V(a)| = √n` for every `a≠0`). |
| **N-PERM** (primary null) | mean `S = 4.24` (ODD 4.255 / EVEN 4.231), min **3.341**, **0 of 120 draws `≤ 2`** ⇒ **no halt**. F7 predicted `≈4.65`. |
| **P-DOSE** (fragility) | **`ε* ≤ 0.02` at 20/20 plant primes** — the smallest level swept. |
| `C-PARSEVAL` / `C-PURITY` / `C-CELLS` / `C-ORBIT` | `≤1.3×10⁻¹⁵` / `≤6.4×10⁻¹⁶` / all / **120/120** (after the D1 fix) |

**The realizable range is pinned with both endpoints attained by named explicit targets**:
`[√(n/p) ≈ 1.0 , ≈0.32√p ≈ 190]`. `χ₂(y)` sits at `≈2`. No outcome here is a bare magnitude.

**P-DOSE settles the interpretation question the spec insisted on.** Swapping just **2%** of the μ₆
orbit signs already carries `S` from `≤2` to `2.51–2.89`; by `ε=0.10` it is `3.2–4.2`. The spec
pre-committed `ε* ≤ 0.10 ⇒ the cap is FRAGILE, so `χ₂(y)` sitting under it is informative`, versus
`ε* ≥ 0.25 ⇒ near-vacuous and the question uninteresting`. **The fragile branch fires, decisively.**

## 3. PRIMARY — H-CAP survives out-of-sample

> **`[VERIFIED — OUT-OF-SAMPLE, 120 frozen primes, 4,735,158 distinct μ₆ configurations]`
> `S_y(p) = max_{a≠0}|V(a)|/√p ≤ 2`. `Nviol = 0`.**
> Range `[1.98567, 1.99999]`.

A falsifying instance was available at every prime and every one of 4.7M cells, the statistic was
shown able to report `S` up to 189.6 on an admissible target of the same shape (P-CEIL) and down to
the Parseval floor (P-FLOOR), and a symmetry-matched null of the same readout reads `4.24` — never
below `3.34`. **This is the pre-registered, out-of-sample result, and it is the one thing in this
whole line that now carries a real grade.**

## 4. Convergence — **R-INDET**, by the spec's own pre-committed robustness clause

`L(p) = log₁₀(2 − S_y)` regressed on `log₁₀ p`, per stratum, `K = 60`, `df = 58`:

| stratum | `β̂` | `SE` | `t₀` (vs 0) | `t₁` (vs −0.448) | G2 | G1 top−bottom |
|---|---|---|---|---|---|---|
| ODD | −0.8035 | 0.1330 | **−6.04** | −2.67 | R2 | −0.9171 (corroborates R2) |
| EVEN | −0.7585 | 0.1283 | **−5.91** | −2.42 | R2 | −0.8022 (corroborates R2) |

Both gates say R2, in both strata. **But the measured residual scatter is `σ̂_L = 0.4407` (ODD) and
`0.4219` (EVEN), and the spec pre-committed that `σ̂_L > 0.35` ⇒ report R-INDET and do NOT enlarge
`K`.** That clause fires.

> **The convergence question is NOT settled. R-INDET.** This is a pre-committed clause firing on a
> measured quantity — not the post-hoc trend-read that v1's D5 was. The correct statement is that
> `S_y ≤ 2` holds out-of-sample and that **whether `S_y → 2` remains open.**

*(Reported, not read as a result: `β̂ ≈ −0.78` is steeper than the seen-set `−0.448`, and `t₁` is
negative in both strata — so R3 did not fire either.)*

## 5. What this does and does not establish about N1

**Establishes** — `max_a|V(a)| ≤ 2√p` on 120 unseen primes, with a fired ceiling control, a fired
floor control, a symmetry-matched null at `4.24`, and a fragility of `ε* ≤ 0.02`.

⚠ **PROXY TAG, carried per the spec.** `S_y ≤ 2` is object-level for `max|V| ≤ 2√p`. Its translation
into the phase language — `|sin θ₁ + sin θ₂| ≤ 1` — rests on the **weight-1 premise**, which is
`[VERIFIED at p = 13, 43 only — six unforced cells]` and costs `O(p⁴)`, so it **cannot be checked
anywhere in this holdout**. Every phase-language sentence inherits that tag. ARM-3 (extending the
premise to `p ≤ 100`) was **not run**.

⚠ **`S_y ≤ 4` is forced by Weil**, and the randomization nulls do not reproduce it — they sit at
`≈4.24`. So part of the real-vs-null gap is a restatement of Deligne. **The live content is the
factor 2 from `4` down to `2`**, not from `4.24` down to `2`.

⚠ **`S_y ≳ 1` is forced by Parseval** (`mean_a|V|² = n−1` exactly). So H-CAP is precisely: *the max
over `≈(n−1)/6` cells is at most twice the rms.*

## 6. Status

- **N1 / §XI.10:** the cap `max_a|V| ≤ 2√p` is now an out-of-sample verified fact with fired controls.
  Whether it is *tight* (`S → 2`) is **R-INDET**. The frontier is **not closed**.
- **Open and sharp:** prove `|sin θ₁ + sin θ₂| ≤ 1`; and extend the weight-1 premise beyond two primes
  so the phase language stops being a proxy.
- A `σ̂_L`-robust convergence design is what a v3 spec would need; the spec forbids simply enlarging
  `K`, which is the correct call and the reason this run abstains on convergence rather than
  over-reading `t₀ = −6`.
