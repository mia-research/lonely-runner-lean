# The cap-respecting null, the re-adjudicated curve-native panels, and the `V₂` identity confirmed

**Date:** 2026-07-30. Scripts: `semicircle_null_v1.py`, `curve_native_beam_scan_v2.py`,
`verify_V2_identity_v1.sage`. **Grade: `[EXPLORATORY — EMPIRICAL, scoped, OOS retested]`**
except §3, which is **`[VERIFIED — exact, 3 primes]`**.
⚠ Same user-authorised gate relaxation — **no `experiment-designer` prereg on §1–§2.**

---

## 1. The cap-respecting, marginal-varying null — the blocker is removed

**The blocker** (`RESULT_theta_structure_v1.md` §4, `RESULT_phase_family_and_tail_v1.md` §3b): two
nulls existed and neither could test a `|V|`-marginal statistic. The frequency-domain class
permutation preserves the `|V|` multiset **exactly** ⇒ zero power against spacings, order statistics,
`Δ₃`, `Σ²`, the whole Katz–Sarnak family, and the entire upper tail. The signal-domain permutation
**violates the proved cap** (top-5 `|V|/√p` = 2.74–3.25 against a ceiling of 2).

**The construction.** `u(a) = V(a)/(2i√p)` is real, and the record's own two moment facts pin its
marginal: `E[u²] = 1/4` **forced** (Parseval) and `E[u⁴] = 1/8` **measured** (= full SU(2)). The
**semicircle law** on `[−1,1]`, density `(2/π)√(1−u²)`, has `m_{2k} = Catalan(k)/4^k`, so
`m₂ = 1/4` and `m₄ = 2/16 = 1/8`. **Both match.** Equivalently `u = cos θ` with `θ ~ (2/π)sin²θ dθ`
— the **Sato–Tate measure**. So:

> **null: `u(a)` iid SEMICIRCLE on `[−1,1]`, rebuilt through the forced `μ₃` + odd symmetry.**

- **Cap-respecting by construction** (`|u| ≤ 1` ⟺ `|V| ≤ 2√p`, the proved ceiling).
- **Marginal-varying** — every draw is a fresh multiset ⇒ nonzero power on order statistics.
- **It IS the Katz–Sarnak / Sato–Tate prediction** the record cites and had never used.
- Statistics must run on the `L = (n−1)/6` **free** class representatives; the other `n−1` values are
  6 exact copies and their degeneracy would swamp every spacing.

**Result — 17 primes (823…4831), R = 400, six statistics: NULL.**
Spacing KS (`S1`), number variance `Σ²` (`S2`), tail (`S3`: max, top-5, frac > 0.95), small-ball
(`S4`: frac < 0.05). Controls pass at every prime: cap holds, `E[u²]` = 0.2394–0.2600,
`E[u⁴]` = 0.1163–0.1344.

**The one consistent-looking cell, and its death.** `S3_max` ran high at **14 of 17** primes,
pooled `z = +2.06`, sign-test `p ≈ 0.013` two-sided. Retested on **15 fresh primes** (5107…7603):

| null | mean z | pooled z | signs |
|---|---|---|---|
| iid semicircle | +0.077 | **+0.30** | 8/15 |
| pooled-empirical marginal (control) | +0.139 | **+0.54** | 8/15 |

**Dead**, under both the theoretical null and a control that removes the marginal assumption
entirely. **Fourth chance pattern killed by the pre-committed OOS rule this session** (after `k=t`,
the `p=2731` multiplicativity hit, and this).

⇒ **Items 3′(1) and 4′ — the four unmeasured RMT statistics — are now RUNNABLE, and are run: null at
17 + 15 primes.** Scope: this bounds structure in the `|V|` marginal against an iid-Sato–Tate
alternative; it does not test correlations that leave every order statistic intact.

## 2. Curve-native panels, re-adjudicated (v1's null was broken)

`curve_native_beam_scan_v1.py` used a **free orbit permutation** — which destroys the forced
symmetries — and produced a phantom. v2 measures each readout's covariance multipliers exactly and
permutes only within the free classes.

**C-COV fires exactly**, confirming the covariance structure rather than assuming it:

| readout | `c_λ` (GLV) | `c_neg` | sd |
|---|---|---|---|
| `χ₂(y)` | `+1` (μ₃-invariant) | `−1` (ODD) | **0.0** |
| `χ₆(x)` | `e^{±2πi/3}` (primitive cube root) | `+1` (EVEN) | 4.5e−16 |
| `χ₂(y)·χ₆(x)` | `e^{±2πi/3}` | `−1` | 4.5e−16 |

**★ The phantom is confirmed dead.** `[I] chi2y` scored `ge = 0/6` (apparent signal) under v1's broken
null and **`ge = 10/12, 11/12, 12/12`** on identical data under the correct one.

**All panels NULL** — `χ₆(x)`, `χ₂(y)χ₆(x)`, sextant × {Q, I} at p = 823, 1303, 1831; `ge` scattered
2/12–12/12 with data at the null mean throughout.

**★ The `k=0` dark fringe is `χ₂(y)`-specific.** 0.00 percentile for `χ₂(y)` at every prime, but
34–64 % / 0–90 % for `χ₆(x)` / `χ₂(y)χ₆(x)` / sextant. The fringe tracks the `2√p` cap, which is a
statement about the twist readout — further evidence it is the cap and not a general phenomenon.

## 3. ★★ `V₂ = V₁² + 2p` — DERIVED (§1 of `RESULT_theta_structure_v1.md`) and now CONFIRMED

`verify_V2_identity_v1.sage`: `V_k(a) = Σ_{P ∈ E(F_{p^k})} χ₂(y_P)·ζ_n^{a·dlog(Tr P)}` via the exact
integer histogram, at 120-bit precision.

| p | n | C1 `h₁ ≡ c` | C2 `max|Re V₁|` | C2 cap | `max_a|V₂ − (V₁²+2p)|` | `max_a|V₂ − (V₁²−2p)|` |
|---|---|---|---|---|---|---|
| 43 | 31 | **True** | 3.0e−33 | True | **4.8e−32** | 1.72e+02 |
| 67 | 79 | **True** | 4.2e−33 | True | **1.1e−31** | 2.68e+02 |
| 127 | 127 | **True** | 1.5e−32 | True | **6.1e−31** | 5.08e+02 |

**Two outcomes:**
1. **The derivation is confirmed.** The identity the record carried as `[VERIFIED-exact] … NOT
   derived` is a **corollary of the 120° configuration**. ⇒ **The cap chain
   `120° ⇒ V₂ = V₁²+2p ⇒ S_y ≤ 2 ⇒ |V| ≤ 2√p` has one open link, not two**, and it is the link
   already identified: the **Kronecker/Stickelberger ideal route** to 120°.
2. **★ The sign is resolved.** The record writes `V₂ = V₁² ± 2p`; the derived and confirmed sign is
   **`+2p`**, by a margin of 30+ orders of magnitude. `[VERIFIED — exact, p = 43, 67, 127]`

⚠ Scope: 3 primes, all small, all `p ≡ 3 mod 4`. The *derivation* is general given the 120°
configuration; the *numerical* confirmation is not a proof of that configuration, which remains
verified-at-22-primes rather than proved for all `p`.
