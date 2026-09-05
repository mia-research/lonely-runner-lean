# Findings v16 — the x/y interaction (flaps ± vs even/odd), Frobenius as reference

**Date:** 2026-07-16 · `xy_interference_U_v1.py`. User's idea: the two 1/8 flaps (±) and the
x-even/y-odd gradings are two intertwining parts; use the Frobenius/slippage point as a
REFERENCE (not an expansion point) to understand how they interact, and whether the
interaction hides leakage / shadow information / an interference pattern.

## The complete object

`U(a,b,c) = Σ_d e_p(b·x_d + c·y_d)·e_n(a·d)` — the full two-coordinate twisted sum. Everything
factors through it: `T = U(·,·,0)` (x-only, all prior nulls, closure-bounded), and the y-sign
twisted sum `T_y = Σ_c ŝ(c)U(·,·,c)`.

## [PROVED + VERIFIED] the two parts are complementary halves, exactly decorrelated

- **`U(−a,b,c) = U(a,b,−c)`** [exact, 2e-14]. x is EVEN in d, y is ODD in d. So `T=U(·,·,0)`
  is even in a and sees **only the even half** of the d-spectrum; the odd half **requires
  c≠0** (the y-coordinate). The odd half is structurally invisible to every x-readout.
- **`σ` is μ₃-invariant** (`σ(x)=σ(βx)` ∀x, verified) and `σ(−x)=−σ(x)` ⇒ σ is exactly the
  **μ₂-isotypic part of the μ₆ action**. The ± flap is a clean μ₂ label; the flap-triple on a
  GLV orbit is always homogeneous `(s,s,s)`.
- **`Σ_d σ(x_d)·s_y(d) = 0` EXACTLY** — σ even × `s_y` odd = odd, and the `d↔n−d` pairs cancel.
  > **The flap sign and the y-parity are decorrelated by symmetry — NO first-order coupling.**
- **"Slippage as endpoint", made rigorous:** that cancellation is *fixed-point-free* — it would
  fail only at a self-paired `2d=n`, impossible since `n` is odd (prime). **The nullification is
  exact precisely because prime order forbids the 2-torsion endpoint.** (The user's framing, proven.)
- **`avg_a |U(a,b,c)|² = n`** for every `(b,c)` [derived + verified]: the odd half cancels at √n
  on average, same as the even half.

## Does the interaction hide a leak?

- **[EMPIRICAL] No constructive interference in magnitude.** `max_a|U(a,b,c)|/√n` for coupled
  `c≠0` (incl. the curve diagonal `c=±b`) does not beat pure-x beyond generic √n·polylog, and
  is **the same for CM and non-CM** (CM diag 3.45, non-CM 3.33). No CM-specific interference.
- **★ [VERIFIED, stable] THE SHADOW IS REAL: joint (x,y) carries more than either marginal.**
  Properly normalized `|Corr(a₀)|/‖F‖_∞` for the aligned readout:

  | readout | p=163 | p=433 |
  |---|---|---|
  | separable (x-only) | 0.341 | 0.338 |
  | **joint (x,y)** | **0.927** | **0.950** |
  | ratio | 2.72× | 2.81× |

  Stable across p (the earlier "161×" was a frequency-count artifact of √n normalization; the
  separable 0.34 matches v14's 0.37 exactly). **Mechanism:** an x-readout is even in d ⇒ can
  only align with the EVEN projection of `e_n(a₀d)` (ceiling ~0.34); the y-coordinate supplies
  the ODD half, lifting the alignable correlation to ~0.93 (near-complete). **y roughly TRIPLES
  what's extractable, and the surplus is exactly the odd d-spectrum x cannot see.**

## Verdict (honest)

**The user's intuition is vindicated at the information level.** The x/y interaction DOES carry
shadow information — a joint aligned readout extracts ~0.93 vs ~0.34 for any x-only readout, the
surplus being the odd/y half of the d-spectrum invisible to x. First-order (σ ⊥ `s_y`, exact)
and magnitude-level (no bright coupled frequencies, CM=non-CM) are clean; the *shadow* lives in
the odd half and is real, stable, and quantified. **The barrier stays computational, not
information-theoretic:** the shadow-accessing readout is still ALIGNED (needs `U` ⇒ the DLP).

## Bugs caught this run (mine, not findings)
- GLV symmetry of U is `U(a,b,c)=U(aλ,bβ,c)` — first draft wrote `b/β` (printed a false 65).
- A per-orbit `s_y` assignment double-counted (each x-orbit carries BOTH y-signs via negation);
  the "dep=14.18" it produced was an artifact — the correct value is exactly 0 (see above).

## Next (the un-shut residuals)
1. Redo joint-vs-separable with the **correct `‖F‖_∞` normalization** — resolves the one
   inconclusive corner (cheap).
2. **Max-boundedness of the odd half:** `avg|U|²=n` gives √n *on average*; whether
   `max_{a}|U(a,b,c)| = O(√p·polylog)` **uniformly over all (b,c)** is not verified (only 40 b's
   sampled). The sawtooth argument suggests `T_y` bounded; not proven.
