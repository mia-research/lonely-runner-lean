# PREREG v2 — ℓ≥5 MI probe (incorporates the experiment-designer audit)

**Date:** 2026-07-25 · **Supersedes `PREREG_ell_ge5_mutual_information_v1.md`, which was NEVER run on
data** — this is pre-data revision after the mandated `experiment-designer` audit, the intended
workflow, not post-hoc. Exact integers; verdicts from exact permutation counts.

Carries all of v1 §0–§7 unchanged **except** the four items below (audit findings R1, R2, R3, N1, all
verified in-script before this rewrite: `scratchpad/ell_mi_v1.py`, and the R1/N1 check).

## R1 (BUG FIX) — relabel exponents must be UNITS mod ℓ

v1's M0 control relabels `(ζ_n², ζ_p³)`. At ℓ=3, `3 ≡ 0 (mod 3)` collapses the alphabet to a constant
(`MI 0.40551 → 0`), which would **spuriously VOID the ℓ=3 controls C+/C−**. **Verified.** Fix: draw
relabel exponents `a,b ∈ (ℤ/ℓ)*` per arm; at ℓ=3 the only nontrivial unit is `2`, so use `(2,2)`.

## R2 (POWER — replace symbolic `ΔÎ` with numbers) — measured by INJECTION, not asymptotics

The §4 null-branch wording "independent to resolution `ΔÎ`" gets concrete per-arm floors, obtained by
**injecting a shift-bridge of known strength `s`** (`j := k + C`, `P(C=0)=s`, else uniform) into a
real-marginal sample and measuring the permutation-test detection rate. Report, per ℓ∈{5,7,11,13} at
N=8000: the minimum `s` detected at 80% power by (i) the omnibus `Î` and (ii) the targeted `T` (N1).
This **calibrates the bound on the actual data**, superseding the `(ℓ−1)²/(2N)` asymptotic gloss.

## R3 (REQUIRED NEW CONTROL — pre-registered NOW, before any data)

Because `j = χ_ℓ(U mod n)` and `k = χ_ℓ(U mod p)` are symbols of the **same** `U = |t−1|`, a positive
`Î` has two possible sources: **(a)** the CM reciprocity tie, or **(b)** the elementary congruence
`n ≡ p (mod U)`, which holds for **any** `n = p+1−t`, CM or not. C−r (random base) breaks both at once
and cannot attribute a positive. **New matched control C-cong:**

> For each instance's `U`, draw two **independent** primes `P ≡ Q (mod U)` of the same bit-length
> (both `≡ 1 mod ℓ`), and compute `Î` / `T` on `χ_ℓ(U mod Q)` vs `χ_ℓ(U mod P)`.
> **`Î` persists ⇒** the signal is the shared-`U` congruence, NOT the CM tie (deflates the finding to
> elementary). **`Î` vanishes ⇒** the CM tie is doing work beyond the congruence.

This is the ℓ≥5 analogue of the ℓ=3 mechanism-isolation control (`RESULT_bridge_mechanism_and_constant_v1`
M1). Also record `#{U a perfect ℓ-th power}` (expected ~0 at ℓ≥5) to bound the forcing channel
explicitly. **Choosing this after seeing a positive would be the exact ordering violation this gate
prevents — hence it is frozen here.**

## N1 (CO-PRIMARY — aim at the predicted symmetry)

The predicted alternative (if any ℓ≥5 bridge exists) is a **shift** `j = k + c` (as the cubic bridge
B1 is `j = k + c₃`), which lives on **ℓ** cells (df ℓ−1), not ℓ². Targeting it recovers `~1/√(ℓ−1)`
effect-size sensitivity (≈3.5× at ℓ=13). **Choice-free targeted statistic** (verified):

> `T := max_{b ∈ (ℤ/ℓ)*} χ²_dev( j − b·k mod ℓ  from uniform )`, permutation-nulled the same way.

`T` is invariant under `(j,k)→(aj,ck)` because relabeling permutes which `b` attains the max — so it is
genuinely choice-free, and the `max` over the ℓ−1 alignments is **auto-corrected** by the permutation
null (the null recomputes the same max). `Î` (omnibus) stays as the catch-all for non-shift dependence.

## N4 (scope tightening on a null)

Add to §4's null branch: a **marginal** `I(j;k)`-null does **not** exclude a **conditional** dependence
`I(j;k | t,v,U) > 0` — the cubic correction `c₃` is itself a function of ideal data `(t,v)`, so an ℓ≥5
bridge could be purely conditional and invisible to marginal MI. A null is scoped to marginal
rational-exponent independence.

## N5 (scope declaration)

**Twist-sampling rule, frozen:** one uniformly-chosen prime-order twist per `p` (independent draws
across `p`), matching the audited-clean design of `AUDIT_bridge_laws_independent_retest_v1`. Not all
twists per `p` (correlated draws inflated a deficit there).

## Unchanged from v1

§1 (statistic + choice-freeness, M0 with the R1 fix), §2 controls (+ C-cong from R3), §3 arms, §5
falsification, §6 reach limit (secp's `149,631` out of MI range), §7 prior-art/scope (exploration, not
a novelty claim; Lemmermeyer Ch. 7 = the general power-reciprocity law, classical).
