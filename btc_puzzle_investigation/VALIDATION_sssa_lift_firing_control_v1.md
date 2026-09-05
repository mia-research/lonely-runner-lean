# VALIDATION (mechanical layer) — SSSA p-adic-lift machinery: control fires, baseline confirms K-entanglement

**Date:** 2026-08-13. **Script:** `sssa_lift_control_v1.py` (exact integer arithmetic mod `p^N`, N=4;
homogeneous Washington projective coords so the E₁ point needs `z=-X/Y`, never a division by `Z`).
**Layer:** mechanical only (per CLAUDE.md §2a: "does the plant fire", exactness) — self-audit + artifact
suffices; this is NOT the leakage test. **No grade on any leakage claim.** Precedes the
`experiment-designer` pre-registration of the actual amicable-consistency test.

Instrument for `PLAN_representation_boundary_program_v1.md` §3/§5 — the `E(𝔽_p) ↔ E(ℚ_p)` formal-group boundary.

---

## 1. Firing control — SSSA recovers `d` on an anomalous curve (`#E = p`)

Curve `y² = x³ + 3x + 8` over `𝔽₄₁`, `#E = 41 = p` (trace 1, anomalous), `G=(4,17)`.
Lift `P,Q=dP` to `ℤ/p⁴`, multiply by `p` to land in `E₁`, read `d ≡ z(pQ̃)/z(pP̃) (mod p)` off the leading
p-adic digit; resolve the trivial `±` by the public check `[v]G == Q`.

**Result: 8/8 exact recoveries, all lift-invariant** (2nd lift `x̃_Q → x̃_Q+p` gives the same `d`).
⇒ the invariant-across-the-boundary determines the global branch when the boundary is clean. **FIRES.**

## 2. Negative baseline — the carry entangles with the lift when `n ≠ p`

Curve `y² = x³ + 7` over `𝔽₁₃` (μ₆ CM, `#E = n = 7 ≠ 13 = p`), `G=(7,5)`, order 7.
Same machinery, multiplier `n`. **Result: recovery is lift-DEPENDENT 8/8** — changing the lift of `Q` by
`p` changes the "recovered" value. This is the mechanical witness of the §3 circularity: `n` is a p-adic
unit, so `ψ([n]K)=n·ψ(K)` does **not** gain valuation, and the free lift term `K` corrupts the leading
digit. The p-adic boundary **alone** does not pin `d` for `n ≠ p`.

## 3. Incidental (noted, not over-read): j=0 degeneracy of SSSA

The first anomalous curve found was `a=0` (`y²=x³+5 / 𝔽₃₇`, j=0 CM). There the attack **degenerated**:
`z([p]G̃)` had valuation 2, i.e. the elliptic-log homomorphism `λ: E(𝔽_p) → 𝔽_p` was the **zero map**
(`recovered = ±d` failed; value was unrelated to `d`). Forcing generic `j` (a≠0) restored `λ ≠ 0` and the
control fired 8/8. **secp256k1 is j=0** — so even the anomalous/clean boundary carries a j=0-specific
degeneracy of the elliptic-log hom. This is an observation about the instrument on CM curves; whether it
bears on the (non-anomalous) target is a separate question, not asserted here.

## 4. What is validated / what is NOT

- **Validated (mechanical):** the lift → `E₁` → elliptic-log-ratio pipeline is correct (control 8/8);
  the `n≠p` failure is lift-entanglement of `K`, reproduced 8/8.
- **NOT tested here:** whether a second representation (the amicable `n`-adic companion) constrains `K`.
  That is the leakage hypothesis and goes through `experiment-designer` pre-registration BEFORE any run,
  with its own matched control, power, scope, and falsification condition.
