# secp256k1 CM — session verified findings (v1, 2026-07-12)

**Scope.** New results from the 2026-07-11/12 verification session. This does
**not** repeat `btc_puzzle_investigation/KNOWN_FACTS_secp256k1_and_keys_v5.1.md`
(curve base object, deployed constants, twist family, GLV=CM ideal, generation
model, attack surface, φ(n)/RH programme) nor `THREADS_v1.md §A`'s single-symbol
result χ(π)=−(28/π)₆⁻¹. It records only what was newly computed or newly
verified here, plus corrections to intermediate session drafts.

**Verification scripts** (self-contained, archived): `verify_session_2026_07_12/`
— `audit.py` (AUDIT 1–4: held-out brute vs closed form, brute amicable closure,
brute three-term ASD, factorization uniqueness), `zeros_verify.py` (L-zeros),
`amicable_sweep_helpers.py` (fast CM point-count). Section references below use
these names.

**Epistemic conventions.**
- **[found]** — a positive statement supported by the stated computation.
- **[consistent]** — data compatible with a value/claim within stated error; not
  a proof of equality.
- **[no-evidence]** — a probe that returned nothing. Read strictly as: *under
  this test, at this range, with these factors, we did not find evidence.* It is
  **not** a disproof or a claim that the thing is ruled out.
- Curve constants (p, n, t, a, b, M) are taken as arithmetic-verified elsewhere.

---

## 1. Explicit LOCAL factorization of the finite Hecke character  [found]

Building on THREADS_v1 §A (χ(π)=−(28/π)₆⁻¹ for primary π, i.e. π≡2 mod 3), the
finite character factors over the conductor f=(84)=(4)(3)(7) as a genuine product
of local characters:

```
χ(π) = ζ₆^{ 3  +  5·(π/π₇)₆  +  1·(π/π̄₇)₆  +  χ₄(π mod 4) }      (ζ₆ = −ω²)
```

- **χ₃** = the constant ζ₆³ = −1 — the mod-(√−3) component, fixed on the primary
  class (all primary π ≡ 2 mod 3 share one image in (Z[ω]/3)^×).
- **χ₇** = (π/π₇)₆⁵·(π/π̄₇)₆¹ — the sextic-at-7 component. The exponents are
  **(5,1)**, asymmetric.
- **χ₄** = a genuine **order-6** character of (Z[ω]/4)^× (12-element group,
  exponent 6, since 2 is inert ⇒ residue field 𝔽₄). Table (π mod 4 → exponent):

  | π mod 4 | (0,1) | (0,3) | (1,0) | (1,1) | (1,2) | (1,3) | (2,1) | (2,3) | (3,0) | (3,1) | (3,2) | (3,3) |
  |---|---|---|---|---|---|---|---|---|---|---|---|---|
  | χ₄ (raw) | 1 | 1 | 3 | 5 | 0 | 2 | 4 | 4 | 3 | 2 | 0 | 5 |

  (the "raw" table folds in the χ₃ constant; subtracting the identity value 3
  gives a homomorphism with χ₄(id)=0, verified 0 violations.)

**Verification [found].**
- Reproduces χ on 494/494 split primes ℓ<8000; every mod-4 class single-valued.
- χ₄ (after removing the constant 3) is a genuine character: 0 homomorphism
  violations over all 12×12 unit pairs; order 6.
- (5,1) is the **unique** exponent pair among all 36 that yields a valid mod-4
  factorization (two independent code paths agree).
- At the secp256k1 Frobenius π_p: χ₃=ζ₆³, χ₇=ζ₆⁴, χ₄=ζ₆⁵ ⇒ product ζ₆¹²=1,
  reproducing χ(π_p)=1 with **no** individually-trivial component.

**Why this matters / what it corrects.** Several intermediate session drafts
claimed the decomposition "fails" (≤4/12 or 11/17 matches) and that χ₄ is a
"quartic character of order 4 on an 8-element group." Those are **[found]**
false: (Z[ω]/4)^× has 12 elements and exponent 6 (no order-4 character exists),
and the factorization does not fail — it needs asymmetric exponents (5,1), not
(5,5). The "sextic contribution is trivial at π_p" statement in those drafts is a
symmetric-exponent artifact: k₁+k₂ = 4+2 = 6 ≡ 0 for this π_p, so any (e,e) gives
0; the true χ₇ part is ζ₆⁴.

---

## 2. Fast exact point-count from the character  [found, reusable tool]

The §1/§A character gives an O(polylog) exact trace, independent of point
counting:

```
a_ℓ = Tr( −(28/π_prim)₆⁻¹ · π_prim ),   ℓ ≡ 1 mod 3 split;   a_ℓ = 0 for ℓ ≡ 2 mod 3.
```

**Held-out validation [found].** On 239 primes in [3001, 5000] — a range used in
no fitting — the closed-form a_ℓ matched brute-force point counts of y²=x³+7 with
**0 mismatches**, and all 116 inert primes gave a_ℓ = 0. This removes the
circularity concern that the formula was merely fit to the same data it was
tested on. (Script: `verify_session_2026_07_12/audit.py`, AUDIT 1.)

---

## 3. BSD / Tamagawa resolution (thread D)  [found]

The record previously carried inconsistent local data (one draft: Kodaira III at
2,3,7 with c=1 — inconsistent, since III forces c=2; another: IV/III/II with
∏c∈{2,6}). Resolved:

- **∏c = 1 and Ш = 1** [found], established *without assuming BSD*: L(E,1) =
  3.04141722842788104243 computed directly from the L-series 2·Σ aₙ/n·e^{−2πn/√N}
  equals the Néron real period ∫dx/√(x³+7) = Γ(1/3)Γ(1/6)/(2√π·7^{1/6}) to full
  precision. With rank 0, torsion 1, Reg 1, BSD (proven for this CM curve, Rubin)
  forces ∏c·Ш = 1.
- **Kodaira II at 2, II at 3, II at 7** [found], each cₚ = 1 — Tate's algorithm,
  and cross-checked against LMFDB 21168.ce2. The naive v(Δ)→type map (v(Δ)=4,3,2)
  is invalid at p=2,3 because of wild ramification; the conductor exponents
  f₂=4, f₃=3, f₇=2 are Type II with wild part, giving N=2⁴3³7².
- Period normalization checked: the two-branch integral over the single real
  component (Δ<0) with ω=dx/(2y) yields ∫dx/√(x³+7); the factor-2 cancels, so no
  hidden ∏c=2.

Independent legs: the numerical period integral and LMFDB neither use the §1/§2
character, so this stands regardless of §1.

---

## 4. Zeros of L(E,s) (thread E)  [found, partially authority-checked]

Computed on the critical line via the exact incomplete-Γ representation
Λ(1+it)=2Re Σ aₙ (cn)^{−(1+it)}Γ(1+it,cn), c=2π/√N, W=+1 (real-valued).

- Sanity [found]: Z(0) ⇒ L(1) = 3.04141722842788 ✓.
- First 8 zeros γ (arith s=1+iγ) matched LMFDB's tabulated zeros to **11–12
  digits**: 0.81731263642, 1.32986126623, 2.40740300794, 3.22030659332,
  3.76693920734, 4.44237636319, 5.28146107033, 5.91353724379.
- 21 distinct zeros found up to γ≈16. **Honest scope:** only the first 8 are
  authority-checked against LMFDB; γ₉…γ₂₁ are self-computed by the same method
  (which the first 8 validate) but not independently confirmed.

(Script: `verify_session_2026_07_12/zeros_verify.py`.)

---

## 5. Amicable 2-cycle closure density (thread B)  [consistent + no-evidence]

The closure ℓ → #E(𝔽_ℓ) → ℓ, restricted to genuine 2-cycles (ℓ ≠ n), with n
prime and coprime to 84:

- Fully brute-force point counts: **0.2794 ± 0.0222** at X=80000; 0.306 ± 0.035
  at X=25000.
- CM-accelerated (§2 a_ℓ): 0.2657 ± 0.008 at X=10⁶.
- The two agree within 0.6σ (so §2 is not biasing the estimate) and both sit
  within ~0.9σ of 13/50 = 0.26.

**Positive [found].** Trace-1 **fixed points** (ℓ = n, i.e. anomalous primes,
a_ℓ = 1) are a **distinct population** from ℓ≠n amicable pairs — 8 at X=25k, 11 at
X=80k. Lumping them in shifts the rate up (~0.31). They must be counted
separately. Two reproducibility gotchas recorded: the Z[ω] Euclidean gcd needs
exact-integer rounding (float breaks above ~10⁵), and the partner n∉{2,3,7} must
be guarded (n=7 makes (28/·)₆ undefined).

**[no-evidence].** Under these two independent sweeps (brute to X=80k;
CM-accelerated to X=10⁶), we **did not find evidence distinguishing** the closure
density from 13/50 — but neither did we find evidence pinning it *to* 13/50
against nearby values (e.g. ~0.28). Separately, the exact-rational claim 13/50
rests on a mod-84 class census (26/100) from prior work (P2) that we **did not
reproduce** this session; that census remains unaudited here. No claim that
13/50 is proven, and no claim that it is wrong.

---

## 6. Supercongruences (thread C)  [found + no-evidence]

- **[found].** The three-term ASD congruence b_{ℓ²} − a_ℓ·b_ℓ + ℓ ≡ 0 (mod ℓ²),
  with b_m = 7^{(m−1)/6}·C((m−1)/2,(m−1)/6), reproduced using **brute-force a_ℓ**
  (independent of §2) at all tested split primes; the mod-ℓ³ upgrades occurred at
  exactly ℓ ∈ {37, 61} in range. (Script: `verify_session_2026_07_12/audit.py`, AUDIT 3.)
- **[no-evidence].** A closed form for the mod-ℓ² correction δ_ℓ was not found:
  under an exhaustive small-coefficient search in the Fermat quotients q_ℓ(2),
  q_ℓ(3), q_ℓ(7) over the tested primes, no small rational combination matched.
  This is not evidence that no closed form exists — the prior work notes it likely
  carries Bernoulli/Euler-number content (Lehmer-type), which that search space
  excludes.
- **[no-evidence].** For the mod-p² unit-root supercongruence via p-adic Γ /
  Gross–Koblitz: at a single prime (p=13), a permutation-and-sign search over Γ
  arguments produced many matching formulas — i.e. the single-prime test is
  underdetermined and does **not** identify a formula. Morita's Γ_p was verified
  only at **integer** arguments (e.g. 12! ≡ −1 mod 169 ✓); fractional arguments
  a/(p−1) were not implemented. No distinguishing formula found under these
  conditions.

---

## 7. Corrections to intermediate session drafts  [found]

For the record, the following claims that appeared in intermediate drafts are
[found] incorrect, with the verified fact:

| Draft claim | Verified fact |
|---|---|
| (Z[ω]/4)^× has 8 elements | 12 elements, exponent 6 |
| χ₄ is a "quartic character of order 4" | χ₄ is order 6; no order-4 character exists on that group |
| χ = χ₄·χ₃·χ₇ "fails" / ≤4–11/17 matches | Factors cleanly with exponents (5,1); 494/494 primes |
| "sextic contribution trivial at π_p" | Symmetric-(e,e) artifact; true χ₇ part is ζ₆⁴ |
| Kodaira III at 2,3,7 / IV,III,II; ∏c∈{2,6} | Kodaira II/II/II; ∏c=1 (LMFDB-confirmed) |
| primes 61, 109, 181 "no primary element" | Code bug; primary gens (−4,−9),(5,12),(−4,−15) exist |
| χ(π_p)=1 shown via floating-point trace | True exactly (2a−b=t in integers); the float value was off by ~1.1×10²¹ |

---

## 8. Session epistemic ledger

- **[found] (verified this session):** local Hecke factorization with (5,1) and
  order-6 χ₄ (§1); fast exact point-count validated on 239 held-out primes (§2);
  ∏c=1, Ш=1, Kodaira II/II/II, L(1)=Ω via two independent legs (§3); first 8
  L-zeros to 11–12 digits vs LMFDB (§4); three-term ASD via brute a_ℓ, upgrades
  {37,61} (§6).
- **[consistent]:** amicable 2-cycle density ≈0.27, compatible with 13/50 (§5).
- **[no-evidence] (probes that returned nothing under stated conditions):**
  distinguishing the amicable density from 13/50 either way (§5); the 26/100
  census reproduction (§5, not attempted); a small-coefficient Fermat-quotient
  closed form for δ_ℓ (§6); a single-prime-determined mod-p² supercongruence
  formula (§6).
- **Assumptions still resting (named, not eliminated):** BSD proven for this CM
  curve (Rubin) and analytic Ш=1 (LMFDB) underlie §3's ∏c conclusion; the
  sextic-symbol convention (ζ₆=−ω², fixed primitive root) underlies §1 (but §2's
  held-out brute test is convention-proof).
