# ANALYSIS — the "public Eisenstein gate → χ₃ GLV readout → d mod 3" pipeline is circular at its load-bearing step

**Grade:** `[EMPIRICAL — SCOPED, control fires]` for the readout test; `[ANALYTIC]` for the circularity location.
**Date:** 2026-08-13. **Script:** `glv_public_gate_circularity_test_v1.py` (exact int; permutation p integer-based).

The pipeline sets its own pass condition (its opening): *"If evaluating [the invariant] requires the
original scalar branch, the construction is circular … then test whether that equivalence determines
the global branch independently."* It fails both halves. This is **not** a closure of the GLV/CM avenue —
it is an audit of one specific recovery chain against the criterion it declared.

---

## 1. What is actually TRUE in the argument (verified, kept separate from the claim)

- **GLV endomorphism** `φ(P)=(βx,y)=λ·P`: verified on secp256k1 (`β³≡1 mod p`, `λ³≡1 mod n`).
- **χ₃ equivariance** `χ₃(βx)=ω·χ₃(x)`: verified — the χ₃-index shifts by a fixed nonzero amount under
  `d↦λd`. So `F(P)=χ₃(x)·y` **does** read the *position within the GLV orbit* `{d,λd,λ²d}`. Real structure.
- `p≡1 mod 3`, CM by `Z[ω]` (j=0), and the amicable `p↔n` relation are genuine recorded facts.

The kernel "χ₃ reads the GLV orbit label" is correct. It is also the **known** GLV structure that buys a
constant-factor Pollard-rho speedup — not a DLP lever.

## 2. The load-bearing step contains the secret (analytic circularity)

Step 3 as written:  `d ≡ d₀·(−1)^j − ⌊d₀ λ^j / n⌋ (mod 3)`.

`d₀` is the discrete log of the orbit's canonical representative — an **unknown scalar**, as hard as the
target. The public readout supplies only `j` (position in the orbit); the relation it establishes is
`d = λ^j·d₀ (mod n)` — a relation **between two unknowns**, not a value of either. Evaluating step 3
requires `d₀`. That is the circularity the opening forbids, sitting in the formula.

The text even concedes the general reason: *"absolute phase rigidity is destroyed, but relative rigidity
survives (the ratio α₂/α₁ = ζ₃)."* Relative/ratio rigidity is by definition a relation between
representations that is **invariant to the global branch** — so it cannot, per the second half of the
criterion, "determine the global branch independently."

## 3. Empirical confirmation — the public channel carries ~0 bits about d (control fires)

Object: the public statistic `j(P)=χ₃-index of x`. Question: does it predict the secret `d mod 3`?

| quantity | value |
|---|---|
| samples (full group, uniform d) | M = 12000, exact scalar mult |
| 3×3 contingency χ² (j vs d mod 3) | **4.27** (4 dof; 9.49 = p.05) |
| **matched permutation control** | **746/2000** shuffles ≥ observed → **exact p = 0.373** |
| control liveness (max shuffle χ²) | 22.43 (statistic *can* move — instrument alive) |
| best-guess accuracy of d mod 3 from j | 0.340 vs base rate 0.335 → **+0.5% = noise** |

`λ ≡ 2 mod 3`, so an orbit's residues are `{d, 2d, d}` and the index `j` (position) is independent of the
base `d mod 3`: knowing your slot in an orbit whose origin you don't know tells you nothing. Confirmed.

> **SCOPED NULL.** **Object:** the public readout `j=χ₃(x)` of `[d]G`. **Class of observable:** its
> mutual information with `d mod 3` (single-point, whole-group). **Power:** the class-permutation control
> fires to χ²≈22; observed sits at p=0.37. **Scope:** secp256k1, full group, uniform d, M=12000, χ₃ only.
> A single public per-point readout does not recover `d mod 3`.

## 4. The other two steps, same wall

- **"Public gate ε=0 for 68% of points"** (Eisenstein lift-norm inradius `s<3/16`): whatever `ε` is, it is
  a function of the **public** `x` alone. A public function of `P` is redundant with `P`; it cannot carry
  information about `d` beyond "d up to the DLP." Reproducing the geometry does not open a scalar channel.
  (The Eisenstein map "`eis(x)`" is also underspecified here; not needed for the verdict.)
- **"Semaev S₄ sieve + Babai on the GLV lattice → O(1)."** Babai/GLV lattice reduction *decomposes a
  KNOWN scalar* `d=d₁+d₂λ`; it does not recover an unknown one. Semaev point decomposition over `F_p` at
  256 bits is the actual hard problem, not O(1). The hand-off hides the DLP inside "resolve in O(1)."

## 4b. Banked term (ledger) — the √6 automorphism factor

The pipeline's mechanism yields nothing, but the μ₆ structure it sits on carries the **known** GLV
automorphism speedup. Banked with correct provenance:

- **Term:** `−1.29 bits` (√6 ≈ 2.45×) on Pollard-rho, from the order-6 point automorphism group
  `{±1}×{1,φ,φ²}` (orbits `{±d,±λd,±λ²d}`, `6 | n−1`). **Provenance: BASELINE** — this is already inside
  the public ~128-bit estimate (Gallant–Lambert–Vanstone / Wiener–Zuccherato). Not a reduction *we* found.
- **Composition — OPEN, not bounded.** For *independent elliptic-curve automorphisms* the factors combine
  as `√(product)` (a further order-`k` action ⇒ `√(6k)`), and the EC automorphism group is small (order 6
  here). **But that √-composition-with-bounded-Aut is exactly the textbook secure-curve accounting this
  project suspends** (CLAUDE.md counter-prior). We do **not** assume future structure-specific reductions
  obey it: a transfer / isogeny-or-CM subgroup drop / index-calculus route (e.g. on the amicable `p↔n` or
  the A_new tower) may not leave a residual rho for √6 to "attach" to at all, and its composition law is
  unknown. **The amplification potential of the banked √6 is therefore OPEN; the hunt is NOT narrowed to
  "exponent-movers only."**
  *(A prior draft of this bullet imported the rho/automorphism composition law and issued a hunt-narrowing
  verdict — a one-way suppression per `feedback_suppression_bias_asymmetric_2026_08_02`; retracted here.)*
- **No-double-count caveat (binding):** the √6, the χ₃ orbit label (§1), the μ₃-phase edge, and the
  amicable-CM bridge are candidates to be the **same group action re-expressed**. Per
  `feedback_anomaly_drill_protocol` (≥2 zeros ⇒ find the ONE group action; excess over Aut names a 2nd
  object), a new factor may be multiplied into the ledger **only if** it is a genuinely independent action
  or independent information about `d`. If a μ₃-phase finding is the μ₆ in other coordinates, it is already
  banked here and must not be counted twice.

## 5. What this does and does not settle

- **Settles:** this exact chain is circular (§2), and its one public, non-circular ingredient (χ₃ orbit
  readout) is information-empty about `d mod 3` at whole-group scale (§3).
- **Does NOT settle (per project counter-prior):** the GLV/CM/amicable avenue at large. The μ₃ *phase*
  moments, the c-axis, short-interval (incomplete-sum) regimes at 2¹²⁸, and finer lattice-position
  features remain untested here and are not touched by this null. Consistent with
  `RESULT_glv_norm_readout_matched_null_v1.md` (scoped null, whole-group) and
  `RESULT_mu3_glv_frequency_support_v1.md` (μ₃ co-occurrence scoped null).
