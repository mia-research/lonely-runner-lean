# PREREG — Is the 120° law EXACT? (`deg gcd(L*(T), L*(ζ₃T)) = 2`)

*2026-07-26. **Written before any `L*` is computed.** Arms HELD pending `experiment-designer`
sign-off (CLAUDE.md §2, mandatory). No leakage or ECDLP claim; this is pure curve arithmetic.*

---

## 0. What is being tested, and what it would buy

`RESULT_n1_v_sign_mechanism_v1.md` established, **numerically**, that the two Frobenius half-angles of
`H¹_c(E, L_{χ₂(y)} ⊗ L_{χ_a})` differ by 120° (357/357 classes, max deviation `9.5×10⁻⁴⁰`).
Equivalently: **`α₂/α₁` is a primitive cube root of unity.**

`ANALYSIS_n1_cap_anew_channel_kronecker_route_v1.md` argues that IF that ratio is exactly a root of
unity, the open cap `S_y ≤ 2` follows, via: purity (all embeddings) ⇒ every pairwise ratio has
modulus 1 everywhere ⇒ if the ratio is a **unit**, Kronecker forces it to be a root of unity ⇒ the
trace is `2i√p·sin(θ+60°)` because `|1+ζ₃| = 1`.

**This prereg tests only the premise, exactly.** It does not test the cap and does not test
Stickelberger.

> **PRIMARY: `g(p,a) := deg gcd( L*(T), L*(ζ₃·T) )` computed exactly over `ℚ(ζ_n, ζ₃)`.
> Pre-committed prediction: `g = 2` at every cell.**

`g = 2` at a cell is an **exact proof** that two of the four eigenvalues differ by exactly `ζ₃` at
that cell — upgrading the 120° law there from `[VERIFIED — numeric, 9.5e−40]` to `[PROVED — exact]`.

---

## 1. ⚠ Assumption audit — run BEFORE the design, results folded in

| # | assumption | status | consequence |
|---|---|---|---|
| A1 | `H¹_c(E, L_{χ₂(y)}) = H¹(A_new)`, dim 4 | derived: `H¹(C) = H¹(E) ⊕ H¹(E,L_{χ₂(y)})`, `6=2+4`; record's own `F^{I_x}=0` at all 4 punctures gives `H¹_c = H¹` | framing only; not load-bearing for the statistic |
| A2 | `V(a) = −tr(Frob | H¹_c)` | Lefschetz; `H⁰_c=H²_c=0` for a nontrivial sheaf; the 3 two-torsion points contribute `χ₂(0)=0` and `O` is excluded | sign convention only |
| A3 | **purity holds at EVERY embedding**, not just the complex one | `[PROVED — CITED]` (Deligne Weil II 3.2.3(2); KS Prop 2). ⚠ **every numerical verification on file checks ONE archimedean place.** The all-places statement rests entirely on the citation | **load-bearing for Kronecker.** Not tested here; flagged |
| A4 | the splitting field is CM (so `αᾱ = p` algebraically) | `ℚ(ζ_n, ζ₃)` is abelian hence CM ✓ | needed for `α·(−ᾱ) = −p` |
| A5 | `α_i` are algebraic integers | `L*` is monic of degree 4 with coefficients in `ℤ[ζ_n]` ✓ | needed for Kronecker |
| A6 | **`e₃ = −p·e₁` and `e₄ = p²` are FORCED by closure+purity alone** | **verified by derivation and numerically this session** (`e₃ = p²Σ1/rᵢ = −p·e₁`; `e₄ = (−p)(−p)`) | ⇒ **they carry ZERO information and MUST NOT be counted as evidence.** They are instrument checks only |
| A7 | ⚠ **the 120° law's existing evidence is NUMERICAL, not exact** | `9.5e−40` is high-precision, not exact. This folder's `CLAUDE.md` OVERRIDE: *"Every result produced before this rule is PROVISIONAL until it is recomputed exactly."* | **this is the reason for this experiment**, and the reason no float may enter the statistic |
| A8 | `L_{χ_a}` is totally unramified ⇒ `dim H¹_c` stays 4 under the twist | record's own weight-1 proof | needed for the degree-4 model |

**A6 is the design's foundation:** because `e₃, e₄` are forced, the free parameters are exactly the
two angles `(θ₁, θ₂)`, so the 120° law is a genuine one-constraint reduction and a test for it can
discriminate. Confirmed by construction in §4 (PLANT-B).

---

## 2. Instrument

**No floating point anywhere in the signal path** (folder OVERRIDE). All arithmetic in `ℤ`, `ℤ[ζ_n]`,
`ℚ(ζ_n, ζ₃)`.

1. **`e₁`:** `V₁(a) = Σ_{P∈E(F_p)} χ₂(y_P)·ζ_n^{a·d(P)}` — exact element of `ℤ[ζ_n]`, cost `O(p)` after
   one `O(p)` group enumeration. (This is the record's own cheap instrument from the 193-prime sweep.)
2. **`e₂`:** from `V₂(a) = Σ_{P∈E(F_{p²})} χ₂(y_P)·ζ_n^{a·N(P)}` — cost `O(p²)`, exact. Then Newton:
   `P₂ = e₁² − 2e₂`. **This is the record's own `O(p²)` route** (`AUDIT_prereg_n1_v_sign_sweep_v2_v1.md`),
   replacing the `O(p⁴)` eigenvalue solve that caps the record at `p ≤ 43`.
3. **`e₃ := −p·e₁`, `e₄ := p²`** — used as *definitions* (forced, A6), and **independently verified**
   at the primes where the `O(p⁴)` route is affordable (see C-FORCED).
4. `L*(T) = T⁴ − e₁T³ + e₂T² − e₃T + e₄ ∈ ℤ[ζ_n][T]`.
5. **`g(p,a) = deg gcd(L*(T), L*(ζ₃T))` in `ℚ(ζ_n, ζ₃)[T]`** — a GCD of two quartics. **No
   factorization, no splitting field, no ideal arithmetic**, so the degree-`2(n−1)` base field is not
   a cost problem.

**Why this statistic and not the ideal test:** the ideal formulation of
`ANALYSIS_..._kronecker_route_v1.md §7` requires arithmetic in the splitting field of a quartic over
`ℚ(ζ_n)` — degree up to `4(n−1)`, infeasible past tiny `p`. **`g` is label-free, Galois-safe, exact,
and cheap**, and it tests the same statement. *(If `g = 2`, the ratio is exactly `ζ₃`, hence a unit,
hence the ideal equality of that route follows — it does not need to be computed separately.)*

---

## 3. Sample — frozen before any `L*` is computed

**Selection rule (deterministic, reproducible):** primes `p` with `p ≡ 7 mod 12` (secp's own class),
`#E(F_p) = n` prime, taken in increasing order.

- **STRATUM S (primary), `p ≡ 7 mod 12`:** the first **10** such primes with `p > 547`.
  *(`p > 547` makes the whole stratum OUT-OF-SAMPLE: the 120° law was measured at
  `p ∈ {13,43,127,163,211,349,397,433,547}` — all `≤ 547`. Those nine are **IN-SAMPLE** and are
  reported separately, never pooled.)*
- **STRATUM C (cross-stratum control), `p ≡ 1 mod 12`:** the first **5** such primes with `n` prime,
  `p > 547`. The record's `e₂` dictionary is **stratum-dependent and inverts** (F2), so this stratum
  is a genuine second condition, not a replicate.
- **IN-SAMPLE set I:** the nine primes above, reported in their own row.

**Cells:** all `(n−1)/6` **μ₆ classes** per prime — never raw `a`. A class is one orbit of
`a ↦ aλ`, `a ↦ −a`. **Every count in the report names μ₆ classes and primes separately.** (The
record's own repeated defect: reading `30/30` where the truth is `5/5`.)

**Freeze:** the prime list, the class-representative rule, and the cell count per prime are written to
`n1_120deg_FREEZE_v1.json` and **SHA-256'd before the first `V₁` call.** The hash goes in the RESULT.

**Budget / ABSTAIN:** `O(p²)` per cell for `V₂`. If the frozen stratum cannot be completed within the
declared wall-clock, **report the completed primes and ABSTAIN on the rest** — do **not** substitute
easier primes. (The record's B1 blocker: a sweep that dies at prime 8 of 50.)

---

## 4. Controls — every one must fire, and each is declared AS a control

| id | control | must produce |
|---|---|---|
| **PLANT-A** *(planted positive)* | synthetic quartet `{α, ζ₃α, −ᾱ, −ζ̄₃ᾱ}` built from an exact Weil number | **`g = 2`** — the pipeline can see the thing |
| **PLANT-B** *(planted negative — the discrimination control)* | synthetic quartet `{α, β, −ᾱ, −β̄}` with `β` an exact Weil number and `β/α` **not** a cube root of unity. Constructible **because A6 shows `e₃,e₄` are forced and do not constrain the second angle** | **`g = 0`** — a `g=2` reading is not an artifact of closure/purity |
| **PLANT-C** *(degeneracy)* | quartet with a repeated root | **flagged as degenerate**, not silently returning `g ≥ 2` |
| **C-FORCED** | `e₄ = p²` and `e₃ = −p·e₁` checked exactly against the `O(p⁴)` eigenvalues at `p = 13, 43` | agreement. ⚠ **A6: these are FORCED, so agreement is an INSTRUMENT CHECK and is NOT evidence for anything** |
| **C-CROSS** | `e₁` from this pipeline vs the record's independent cheap `V₁(a)` computation | exact agreement at every cell |
| **C-NOFLOAT** | `check_no_float.sh` over the signal-path files | passes before any cell is run |
| **C-DEGEN-CENSUS** | count cells with `V(a) = 0` or repeated roots | reported as a separate row; excluded from the primary with the exclusion count printed |

⚠ **NOT a control, and must not be reported as one:** the prediction that `ζ₃` lies in the splitting
field (`ANALYSIS §6`). It is a **consequence of the hypothesis under test**, so it cannot validate the
instrument. It is a **secondary prediction** and is reported in §6 only.

---

## 5. Pre-committed readings — written before any data

| outcome | pre-committed conclusion |
|---|---|
| `g = 2` at **every** cell of stratum S | the 120° law is **`[PROVED — exact]` at the tested cells**. The Kronecker premise holds there. ⇒ proceed to the Stickelberger step — **and only then**, after re-verifying that citation (three failed runs) |
| `g = 0` at **any** cell of S | **the 120° law is NOT exact.** A `9.5e−40` agreement that is not an identity is itself a major finding, and the Kronecker route is **dead**. Report the failing cell verbatim; do not re-scope the stratum |
| `g = 2` on S but `g = 0` on stratum C | the law is **stratum-specific** (`p ≡ 7 mod 12` only). Re-type; secp's stratum is unaffected but the mechanism cannot be generic `j=0` |
| `g = 4` anywhere | the whole multiset is `ζ₃`-stable — a **stronger** structure than the law; re-type, do not report as confirmation |
| any PLANT fails | **halt.** No cell result is reported. The instrument is broken |
| budget exhausted | ABSTAIN on the remainder with the completed count stated. **Abstention is not a closure** ([[feedback_prereg_abstention_is_the_finding_2026_07_19]]) |

**Falsification condition, stated once:** a single cell of stratum S with `g ≠ 2` refutes exactness.

---

## 6. Secondary (reported, never promoted)

- `ζ₃ ∈` splitting field of `L*` — forced by the hypothesis, so informative only if it **fails**, in
  which case the eigenvalue computation is wrong (not the theory).
- The order of the ratio when `g = 2`: pre-committed to be exactly 3. If some cells give a different
  root-of-unity order, the law is "ratio is a root of unity of varying order" — a different statement.
- `S_y = max|V|/√p` per prime, recomputed exactly, as a consistency check against the record's
  `[VERIFIED, 120 primes]` cap.

---

## 7. Scope, and what this cannot do

- **Scale banner #5.** Every cell is at `p ≈ 10³`. secp is `2²⁵⁶`. `g = 2` at 15 primes says nothing
  directly about secp; it establishes an exact identity at tested cells, which is the input the
  *analytic* route needs — the reach comes from a proof, not from these numbers.
- **This does NOT prove the cap.** It tests the premise. The cap additionally needs A3 (cited, untested
  here) and the order-pinning step (§5 row 1), which Kronecker alone does not supply.
- **This does not test Stickelberger** and inherits none of its unverified citation.
- ⚠ **`e₃, e₄` are forced (A6).** No count involving them may appear in any headline.

---

## 8. Status

**Arms HELD.** Not runnable until `experiment-designer` signs off; deviations to be filed in
`PREREG_n1_120deg_exact_ideal_v1_DEVIATIONS.md` as they occur, not retrospectively.
