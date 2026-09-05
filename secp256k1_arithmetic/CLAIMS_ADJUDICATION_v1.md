# Adjudication of the pasted results table (2026-07-11)

Tested by `test_claims_v1.py` (T1–T8) and `rho_b_investigate_v1.py`. Exact
arithmetic decides every row; the two L(1)/Ω rows are settled by a from-scratch
recomputation (exact Hecke eigenvalues to n ≤ 4000). Verdicts below; **two rows
are wrong**, both instructively.

## Results table

| # | Claim | Verdict | What the test showed |
|---|---|---|---|
| 1 | Frobenius (a, b) in ℤ[ω] | **✓ confirmed** | `N(a+bω)=p`, `2a−b=t`, `N(a−1+bω)=n` all exact (T1). |
| 2 | "π_n = 1−π_p; amicability automatic when n prime" | **✗ half wrong** | `π_n = π_p − 1` (associate of `1−π_p`) is a **theorem** ✓. "Automatic when n prime" is a **j≠0 theorem misapplied to our j=0 curve** — REFUTED by brute force: of 22 split ℓ<1500 with `#E₇(𝔽_ℓ)` prime, only 10 close; 12 fail (e.g. ℓ=43→31→**21**≠43; 97→79→67; 211→199→189). Closure is the mod-84 class condition, prob **13/50**, not 1 (T2). |
| 3 | Formal-group p-adic integrality (20 primes) | **✓ strengthened** | Not 20 spot primes but **all primes at once**: `[2](T), [3](T), [5](T) ∈ ℤ[[T]]` to `T³⁷` via the multiplication series (T3). This is the actual integrality statement (formal group defined over ℤ). |
| 4 | Unit root α ≡ t (mod p), Hensel-lifted to p² | **✓ confirmed** | `α=t` roots `x²−tx+p` mod p; `α = t − p·t⁻¹` roots it mod p²; `v_p(β)=1` for the other root (T4). |
| 5 | Sextic-unit distribution uniform (Chebotarev) | **✓ confirmed exactly** | Class census: **exactly 72 of 432 classes per unit** (perfect uniformity); empirical 3000 split primes χ²=3.26 (df 5, p≈0.66). "~16.5% original twist prime" = 1/6 marginal ✓ (T5). |
| 6 | Analytic conductor A(ψ) ≈ 536.19 | **✓ confirmed** | `N/(4π²) = 21168/(4π²) = 536.1917` (T6). This is the standard analytic conductor `N/(2π)²` for a weight-2 / degree-2 motive. |
| 7 | Real period Ω ≈ 6.082834440384 | **✗ normalization** | The BSD/Néron real period is **Ω = 3.0414172284** (= `Γ(1/3)Γ(1/6)/(2√π·7^{1/6})`, verified to 12 digits). The pasted 6.0828 = **2Ω** = `∫_{E(ℝ)}|dx/y|` (uses `dx/y`, not the Néron differential `dx/2y`). It is a real quantity but not the BSD period, and it is inconsistent with row-8's "L matched Ω" (see below). |
| 8 | Local values \|χ(𝔭)\|² = N𝔭 = ℓ | **✓ but mislabeled** | True for **ψ** (∞-type (1,0) ⇒ \|ψ(𝔭)\|²=N𝔭), verified (T8). For the **finite** character χ, \|χ\|=1 (χ is a root of unity). The claim holds if 𝔭 means the Grössencharacter ψ. |

## Q&A table

| Q | Verdict | Correction |
|---|---|---|
| 1. Why 977? | **✓ (amicability clause struck)** | 977 = first prime descending from `2²⁵⁶−2³²−1024` (Solinas), which happens to carry a prime-order j=0 curve (~3% bonus). Correct. But "amicable pair is automatic CM consequence" as the *reason for 977* is a **non-sequitur** — amicability is downstream of n prime, not a cause of the field choice; and it isn't automatic for j=0 anyway (row 2). |
| 2. Supercongruences → p-adic L? | **✓** | Local Honda structure holds (our T3 integrality + the three-term ASD mod ℓ²); global interpolation obstructed (arXiv:2605.17645). Consistent with our record. |
| 3. Sextic distribution? | **✓** | Uniform by Chebotarev — we now have it **exactly** (72/432 per unit), not just empirically. |
| 4. Hecke explicit formula? | **✓** | A(ψ)=536.19 ✓, W=+1 ✓, and stronger than "local formula with sextic symbols": the whole finite character is the **single symbol χ(π)=−(28/π)₆⁻¹** (our v2 finding). |
| — | "Ω and L(E,1) matched to LMFDB to 20+ digits" | **partly** | L(E,1)=Ω=3.0414172284 matched to LMFDB/closed form to 12 digits here (float limit); "20+ digits" needs mpmath, not run. The Ω that matches L(1) is **3.0414**, not the pasted 6.0828 — so the table is internally inconsistent on this pair. |

## The BSD resolution (this closes thread D — no tension)

From-scratch `L(E,1) = 3.041417228428` (exact `a_n`, approximate functional
equation, T7) equals **Ω = 3.041417228428** to 9 digits: `L(1)/Ω = 1.000000000`.

`y² = x³ + 7` is a **global minimal model** (`Δ = −2⁴·3³·7²`, all `v_ℓ(Δ) < 12`),
so `dx/2y` is the Néron differential and Ω = 3.0414 **is** the BSD real period.
BSD for analytic rank 0 is a **theorem** here (CM curve, Rubin/Kolyvagin), giving

```
L(1)/Ω = (∏_ℓ c_ℓ · #Ш) / #E(ℚ)_tors²  = 1   ⇒   every c_ℓ = 1  and  #Ш = 1
```

(torsion trivial). So **all Tamagawa numbers are 1 and Ш is trivial** — my
earlier thread-D worry (guessed Kodaira IV/III/II ⇒ ∏c ∈ {2,6}) was based on
reading types off `(v(c₄),v(c₆),v(Δ))` without Tate/Ogg; the correct types (with
the wild parts at 2, 3) are all **Type II with c = 1**. The record `L(1)=Ω` is
right; there was never a tension. The pasted "Ω ≈ 6.0828" would have created a
fake `L(1)/Ω = 1/2`.

## Cross-check that lands (the investigation continues): per-b closure ρ_b

`rho_b_investigate_v1.py`. The single-symbol formula generalizes to
`u_b(π) = −(4b/π)₆⁻¹` (verified 0 mismatches vs point counts, b=2,3,5,7, all
split primes < 3000). The mod-84 closure census gives exact per-b constants:

```
ρ_2 = 1/2,   ρ_7 = 13/50,   ρ_3 = 18/101,   ρ_5 = 1/10      (b=1: degenerate, 2-torsion, 0)
```

**Falsifiable prediction, passed 4/4:** ρ_b must order the amicable-pair
abundance. Direct exact recount to a common X = 20000:

```
b:        2      7      3      5
ρ_b:    0.500  0.260  0.178  0.100     (class census)
#pairs:   34     21     15     11       (direct point-count enumeration)
```

Ordering matches exactly (`b2 > b7 > b3 > b5`); consistent with the relayed
round-37 counts (24, 14, 19 for b=2,3,7). The magnitudes are not proportional
because the total density also carries a b-dependent Hardy–Littlewood twin-norm
constant `C_HL(b)`; ρ_b is the local-alignment factor that fixes the **ordering**.
This is exactly the object Silverman–Stange (arXiv:0912.1831) set up for j=0:
their conjectural constant is a Grössencharacter-value analysis at prime ideals
𝔭 with `#E(𝔽_𝔭)` prime — our ρ_b is a computed instance.

**Next (source-first):** read S–S §on j=0 (the paper states a conjectural
density constant for y²=x³+b); compare their constant to our ρ_b·C_HL(b). This
is the one row that could be a genuine contribution vs a reconstruction — it
must be adjudicated against their explicit formula, not asserted.
