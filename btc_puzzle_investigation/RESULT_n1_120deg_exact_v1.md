# RESULT — the 120° law is EXACT: `g = deg gcd(L*(T), L*(ζ₃T)) = 2` at every tested cell

*2026-07-27. Executes `PREREG_n1_120deg_exact_ideal_v4.md` (gate-signed-off) under the folder no-float
OVERRIDE. No leakage or ECDLP claim; pure curve arithmetic. Grades: `[PROVED-exact]` = an exact
integer/modular identity at the stated cells; `[CONFIRMED-independent]` = agreed by a second
implementation.*

---

## 1. Headline

> **`[PROVED-exact]` The 120° law `α₂/α₁ = ζ₃` — i.e. two of the four Frobenius eigenvalues of
> `H¹_c(E, L_{χ₂(y)} ⊗ L_{χ_a})` differ by exactly a primitive cube root of unity — holds at EVERY
> census-surviving cell of ALL 22 tested primes:** 7 in-sample + **10 out-of-sample stratum-S
> (`p≡7 mod12`, secp's class)** + 5 cross-stratum C (`p≡1 mod12`). This upgrades the law from
> `[VERIFIED-numeric, 9.5×10⁻⁴⁰]` to an **exact identity** at those cells.

The statistic is `g(p,a) = deg gcd(L*(T), L*(ζ₃T))`, computed **multi-modularly with no floating
point** (deviation D2); `g = 2 ⟺ ζ₃ ratio` among census survivors (gate-verified exhaustively).

---

## 2. Frozen sample and integrity

- **Freeze:** `n1_120deg_FREEZE_v1.json`, **SHA-256 `a964f246b87fbe302b4740c3123a40a25ff0376b60cc45f8c3ef14d3c23c9fdf`**, written by point-counting only, **before the first `V₁`**.
- **Selection rule:** `p≡7 mod12`, `#E(F_p)=n` prime, increasing; STRATUM S = first 10 with `p>547`
  (out-of-sample); STRATUM C = first 5 primes `p≡1 mod12`, `p>547`; IN-SAMPLE I = the `p≡7`, `≤547`
  primes (deviation D1 corrected the prereg's mis-quoted in-sample list; OOS integrity intact).
- **Cells:** the `(n−1)/6` μ₆-cosets per prime — never raw `a`.

---

## 3. Controls — all fired

| control | result |
|---|---|
| PLANT-A / PLANT-Z (planted positives) | `g=2` ✓ |
| PLANT-B / PLANT-U1 (planted negatives) | `g=0` ✓ — statistic is not vacuous |
| C-NOFLOAT (`check_no_float.py`, AST) | pass on all signal-path files ✓ |
| C-COEFF (independent Sage `O(p⁴)` route) | all four eigenvalues weight-1, `|α|=√p` to `2.2e-16` — validates the `e₂` sign `[CONFIRMED-independent]` |
| C2 (Newton/root recovery, Sage) | planted tuple recovered to `4.4e-16` ✓ |
| forced-relation sign (`verify_e3_sign.sage`, true `V₁..V₄`) | `e₄/p²=1`; `e₃/(p·e₁)=+1` at p=13, `−1` at p=43 `[CONFIRMED-independent]` (see D4) |

---

## 4. The result

| stratum | primes | cells (Σ (n−1)/6) | verdict |
|---|---|---|---|
| IN-SAMPLE I (`p≡7 mod12`, `≤547`) | 43,67,79,127,163,211,547 | 197 | **7/7 primes ALL `g=2`** |
| **STRATUM S (`p≡7 mod12`, `>547`) — PRIMARY, OOS** | 823,907,967,991,1051,1303,1831,2143,2251,2503 | **2464** | **10/10 primes ALL `g=2`** |
| STRATUM C (`p≡1 mod12`, `>547`) | 577,733,1237,1249,1669 | 924 | **5/5 primes ALL `g=2`** |

**No census exclusions** (`V(a)=0`: 0), **no repeated roots** (0), **no cell with `g≠2`** anywhere.
Longest prime `p=2503` completed in 55 s, well inside the 900 s/prime frozen budget. Raw:
`RESULT_n1_120deg_exact_v1.json`, log `run_n1_120deg_v1_fixed.log`.

**Pre-committed reading (§5 row 1) triggered:** the Kronecker premise `α₂/α₁ ∈ μ` holds, exactly, at
every tested cell of secp's stratum.

---

## 5. A false null caught mid-run, and the corrected structural finding

The **first** sweep reported stratum C `g=0` at every cell (which would have fired the "law is
stratum-specific" reading). **It was a bug, not a null** (deviation D4): the forced relation
`e₃ = −p·e₁` (prereg A6) holds only for `p≡3 mod4`; for `p≡1 mod4` the pairing closure is `α↦ᾱ`
(because `χ₂(−1)=+1`, `V(a)` real) and `e₃ = +p·e₁`. The independent Sage route exposed it — at p=13 the
eigenvalue phases are exactly 120° apart, so `g` is 2 there. After fixing to **`e₃ = χ₂(−1)·p·e₁`**
(`e₄=p²` universal), both strata give `g=2`, and the Sage `V₁..V₄` route confirms the sign
independently.

> **Corrected finding:** the 120° law is **not** stratum-specific — it holds in **both** `p mod 12`
> strata; only the pairing sign `e₃ = χ₂(−1)·p·e₁` differs by `p mod 4`. **This amends prereg A6**
> (which stated `e₃=−p·e₁` unconditionally). Discrimination is intact: PLANT-B still returns `g=0`,
> and the first-pass wrong-sign returned `g=0` on real stratum-C data — the statistic is not forced.

---

## 6. Scope — what this establishes and what it does NOT

**Establishes:** the **premise** of the Kronecker route (`α₂/α₁` is exactly `ζ₃`) as an exact identity
at 22 primes × their cells; the `e₂` sign and the `p mod 4` forced-`e₃` sign, independently confirmed.

**Does NOT establish (unchanged from `ANALYSIS_..._kronecker_route_v2.md §8`):**
- **The cap `|V|≤2√p`.** This proves only the premise. The cap additionally needs A3 (purity at every
  embedding — cited, untested here), the order-pinning step incl. determining `μ(L)` (`[REV e.3]`), and
  **uniformity in `(a,p)`** (`[REV e.5]`).
- **Uniformity.** This is per-cell at 22 primes; **no finite sweep gives all `a`, all `p`.**
- **Stickelberger.** Not tested; its citation remains unverified (three failed runs).
- **secp scale (banner #5).** Every cell is `p≈10³`; secp is `2²⁵⁶`. `g=2` at these primes establishes
  the exact identity that the *analytic* route consumes — the reach comes from a proof, not these
  numbers.

**Next, in order:** (i) the `ζ₃ ∈` splitting-field forced check (§6 of the analysis; an instrument
check); (ii) re-verify the Stickelberger citation before any use; (iii) the order-pinning / `μ(L)` step.
The `[REV §4b]` lead — that `L*` descends to `ℚ(ζ_n)^{⟨σ_λ⟩}`, the Galois home of the `ζ₃` — is the
most likely source of the second input the order-pinning needs.
