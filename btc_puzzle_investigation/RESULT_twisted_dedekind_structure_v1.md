# RESULT — the twisted sign/sawtooth family: a structure map (paper-oriented)

*2026-07-24. Grew out of the proof of `(†)` (`RESULT_fld_dagger_proof_v1.md`). Records the general
structure around the twisted Dedekind–Rademacher sums, graded per piece. `p ≡ 7 mod 12` throughout
(so `χ₂` odd, a primitive 6th root exists), `n=#E(F_p)` prime, `h = h(−p)`. Verified with exact
integer/`Fraction` arithmetic. Intended as raw material for a possible paper — grades are strict.*

**No leakage / ECDLP claim. Pure analytic number theory (character-twisted lattice sums).**

---

## 0. The two families

For `c ∈ (ℤ/p)*`, `c ≠ 1`, and a Dirichlet character `χ` mod `p`, define
```
sawsum_χ(c) = Σ_{s=1}^{p−1} χ(s)·((cs/p))          ((x)) = {x} − ½  (sawtooth)
sgnsum_χ(c) = Σ_{s=1}^{p−1} χ(s)·sgn(cs mod p − s)
```

## 1. The SAWTOOTH law — general, clean, PROVED

> **`[PROVED — all χ]`  `sawsum_χ(c) = χ̄(c)·B_{1,χ}`,  where `B_{1,χ} = (1/p)Σ_{t=1}^{p−1} χ(t)·t`
> is the generalized Bernoulli number.**

*Proof.* `Σχ(s)((cs/p)) = (1/p)Σχ(s)(cs mod p) − ½Σχ(s)`. For `χ≠χ₀` the second term is 0; substitute
`t = cs mod p` (bijection of `(ℤ/p)*`): `(1/p)Σ_t χ(c⁻¹t)·t = χ̄(c)·B_{1,χ}`. ∎

Verified `max|·| ≤ 3×10⁻¹³`, `d=2,3,6`. Specializations:
- **`χ₂` (odd):** `B_{1,χ₂} = −h`, so **`sawsum_χ₂(c) = −χ₂(c)·h`** (the anchor used in the `(†)` proof).
- **`χ₃` (even, `χ₃(−1)=1`):** `B_{1,χ₃} = 0`, so `sawsum_χ₃ ≡ 0`.
- **`χ₆` (odd):** `B_{1,χ₆} = 1 − √3·i` type (a Gauss/Jacobi period), so `sawsum_χ₆(c) = χ̄₆(c)·B_{1,χ₆}`.

## 2. The SIGN sum

### 2a. Even characters give zero `[PROVED]`
Under `s↦p−s`: `sgn(c(p−s) mod p − (p−s)) = −sgn(cs mod p − s)`, while `χ(p−s)=χ(−1)χ(s)`. For **even**
`χ` (`χ(−1)=1`) the summand is antisymmetric ⇒ `sgnsum_χ ≡ 0`. (E.g. `χ₃`, verified exactly 0.) A
nonzero sign sum requires an **odd** character. `[PROVED]`

### 2b. The QUADRATIC law (LAW1) — the centerpiece `[VERIFIED strongly; PROVED at c=ρ]`

> **`sgnsum_χ₂(c) = 2h·(1 − χ₂(c) + χ₂(c−1))`.**

Verified for **all `c`** at **27/27** primes `p≡7 mod12`, `p<600` (exact). Firing control: the reduced
form `2h(1−χ₂(c))` (dropping the `χ₂(c−1)` term) **fails at 27/27** — the `c−1` boundary term is
essential. Linear-fit residual `10⁻¹⁴`; coefficients `(C,A,B)=(2h,−2h,2h)` exactly (`h=5→10`, `7→14`,
`9→18`).

- **`(†)` is the case `c = ρ`** (primitive 6th root): `χ₂(ρ)=−1`, `χ₂(ρ−1)=χ₂(ρ²)=1` ⇒
  `sgnsum_χ₂(ρ) = 2h·3 = 6h`, i.e. `T = 3h`. **`[PROVED]`** (`RESULT_fld_dagger_proof_v1.md`, orbit
  collapse using `ρ²=ρ−1`).
- **General `c`: `[VERIFIED, general proof OPEN]`.** The orbit-collapse proof is specific to order-6
  `ρ`. Two proved companions constrain the general law: the reciprocity `M(c) = −χ₂(c)·M(c⁻¹)` (§3),
  and the sawtooth law (§1). Reducing LAW1 to a character-weighted floor/Dedekind count (Berndt–Evans
  machinery) is the natural route — not yet executed.

### 2c. The SEXTIC sign sum is genuinely richer `[VERIFIED — no clean universal form]`
`sgnsum_χ₆(c)` is **determined by `(χ₆(c), χ₆(c−1))`** (§4) but is **not** a linear function of them:
a 9-term character basis fits exactly at some primes (`p=199`, coeffs `±6`) and fails at others
(`p=79,151`, residual `≈9`). So **the clean linear closed form is special to the quadratic character**;
the order-6 case has `p`-dependent structure. Recorded as a boundary of the clean theory, not a gap to
paper over.

## 3. Reciprocity `[PROVED]`
Let `M(c) = Σ_s χ₂(s)·[cs mod p > s]`, so `sgnsum_χ₂(c) = 2M(c)`. Substituting `t=cs` and using
`Σχ₂=0`:
> **`M(c) = −χ₂(c)·M(c⁻¹)`.**
Verified consistent with LAW1 (`M(c⁻¹)` via `c⁻¹−1 = −(c−1)/c`, `χ₂(−1)=−1`).

## 4. The endpoint-determination structural law `[VERIFIED — d=2,3,6]`

> **For every character order `d | (p−1)`, `sgnsum_{χ_d}(c)` is a function of `(χ_d(c), χ_d(c−1))`
> alone.**

The value depends on `c` only through the character at the two "cusps" `c` and `c−1` — the signature
of a Dedekind–Rademacher cocycle. Verified `d=2,3,6` at `p=79,127,151` (every `c`). For `d=2` the
function is linear (LAW1); for `d=6` nonlinear (§2c). **A proof of this structural law would be the
paper's backbone** — it is the general phenomenon of which LAW1 and `(†)` are the cleanest instance.

## 5. Grades and paper-relevant status

| statement | grade |
|---|---|
| `sawsum_χ(c) = χ̄(c)·B_{1,χ}` (all χ) | **`[PROVED]`** |
| `sawsum_χ₂(c) = −χ₂(c)h` | **`[PROVED]`** |
| sign sum `≡ 0` for even χ | **`[PROVED]`** |
| **LAW1** `sgnsum_χ₂(c)=2h(1−χ₂(c)+χ₂(c−1))` | `[VERIFIED 27/27 all c; PROVED at c=ρ; general proof OPEN]` |
| `(†): T = 3h` (`c=ρ`) | `[PROVED — pending review]` |
| reciprocity `M(c)=−χ₂(c)M(c⁻¹)` | **`[PROVED]`** |
| endpoint-determination (all `d`) | `[VERIFIED d=2,3,6]` |
| `sgnsum_χ₆` nonlinear / `p`-dependent | `[VERIFIED — boundary of the clean theory]` |

## 6. Open (the paper's spine)
1. **Prove LAW1 for general `c`** — reduce `M(c)` to a `χ₂`-weighted floor count and apply Berndt–Evans.
2. **Prove the endpoint-determination law** for general `d` (the cocycle statement).
3. **Characterize `sgnsum_χ₆`** — the `p`-dependence, likely a Jacobi-sum / `ℤ[ζ₆]` object.
4. Scope reconciliation `p≡7 mod12` vs `RESULT_fld_classnumber`'s `p≡19 mod24` for `|FLD|=6h`.
5. Pending adversarial review of the `(†)`/`c=ρ` orbit-collapse proof.
