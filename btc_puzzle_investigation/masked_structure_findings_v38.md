# v38 — Both S problems reduced to one primitive-6th-root Dedekind region

**Date:** 2026-07-18 · **Scripts:** `_dedekind_reduction_v1.py`, `_dedekind_sum_connection_v1.py`
(+ v37 machinery). Task: (P1) close H1's lattice lemma `(−1)^{flap/6}=χ₂(2)`; (P2) the S-core — why,
when parity permits, `S` actually hits 0 (35/35).

> ## ⚠ SCALE / SCOPE
> Verified `p ≤ 3000`. Pure lift/lattice geometry, x-only — **no leakage bearing.** `p≡1 mod 6`,
> `n=#E(F_p)` prime. **Grading is strict: everything below is a `[VERIFIED]` reduction or a
> `[PROVED]` step; the two target statements are NOT proved from scratch — they are reduced to named
> classical lemmas and verified, not closed. Do not read this as a proof of H1 or the S-core.**

---

## 1. The common reduction — both problems live on ONE region  `[PROVED reduction + VERIFIED]`

Babai rounding in the reduced basis is coordinate-wise, so the rhombus coordinates are
**`u(x)=cent(ax)/p`, `v(x)=cent(bx)/p`** for fixed `a,b∈F_p*` (`cent` = centered residue in
`(−p/2,p/2]`). Verified exactly for all `x`, all p. Substituting `s=ax`, `r=b/a`, and folding the
`σ`-orientation (`±`) into the sign of `r`, the flap triangle `T⁺` becomes:

```
T⁺_s = { s ∈ F_p* :  cent(s) − cent(ρs) > p/2 } ,   ρ = a PRIMITIVE 6th ROOT of unity (ρ²−ρ+1≡0).
```
**`ρ` is order 6 at every prime** (verified; provable — the Eisenstein-reduced basis puts `R₁,R₂` at
120°, so `r=b/a` is a 6th root). Both open problems are exactly:

- **P1 (H1 lemma):** `|T⁺_s| ≡ 0 (mod 6) ⟺ χ₂(2)=1`.  *(verified)*
- **P2 (S-core):** `S = (χ₂(a)/3)·Σ_{s∈T⁺_s} χ₂(s)`, so `S=0 ⟺ Σ_{s∈T⁺_s} χ₂(s)=0`.  *(verified)*

`T⁺` matches the flap `{σ=+1}` exactly (all primes). *(`_dedekind_reduction_v1.py`.)*

**Why one object serves both:** `1−ρ = −ρ²` (from `ρ²=ρ−1`), so `cent(s)−cent(ρs) ≡ −ρ²s (mod p)` —
the flap is a **carry of multiplication by the cube root `ρ²`**. Both the *size* (P1) and the
*χ₂-weight* (P2) of the same carry-region are what's asked.

---

## 2. The Dedekind main term is a fixed CM value — `χ₂(2)` is a BOUNDARY effect  `[VERIFIED]`

The Dedekind sum of the region evaluates in closed form (`_dedekind_sum_connection_v1.py`, all p):
```
s(ρ,p) = Σ_{i=1}^{p-1} ((i/p))((ρi/p)) = −(p−1)/(12p)     — a fixed CM-point value, NO χ₂(2) content.
```
So the `χ₂(2)` distinction is **not** in the Dedekind main term; it lives entirely in the **boundary
lattice-count** (points near the line `cent(s)−cent(ρs)=p/2`). This confirms P1/P2 are
**Eisenstein/Gauss-lemma boundary statements**, and tells the proof exactly where to look.

---

## 3. P1 reduced to a Gauss's-lemma congruence  `[VERIFIED — the crisp remaining lemma]`

Clean triangle reformulation (`3 | N` so `N` and `ORB` share parity; `(−1)^N=(−1)^ORB`):
```
N := |T⁺_s| = #{ s ∈ [1,(p−1)/2] : ρs mod p ∈ (p/2, p/2 + s) }        (verified = |T⁺_s|)
```
Gauss's lemma gives `χ₂(2)=(−1)^{μ₂}`, `μ₂=#{s∈[1,(p−1)/2]: 2s mod p > p/2} = (p+1)/4` (`p≡3 mod 4`).
So **P1 ⟺ the lattice congruence**
```
N ≡ μ₂ (mod 2)         [verified 27/27, p≤3000]   ⟹   (−1)^{flap/6} = χ₂(2).
```
This is a decidable, self-contained Eisenstein-style statement: the flap-triangle count and the
`χ₂(2)` Gauss count agree mod 2. **Remaining step (not done): prove `N ≡ μ₂ mod 2`** by the standard
triangle-reflection argument. `[GAP — named]`

---

## 4. P2 reduced to a character balance on the same region  `[VERIFIED — remaining lemma]`

```
Σ_{s∈T⁺_s} χ₂(s) = 0   ⟺   χ₂(2) = 1        [verified, p≤900]
```
i.e. when `ORB` is even the flap μ₆-orbits split **exactly evenly** between `χ₂(rep)=+1` and `−1`.
Since every *multiplicative* and *reflection* involution was already ruled out (v36), the pairing that
forces this balance is **non-multiplicative and involves `2`** (the balance appears precisely when
`χ₂(2)=1`, i.e. `2=c²`). **Remaining step (not done): exhibit that pairing / evaluate the sum as a
Jacobi-type object.** `[GAP — named]`

---

## 5. Status — grading

| item | grade |
|---|---|
| `u=cent(ax)/p`, `v=cent(bx)/p` (coordinate-wise Babai) | `[VERIFIED exact, all x]` (standard) |
| `T⁺_s = {cent(s)−cent(ρs)>p/2}`, `ρ` primitive 6th root | `[PROVED reduction + VERIFIED]` |
| both problems on this one region | `[VERIFIED]` |
| `s(ρ,p) = −(p−1)/(12p)`; `χ₂(2)` is a boundary effect | `[VERIFIED]` (known CM value) |
| P1 ⟺ `N ≡ μ₂ (mod 2)` | `[VERIFIED]`; the congruence itself `[GAP — named]` |
| P2 ⟺ `Σ_{T⁺}χ₂(s)=0 ⟺ χ₂(2)=1` | `[VERIFIED]`; the balance `[GAP — named]` |

**Neither H1 nor the S-core is proved.** What is achieved: both were separate, opaque empirical
`p mod 8` facts; they are now **one** explicit Dedekind region (`ρ` a primitive 6th root), with the
Dedekind main term evaluated, `χ₂(2)` localized to the boundary, and each target reduced to a single
crisp classical lemma (a Gauss-lemma lattice congruence for P1; a character balance for P2). The two
`[GAP]`s are the remaining work — standard-flavored but not executed here.

**No leakage bearing** (x-only lattice geometry, inside the Part V bound).

---

## 6. Reproduction
```
python3 _dedekind_reduction_v1.py 100 1100        # u,v=cent(a/b x)/p; T+ = 6th-root region; P1,P2 verified
python3 _dedekind_sum_connection_v1.py 100 900    # s(rho,p) = -(p-1)/(12p); chi2(2) is boundary
```
Both exact (int/Fraction); signal path has no float. Prior: v37 (H1 reduction), v34 §4 (S law).
