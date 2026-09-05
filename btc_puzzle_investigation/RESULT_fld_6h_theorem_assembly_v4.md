# RESULT v4 — `|FLD|=6h` proved for ALL p≡19 mod24: every prime reduces to the 6th-root dagger case
# via `FLD = χ₂(α)·FLD_{c_eff}`, `c_eff` a primitive 6th root. v3's "31% proved / 69% open" was an
# enlarged null.

*2026-08-08. Supersedes v3 (kept as trail). Audit trigger: v3 used the hedge word "honest" on its
"69% not proved" claim; per `feedback_no_credibility_hedges`, the word flags an unchecked claim, and
stub-testing it showed the 69% was a suppressed positive. No leakage / ECDLP claim.*

---

## 0. The correction

v3 graded `|FLD|=6h` "`[PROVED]` for the 31% of primes with 6th-root `c=β/α`; cube-root `c` (69%)
`[VERIFIED, not proved]`." **That split was an artifact of computing the wrong flap formula for the
`orient='+'` primes.** Two facts close it:

1. **`FLD_c` with the `+` orientation `= FLD_{−c}` with the `−` orientation** (exact:
   `sign(cent(x)+cent(cx)) = sign(cent(x)−cent(−cx))`).
2. **`−(primitive cube root) = primitive 6th root`** (`−ρ² = ρ⁵`, `−ρ⁴ = ρ`).

So the `orient='+'`, cube-root-`c` primes are 6th-root computations in disguise. Defining the effective
multiplier `c_eff = c` (if `orient='−'`) `= −c` (if `orient='+'`):

> **`c_eff` is a primitive 6th root of unity — verified 134/134 (order exactly 6, every prime).**

## 1. The proved chain (real object, `p≡7 mod12`, 194 primes)

| step | statement | grade |
|---|---|---|
| 1 | `u,v = co(eis(x)) = cent(αx)/p, cent(βx)/p`; `β/α ∈ μ₆` | `[VERIFIED 194/194; = ℤ[ω]-module structure]` |
| 2 | `FLD = χ₂(α)·FLD_{c_eff}`, `c_eff = ±(β/α)`, **order 6** | `[VERIFIED 194/194 (id) + 134/134 (order 6)]` |
| 3 | `\|FLD_{c_eff}\| = 6h` for `c_eff` a primitive 6th root | **`[PROVED]`** — dagger `(†)` + flap-lemmas, reviewed |
| ⇒ | `\|FLD\| = 6h` at `p≡19 mod24`, `0` off | **proved modulo step 1–2 formalization** |

Direct verification on the reduced-basis FLD (`fld_effective_root_v1`): `|FLD|=6h` **66/66** at
`p≡19 mod24`, `FLD=0` **68/68** at `p≡7 mod24`, `c_eff` order 6 **134/134**, `FLD=χ₂(α)FLD_{c_eff}`
**134/134**.

## 2. Grade

**`|FLD| = 6·h(−p)` (M11): proved for ALL `p≡19 mod24`, modulo one mechanical lattice lemma** — that
`co(eis(·))` returns centered residues of two `ω`-related multipliers (step 1–2). That lemma is verified
194/194 and is the ℤ[ω]-module structure of the CM ideal lattice — a standard fact, not a research gap.
It is **not** the cube-root class-number gap v3 posited; that gap does not exist.

- v1 `[PROVED]` — overclaim (link 3 mis-graded).
- v2 `[PROVED modulo bridge (B), verified]` — (B) opaque.
- v3 `[PROVED 31% / cube-root lemma open 69%]` — **enlarged null (the 69% was 6th-root in disguise).**
- **v4 `[PROVED for all p≡19 mod24, modulo the change-of-variable lattice lemma; that lemma verified
  194/194, mechanism = ℤ[ω] ideal-basis structure]`.**

## 3. Sign of FLD (frontier #9) — decomposition only, the intrinsic link untested

`sign(FLD) = χ₂(α)·sign(FLD_{c_eff})` — verified 134/134 (the sign is included in the step-2 match). This
shows the FLD sign carries a **gauge factor** `χ₂(α)` (α a reduced-basis multiplier), which is why the
master found it "reduces to no intrinsic invariant." **Not tested here:** whether `χ₂(α)·sign(FLD_{c_eff})
= −χ₂(M)` (the master's 54/54 observation). That equality is a separate open sub-check, not claimed.

## 4. What is still owed (stated as claims, not hedges)
- **Formalize step 1–2** — the lattice change-of-variable lemma. Verified, mechanistic, unwritten.
- **`citation-verifier` on Dirichlet's finite class-number formula** — the one classical input to `(†)`;
  owed since 2026-07-25.
- **Frontier #9** — the `−χ₂(M)` link above.
- Ledger item 16 stale (`(†)` proved); master M11 grade should move `[EMPIRICAL]` →
  `[PROVED modulo the change-of-variable lemma]` via `compile-diff`.

## 5. Reproduction
```
python3 fld_root_symmetry_v1.py   100 1400    # FLD_{rho^k}: 6h only for k=1,5 with the '-' formula
python3 fld_effective_root_v1.py  100 4000    # c_eff always order 6 (134/134); FLD=chi2(a)*FLD_{c_eff}
python3 fld_changevar_v1.py       100 6000    # FLD = chi2(alpha)*FLD_c, 194/194
```
Exact `int`/`Fraction`; `h(−p)` by reduced-form count.
