# RESULT v3 — the bridge (B) is a CHANGE OF VARIABLE: `FLD = χ₂(α)·FLD_c`. `|FLD|=6h` proved for
# 6th-root multipliers; reduced to ONE sharp lemma (cube-root canonical flap) for the rest.

*2026-08-08. Supersedes v2 (kept as trail). This is the "fix the test" pass: v1/v2 tested and
proved things about the **ρ-window object**, then leaned on an unproven bridge (B) to reach the
**reduced-basis FLD**. This version runs the reduction **on the reduced-basis FLD itself** and finds
(B) is not a coincidence — it is an exact change of variable. No leakage / ECDLP claim.*

---

## 0. The methodological fix

The defect v2 diagnosed: my claim was about the master's reduced-basis `FLD`, but my chain proved a
class-number law for a *different* construction (the ρ-window) and connected them only by the empirical
bridge `(B) |signed| = |S′|`. A test that proves things about object X cannot validate a claim about
object Y. So this pass asks: **what is the reduced-basis σ, arithmetically, and does it reduce to the
canonical flap the flap-lemmas/dagger machinery handles?**

## 1. What the reduced-basis σ actually is

`u(x),v(x) = co(eis(x))` are the **centered** lattice coordinates `cent(αx)/p, cent(βx)/p` for two
dual-basis multipliers `α = p·u(1) mod p`, `β = p·v(1) mod p`. Verified exactly (`fld_dual_mult_v1`,
`fld_changevar_v1`, `p≡7 mod12`, 194 primes):

| fact | result |
|---|---|
| `u(x)=cent(αx)/p`, `v(x)=cent(βx)/p` (linear) | 194/194 |
| `t(x):=p(u−v) ≡ (α−β)·x (mod p)` integer, linear | 194/194 |
| **`c := β/α` is a nontrivial 6th root of unity** `ρ^k`, `k∈{1,2,4,5}` | **194/194** |

The last line is the ℤ[ω]-module structure of the ideal lattice surfacing: the two reduced-basis
vectors differ by `ω`, so the two dual multipliers differ by a 6th root. `σ(x)` is therefore **not** a
2D mystery — it is the canonical single-multiplier flap `sign(cent(x)−cent(cx))` after the substitution
`x → αx`.

## 2. The bridge (B) is a change of variable  `[VERIFIED 194/194; mechanism = ω-scaled dual basis]`

> **`FLD = χ₂(α) · FLD_c`**,  `FLD_c := Σ_x sign(cent(x)−cent(cx))·χ₂(x)` on flap `|cent(x)−cent(cx)|>p/2`,
> `c = β/α = ρ^k`.

Proof is algebra: put `y=αx` (bijection of `F_p*`); `σ(x)=sign(cent(αx)−cent(βx)) = sign(cent(y)−cent(cy))`,
and `χ₂(x)=χ₂(α)χ₂(y)`. (Orientation `+` uses `cent(y)+cent(cy)`; same argument.) **Verified 194/194.**
This **dissolves (B)**: `|FLD| = |FLD_c|`, exactly — not a numerical coincidence between two flaps, but
one flap re-indexed. v2's "(B) unproven" is superseded; the real content is `|FLD_c|=6h`.

## 3. Corrected grade for `|FLD| = 6h`

`|FLD| = |FLD_c|`, so it reduces to the **canonical flap law** `|FLD_c| = 6h` at `p≡19 mod24`:

| multiplier class | share (194 primes) | `|FLD_c|=6h` | proof status |
|---|---|---|---|
| `c` primitive **6th** root (`k=1,5`) | 60/194 (31%) | 30/30 | **`[PROVED]`** — exactly the flap-lemmas ρ-object + dagger `(†)` |
| `c` primitive **cube** root (`k=2,4`) | 134/194 (69%) | 66/66 | `[VERIFIED, not proved]` — needs the cube-root analogue of `(†)` |

So: **`|FLD|=6h` is `[PROVED]` on the ≈31% of primes whose dual basis is 6th-root-related, and reduced
to ONE sharp lemma — the cube-root canonical-flap class-number law — on the other ≈69%.** The remaining
gap is no longer an opaque bridge; it is a specific character-sum identity for order-3 `c`, and the
**SIGN law** already covers the underlying pure sign-sum for order-3 χ/c (`RESULT_twisted_dedekind_structure_v2`,
review: "0 fails over 250 (χ,c) triples including complex χ of orders 3,4,6"). The open work is the
flap→window reduction for cube-root `c`, mirroring flap-lemmas v3 §1–3.

**Honest headline:** `|FLD|=6h` is **not** a completed theorem. It is proved for a minority of primes and
sharply reduced for the majority. The advance over v2 is that (B) is explained (change of variable) and
the residual is one well-posed lemma with its tool identified — not that the theorem is closed.

## 4. Bonus — this resolves the *shape* of the FLD-sign question (frontier #9)

`sign(FLD) = χ₂(α)·sign(FLD_c)`. The master found `sign(FLD)=−χ₂(M)` "reduces to no **intrinsic**
invariant." That is now explained: the sign carries a factor `χ₂(α)`, and `α` is a **reduced-basis
(gauge-dependent) multiplier** — so `sign(FLD)` is *expected* to resist reduction to an intrinsic
invariant, because part of it is `χ₂` of a basis choice. Frontier #9's "no intrinsic invariant" is a
feature of the `χ₂(α)` gauge factor, not a missing law. (Testable: is `χ₂(α) = −χ₂(M)/sign(FLD_c)`?)

## 5. Reproduction
```
python3 fld_dual_mult_v1.py   100 1000      # beta/alpha is a 6th root of unity, 38/38
python3 fld_changevar_v1.py   100 6000      # FLD = chi2(alpha)*FLD_c, 194/194; |FLD_c|=6h by root class
```
Exact `int`/`Fraction`; `h(−p)` by reduced-form count.

## 6. Ledger of what stands
- `(†)` `[PROVED]` (dagger, reviewed) — ledger item 16 stale (unchanged).
- `FLD = χ₂(α)·FLD_c` `[VERIFIED 194/194; provable from ℤ[ω]-module structure]` — new; dissolves (B).
- `|FLD_c|=6h`, `c` 6th root `[PROVED]`; `c` cube root `[VERIFIED 66/66, open]`.
- `|FLD|=6h` overall: `[PROVED for k∈{1,5}; reduced to the cube-root canonical-flap lemma for k∈{2,4}]`.
  **Not** `[PROVED]` outright — v1's grade remains withdrawn.
- L1: `[PROVED — corollary]` on the ρ-window object (unchanged).
