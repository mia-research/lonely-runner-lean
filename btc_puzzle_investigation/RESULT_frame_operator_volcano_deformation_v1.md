# RESULT — down the volcano: the frame operator's `½` is a **symmetry** fact, its `¾` a **shape** fact; neither survives descent (differently), and `¾` is **not a hexagonal fingerprint**

*2026-07-24. Opens the conductor/volcano direction — the one `(★)` does not bound. Object: the frame
operator `C = Σ eis(x)eis(x)ᵀ` (Master Part V, M10), whose eigenvalue ratio `λ_max/Tr` is `½` on the
μ₃-core and `¾` on the full lift. Script: `scratchpad/frame_deform.py`, exact `sympy` (algebraic
numbers, no float in any reported value). Curve/CM/lattice geometry; **no leakage / key-recovery / ECDLP
claim.***

---

## 0. The setup, and the crater fact `[PROVED]`

Every `j = 0` curve `y² = x³ + b` carries the GLV automorphism `[ω] : (x,y) ↦ (βx, y)`, which satisfies
`[ω]² + [ω] + 1 = 0`, so **`ℤ[ω] ⊆ End(E)`**. `ℤ[ω]` is already the maximal order, so `End(E) = ℤ[ω]`
and **every `j=0` curve sits at the crater of every ℓ-isogeny volcano — secp included.**

A **descending** ℓ-isogeny (`ℓ | f`, the conductor `f = [ℤ[ω] : ℤ[π]]`; secp `f = 3·79·349·C112`) lands
on a curve `E'` with `End(E') = ℤ + ℓℤ[ω]` — a non-maximal order. Its unit group is **`{±1}` only**:
`E'` has **`j ≠ 0`, no μ₃, no GLV `β`.** The endomorphism lattice is the index-ℓ sublattice
`L_ℓ = ℤ + ℓℤ[ω]` — a sublattice of the hexagonal lattice that is **not itself hexagonal**.

**Question (the user's):** which proved laws are μ₆/`j=0` facts, and which are CM-lattice facts that
survive when the lattice stops being hexagonal? Answered here for the frame operator.

## 1. The `½` (μ₃-core) is pure symmetry — exact, and lost off the crater `[PROVED + VERIFIED]`

`λ_max/Tr = ½ ⟺` the second-moment tensor is **isotropic** (`C ∝ I`). For **any** μ₃-symmetric point set
this is **forced**: the 2-dimensional real representation of `C₃` (rotation by 120°) is **irreducible**,
so the only μ₃-invariant symmetric 2-tensor is a multiple of the identity (Schur). Hence
```
λ_max/Tr = ½   EXACTLY,   for every μ₃-symmetric set — independent of the lattice, of θ, of p.
```
Numerical witness: a random cloud symmetrized under μ₃ gives `C = c·I` (off-diagonal exactly 0), ratio
`½`. The square lattice gives `½` too — for the same reason (μ₄ also has an irreducible 2-D real rep).

> **`½` is not hexagonal and not arithmetic — it is the signature of a symmetry group with an
> irreducible 2-D real representation (μ₃, μ₄, μ₆).** On a volcano descendant, whose symmetry is only
> `{±1} = μ₂` (2-D rep reducible, `−I`), **this force is gone** — the "core" of `E'` has no reason to be
> isotropic. **The `½` is a crater/μ₃ fact, lost by loss of symmetry.**

## 2. The `¾` (full lift) is a hexagonal **shape** constant that deforms down the volcano `[VERIFIED — exact algebraic]`

`λ_max/Tr` of a uniform distribution over the **reduced** fundamental rhombus of `L_ℓ = ℤ + ℓℤ[ω]`:

| `ℓ` | reduced cell | `λ_max/Tr` (exact) | ≈ |
|---:|---|---|---|
| 1 (hexagonal, crater) | 60° rhombus | **`3/4`** | 0.7500 |
| 2 | 1 : √3 rectangle | `3/4` | 0.7500 |
| 3 | — | `½ + √37/16` | 0.8802 |
| 5 | — | `½ + √13/8` | 0.9507 |
| 7 | — | `½ + √1297/76` | 0.9739 |
| `ℓ → ∞` | degenerate (1-D) | `→ 1` | — |

Reproduces the record's `¾` at `ℓ=1`. **As one descends (ℓ grows), the constant climbs monotonically
from `¾` toward `1`** — the lattice stretches and the second moment becomes anisotropic. For secp's
conductor primes `ℓ ∈ {3, 79, 349, …}`: `ℓ=3 → ≈0.88`, and the large primes `→ 1` (fully degenerate).

> **`¾` is a hexagonal-lattice shape fact — it deforms off the crater, by change of lattice shape (not
> loss of symmetry).**

## 3. ★ Caveat that sharpens the record: `¾` is **not a hexagonal fingerprint** `[VERIFIED]`

The `ℓ = 2` reduced cell is a **1 : √3 rectangle** — a *different* lattice — and it **also gives exactly
`¾`** (variance ratio `1 : 3 ⇒ 3/(1+3) = ¾`). So the value `¾` does **not** identify the hexagonal
lattice; it is shared by a rectangular sublattice by aspect-ratio coincidence.

**Bearing on the record:** Master Part V calls `¾` "θ-independent lattice geometry." True at the crater,
but the *number* `¾` alone is not a hexagonal certificate — any claim of the form "`¾` ⟹ hexagonal
structure" is **too strong**. The hexagonal structure is certified by the *pair* `(½ core, ¾ full)`
together with the μ₃ isotropy of §1, not by `¾` alone. Recommend annotating M10 accordingly.

## 4. The dichotomy this establishes

| law | nature | fate on a conductor-ℓ descendant |
|---|---|---|
| frame-operator core `½` | **symmetry** (μ₃ irreducibility) | **lost** — μ₂ does not force isotropy |
| frame-operator full `¾` | **shape** (hexagonal reduced cell) | **deforms** — `½ + √(ℓ⁴−ℓ²+1)/(…)`, `→1` |
| Cap Law / flap / `ε` / sextant | **defined via the μ₃ β-action** | **undefined** — no `β` exists on `E'` |

> **The entire lift-geometry programme is a crater phenomenon.** Its symmetry parts (`½`, and every
> β-defined object) vanish off the crater because μ₃/μ₆ vanish; its one shape part (`¾`) survives as a
> deforming lattice constant. **Nothing in it is a CM-lattice fact that persists unchanged on a
> non-hexagonal descendant.** This is a structural characterization, and it is *why* these laws carry
> "zero secp arithmetic" (Master, `masked_structure_findings` v5–v13): they are properties of the
> hexagonal crater, which every `j=0` curve shares.

## 5. Honest scope — what is proved vs conjectured

- §1 (`½` = μ₃ symmetry, lost under μ₂) — **`[PROVED]`** (representation theory) **+ VERIFIED**.
- §2 lattice values and §3 (`ℓ=2` rectangle also `¾`) — **`[VERIFIED — exact algebraic]`**, pure lattice
  geometry, no curve or model assumption.
- ⚠ **The claim that a real descendant curve `E'`'s frame operator equals the `L_ℓ` value of §2 is
  `[DERIVED — UNVERIFIED]`.** It assumes `E'`'s CM-reduction fills the `L_ℓ` reduced cell uniformly — the
  record's established model at `ℓ=1`, extended but **not computed on an actual descendant.** The clean
  next probe: build a 3-isogenous descendant at a small crater prime, define its eis via `ℤ+3ℤ[ω]`, and
  check the frame constant is `½+√37/16 ≈ 0.88`. Until then §2 is a statement about lattices, and its
  application to descendant *curves* is a conjecture.
- **No `d`-side content, no secp-scale claim** (all lattice work; the crater fact §0 is the only
  full-scale statement and it is `[PROVED]`).

---

## 6. What remains open in the volcano direction

1. **Verify §2 on an actual descendant curve** (the `[DERIVED — UNVERIFIED]` step above).
2. **What, if anything, is intrinsic to the descendants?** They lose every μ₆ law; do they gain a
   μ₂-specific invariant the crater lacks? Unknown.
3. **The conductor factorization `f = 3·79·349·C112` as a set of volcano depths** — is there structure in
   *which* primes divide `f` (e.g. a splitting/inert pattern in `ℤ[ω]`)? Untouched.
4. Priority check — not run.

---

*Grades as tagged inline. Scan-free: §1 is representation theory, §2–§3 exact algebraic geometry of
lattices; the scale banner is not invoked because no `p`-scan enters. The one curve-arithmetic statement
(§0, crater) is `[PROVED]` and holds at secp.*
