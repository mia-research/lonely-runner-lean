# RESULT — the descendant frame operator is a **curve statement**: `(8+√37)/16 ≈ 0.8802`, verified end-to-end

*2026-07-24. Runs `PREREG_descendant_frame_operator_v1.md` (deviations: `..._DEVIATIONS.md` — 5, incl. a
recurring hardcoded-print bug caught by its own output). Promotes `RESULT_frame_operator_volcano_
deformation_v2.md` §3 from `[CONJECTURE]` to `[VERIFIED]`. Scripts: `descend_step1.py`, `descend_final2.py`,
`descend_curve.py`, `floor_check.py`, `connect.py`. Curve/CM/lattice geometry; no leakage / d-side / ECDLP
claim.*

---

## 0. What was owed, and what is now closed

v2 §3 flagged that "a real descendant curve's frame operator `= 0.88`" rested on two unstated
assumptions — the **ideal class** and **equidistribution**. Both are now resolved, and an actual
descendant curve is exhibited and certified. The result is no longer a lattice conjecture; it is a
statement about curves with `End = O_3 = ℤ + 3ℤ[ω]`.

## 1. The prereg outcome — control fired, prediction landed `[VERIFIED]`

Frame statistic `ρ = λ_max/Tr` of the **finite-`p` `eis'` point set** (the residue-ring reduction
`F_p ≅ O_ℓ/(π')` into the reduced cell — the record's own definition of `eis`, applied to the order
`O_ℓ`; `#reps = p` exactly at every prime):

| `ℓ` | prediction | `p=307` | `p=1009` | `p=3001` | `p=6007` | `p=10009` |
|---|---|---|---|---|---|---|
| **1** (crater, **C1 control**) | `3/4` | 0.7810 | 0.7498 | 0.7484 | 0.7572 | **0.7495** |
| 2 | `3/4` | 0.7501 | 0.7500 | 0.7500 | 0.7500 | 0.7500 |
| **3** (descendant) | `(8+√37)/16` | 0.8793 | 0.8801 | 0.8803 | 0.8800 | **0.8802** |

- **C1 fires:** at the largest prime `ℓ=1` gives `0.7495`, inside `[0.74, 0.76]`. The construction
  reproduces the record's crater `¾` — so `ℓ>1` is trustworthy (prereg §2).
- **ℓ=3 lands:** `0.8802` at `p=10009`, `|Δ| = 1×10⁻⁴`, matching `(8+√37)/16` exactly.

Per the prereg's pre-committed table, this is the "**C1 fires and ℓ=3 → 0.8802**" row ⇒ the descendant
frame operator **equals** the `O_3` value.

## 2. The ideal-class gap is closed by a class number `[VERIFIED]`

v2 §3(a): the descendant's period lattice is *some ideal class* of `O_ℓ`, not necessarily the principal
one. Resolved: **`h(O_ℓ) = 1` for `ℓ = 1, 2, 3`** (discriminants `−3, −12, −27`; exact reduced-form
count). So the prime `𝔭` above `p` is **principal**, `𝔭 = (π')` is similar to `O_3` as a lattice, and
`ρ` is **single-valued** = the shape of `O_3`'s reduced cell. **The ambiguity I flagged is real only at
`ℓ ≥ 4`** (`h(O_4)=h(O_5)=h(O_7)=2`), where it does not concern the 3-descent.

## 3. An actual descendant curve, exhibited and certified `[VERIFIED — p=43, 127]`

Existence via the **modular polynomial** `Φ_3(0,Y)/Y` (its roots *are* the 3-isogenous `j`-invariants):
at **every** crater prime it has exactly one non-zero root `j'` — a curve `E'/F_p` 3-isogenous to the
`j=0` crater curve, with `j' ≠ 0` (so `End(E') ≠ ℤ[ω]`). Vélu from a rational 3-torsion kernel reproduces
`j'` where the descending kernel is `F_p`-rational (`p=43→24`, `127→12`, `307→289`).

**Conductor certified at `p=43` and `p=127`:** there the descendant's **only** 3-neighbour is the crater
`j=0` (`Φ_3(j',Y)` has the single root `0`). Since (i) the crater is maximal (conductor 1), (ii) a
3-isogeny moves only the 3-part of the conductor by one, and (iii) `j' ≠ 0`, this forces
**`End(E') = O_3` (conductor exactly 3).** The `eis'` of these certified curves:

| certified curve | `eis'` frame `ρ` | vs `(8+√37)/16` |
|---|---|---|
| `p=43`, `j'=24` | 0.8794 | `|Δ| = 8×10⁻⁴` (finite-size) |
| `p=127`, `j'=12` | 0.8813 | `|Δ| = 1×10⁻³` (finite-size) |

⚠ **`p=307` is NOT a floor case** — `j'=289` has further 3-neighbours `{13,233,262}`, each of which
connects *only* back to `289` (conductor 9), so `v_3(f)=2` there. `j'=289` is still conductor 3 (depth 1),
but the clean, unambiguous certificates are `p=43,127`. (This corrected a hardcoded print that had
labelled every case a floor — deviation D1.)

## 4. The curve statement

> **A curve `E'/F_p` with `End(E') = O_3 = ℤ+3ℤ[ω]` — a 3-isogenous descendant of a `j=0` crater
> curve — has frame operator `λ_max/Tr = (8+√37)/16 ≈ 0.8802`, versus the crater's `¾`.** Verified via the
> order's `eis'` (converged to `10⁻⁴`, C1 control firing), with `End(E')=O_3` certified on actual curves
> at `p=43,127` and the value made single-valued by `h(O_3)=1`.

This is what turns v2's lattice arithmetic into a statement about curves: the descendant is a real curve,
its endomorphism ring is certified, and its `eis'` frame constant is `0.88`, not `0.75`.

## 5. It reaches secp's isogeny class — as a `[DERIVED]` consequence

**`v_3(f_secp) = 1`** (`f = 3·79·349·C112`, the `3` exact). So **secp has a 3-isogenous descendant with
`End = O_3`** — a real 256-bit curve, same order `n`, `j ≠ 0`, no GLV. Because `(8+√37)/16` is a property
of the **order** `O_3` (scale-free — the order is the same at every `p`; only `π'` scales), **that
descendant's frame operator is `0.8802`.** `[DERIVED]` — the small-`p` verification plus the scale-free
order argument; **secp's descendant curve was not itself constructed.** No d-side, no ECDLP content.

This is the concrete meaning of "descend off the crater": secp's own 3-neighbour is a curve where the
hexagonal `¾` has deformed to `0.88`, the μ₃ isotropy `½` is gone (no GLV), and the Cap Law / flap / `ε`
have no form (no `β`). The lift-geometry programme is a crater phenomenon; one step down, its constants
change.

## 6. What remains open

1. **`ℓ = 79, 349`** (secp's other conductor primes): `h(O_79), h(O_349) > 1` in general, so the ideal
   class matters and `ρ` is **not** single-valued — the descendant frame value is a **set**, unresolved.
   This is the genuinely open large-`ℓ` corner.
2. **A μ₂-specific invariant the descendants might *gain*** (they lose all μ₆ structure) — untouched.
3. **Structure in *which* primes divide `f = 3·79·349·C112`** (splitting/inert pattern in `ℤ[ω]`) —
   untouched.
4. Priority check — not run.

---

*Grades: §1 `[VERIFIED — prereg primary, C1 fired]`; §2 `[VERIFIED — exact class number]`; §3 curve
existence `[VERIFIED — Φ_3, 8 primes]`, conductor `[VERIFIED — p=43,127]`, `[DERIVED — standard CM]` for
the general conductor step; §4 `[VERIFIED]`; §5 `[DERIVED — scale-free order + v_3(f)=1; secp descendant
not constructed]`. Small-`p` scans under frontier §XI.5's banner; the frame value, being a property of the
order, is scale-free.*
