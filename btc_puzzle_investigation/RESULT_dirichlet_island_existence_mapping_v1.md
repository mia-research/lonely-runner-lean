# RESULT — Dirichlet islands: do they EXIST and can they be MAPPED? (established first, independent of leakage)

**Grade: `[VERIFIED — exact: enumeration + closed formula + three-gap theorem]`.** Date 2026-08-17.
**This establishes the OBJECT only.** Whether a public key *leaks* its island-membership is a **separate**
question, deferred to `RESULT_dirichlet_island_structure_and_leakage_v1`. The islands below are a
**deterministic, key-independent** structure of the interval + the curve arithmetic — they are there whether
or not anything leaks. Does not edit any master; accumulates toward a future v13. Reproduction:
`scratchpad/islands_exist_map.py`, `islands_secp_map.py`. Exact `int` throughout.

## The question (posed correctly, before leakage)
Two distinct "island" objects appear in the thread. Establish that each **exists as a well-defined set** and
is **mappable** (describable at puzzle scale without brute force). Leakage is NOT addressed here.

## Object 1 — SOURCE islands (best-approximation points of `d`)
`d_q = 2^(b−1)(1 ± 1/q)` — scalars whose ratio `d/2^(b−1)` is a small-denominator rational. The distinct
centers are exactly the floor-quotient set `{⌊2^(b−1)/q⌋}`.
- **EXISTS + count is EXACT:** `#centers = 2·⌊√N⌋−1 (+1)`, `N=2^(b−1)`. **Enumeration = formula, 4/4**:
  b=10→44, b=14→180, b=18→723, b=22→2895 (all exact).
- **MAPPED at puzzle scale** (formula, no enumeration): b=135 → **2^68 centers** (coverage 2^−66 of the
  interval); b=140 → 2^70 (2^−69); b=145 → 2^73 (2^−71). Sparse, but an explicit, computable set.

## Object 2 — the full FAREY island hierarchy (key-independent)
Farey fractions `p/q ∈ [1,2)` (since `d/2^(b−1) ∈ [1,2)`); the island (Stern-Brocot cell) around `p/q` has
half-width `~1/(qQ)` — **low q ⇒ big island**, nested hierarchy.
- **EXISTS + MAPPED (exact):** center count in `[1,2)` at order Q = 22/80/324/1260 for Q=8/16/32/64, growing
  `~(3/π²)Q²`; big cells at `1/1, 3/2, 4/3, …`, smaller ones nested. A deterministic tessellation.

## Object 3 — the CURVE island `{d ∈ I : λd mod n ∈ I}` (the in-scope, endomorphism object)
Scalars in the interval whose GLV image `φ(P)=[λ]P` lands back in the interval. `λ` = cube root of unity mod
`n` (verified `λ²+λ+1≡0`).
- **EXISTS — ENUMERATED, not just expected:** small curves, `|I|=6√n`: expected ~35, **enumerated 37 (n=10009)
  / 36 (n=40009)**.
- **THREE-GAP THEOREM CONFIRMED (the mapping mechanism):** the enumerated island gaps take **≤3 sizes, with
  the largest = sum of the other two** — n=40009 gaps `[17, 23, 40]`, **40 = 17+23** ✓; n=10009 gaps `[10,19]`
  (2 sizes). So the set is a genuine three-distance/Bohr set, its geometry fixed by `CF(λ/n)`.
- **MAPPED at real secp puzzle scale** (via convergents of `λ/n`, `CF(λ/n)=[0,1,2,14,3,2,1,7,…]`, 142
  convergents spanning 2^0..2^255): island **count = 2^12 / 2^22 / 2^32** (b=135/140/145); the characteristic
  gap sizes are the convergent denominators bracketing `n/|I|` — b=135: `q≈2^121..2^122`; b=140: `2^112..2^117`;
  b=145: `2^111..2^112`. The full 2^12-point puzzle-135 island set is therefore **describable in closed form**
  (three gap sizes from CF(λ/n)) without enumerating 2^134 values.

## Established (existence + mapping — this file's whole claim)
- **YES, the islands exist**, as three distinct deterministic key-independent sets (source best-approx; Farey
  hierarchy; curve ×λ return set), each with an **exact size** and **exact/closed-form structure** at puzzle
  scale.
- **YES, they are mappable**: source/Farey by exact formula; curve island by `CF(λ/n)` + three-gap theorem
  (verified by enumeration). No brute force needed to describe the puzzle-scale sets.
- **Scope:** existence/mapping is exact and unconditional. The count for Object 3 is the expectation `|I|²/n`;
  the three-gap *structure* is theorem-backed and enumeration-confirmed at small n.

## Explicitly SEPARATE (not this file)
Whether the public point `P=[d]G` reveals which island (if any) the **secret** `d` lies in — the leakage /
keyspace-reduction question — is deferred to `RESULT_dirichlet_island_structure_and_leakage_v1`. Existence
and mappability stand on their own regardless of that answer.
