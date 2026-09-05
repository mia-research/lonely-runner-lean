# DEVIATIONS from PREREG_amicable_correspondence_bits_v1.md

All deviations below were decided **before** any data from the registered features were computed. None is
forced by a result; each is forced by an algebraic identity, a cost structure, or an arithmetic error in
v1. `PREREG_amicable_correspondence_bits_v1.md` stays **frozen** as written (it is the ordering evidence);
the amended spec that will actually be run is
**`PREREG_amicable_correspondence_bits_v2.md`**. This file is the bridge between them.

Independent re-verification at amendment time (scratchpad `cm2.py`, `frame3.py`, `design2.py`,
`design3.py`): the coordinator's frame numbers were **reproduced, not accepted** — see D1/D2.

---

## D1. Prime frame extended; design split into two tiers. **CHANGED.**

**The prereg says** (§6): a single frame `p < 20000`, **21** independent amicable units, and (§5) a
minimum detectable amicable-vs-non-amicable rate difference of **0.333**, with the explicit sentence
"a difference of `0.23` would need 30 matched pairs, which the frame does not contain at `p < 20000`."

**What changed.** The `p < 20000` cap in v1 was an artifact of counting points by the `O(p)` character sum
(see D2). With a CM counter the frame extends. Re-enumerated independently:

| limit | amicable | non-amic | fraction | 2-cycles (units) |
|---|---|---|---|---|
| 20000 | 42 | 93 | 0.311 | 21 |
| 200000 | 216 | 566 | 0.276 | 108 |

Both rows reproduced here from scratch; the `p < 20000` sub-frame matches v1 §6 **element-for-element**
(same 21-unit list). The `10⁶` row (839/2296/420) was **not** verified at amendment time and is not relied
on by v2.

**The cost fact that decided the design, which the unit count and `Σn` alone do not show.** The exact
`Γ*` arm needs **no** resampling (its null is analytic, FPR `< 2^{−(n−1)/4}`), so it costs `Σn`. The
graded arm of §2b needs **199 M1 replicates**, so it costs `199 × Σn` — the binding cost, and it is not
in the `Σn` column:

| frame | curves (both orientations, both arms) | `Σn` | exact arm | graded arm `199 × Σn` |
|---|---|---|---|---|
| `p < 20000` | 84 | 6.50 × 10⁵ | trivial | **1.29 × 10⁸** — affordable |
| `p < 200000` | 432 | 3.47 × 10⁷ | **3.47 × 10⁷** — affordable | 6.91 × 10⁹ — not affordable |
| `p < 10⁶` | — | 3.94 × 10⁸ (coordinator) | ~23× the above | 7.8 × 10¹⁰ — not affordable |

**Amendment (pre-data).** Two tiers, each with its own scope line, and **no number from one tier may be
quoted with the other's scope**:
- **Tier A — `p < 200000`, 108 units:** exact `Γ*` arm (§2 primary) and the exact ARM-B invariants.
- **Tier B — `p < 20000`, 21 units:** graded arm (§2b) and the sampled ARM-B invariant.
Extending Tier A to `10⁶` is a pre-declared future option contingent on a faster exact-arm implementation;
taking it requires a new entry in this file, not a judgment call at run time.

**Scope this moves.** Tier A minimum detectable rate difference **0.333 → 0.065** (exact Fisher, one-sided,
`α = 0.01`, 108 vs 108). **The `0.23` effect v1 §5 called unreachable is now inside the frame.** Tier B's
floor is unchanged at 0.333. Scale-honesty figure moves from 14.25 bits to **17.60 bits** against secp's
256 — still spanning none of the gap; the §6 scale clause is unweakened.

---

## D2. Point counter replaced: `O(p)` character sum → CM/Cornacchia. **CHANGED, validated.**

**The prereg says** (§6, implicitly via the frame script) that `n = #E_7(F_p)` is obtained by the `O(p)`
Legendre-sum count.

**What changed.** For `y² = x³ + 7` with `p ≡ 1 mod 3`, Cornacchia gives `p = a² + 3b²`, the six
sextic-twist traces are `{±2a, ±(a+3b), ±(a−3b)}`, and the correct one is selected by testing which
candidate order annihilates independent points; `q ≡ 2 mod 3` is `j = 0` supersingular with `#E = q+1`.

**Validation, re-run independently at amendment time (`cm2.py`).** Over **all 1123** primes `p ≡ 1 mod 3`
with `11 ≤ p < 20000`, the CM counter agrees with the `O(p)` counter on **1123/1123, zero mismatches**.
Exactly **2** primes (`p = 13`, `p = 181`) were left ambiguous by the 5-point annihilation test and were
resolved by the `O(p)` fallback. The fallback is retained in the pipeline.

**Scope this moves.** None, at `p < 20000` — the sub-frame is reproduced exactly. Above 20000 the counter
is the only source of `n`, so **its validation is now a pipeline-validity control** and is recorded in
v2 §8 alongside the no-float check. If the counter returns `None` (ambiguous) and the `O(p)` fallback is
infeasible at that size, the curve is dropped **and listed**, never dropped silently.

---

## D3. Unit rule `p < n` was not orientation-neutral. **FIXED.**

**The prereg says** (§6): "Units are one curve per 2-cycle, the one with `p < n` → 21 independent
amicable units."

**The algebra.** Every amicable pair appears in both orientations (`(67,79)` and `(79,67)`), and the frame
contains exactly 108 of each. For `p < n`, reduction mod `n` is the **identity** on `[0,p)`, so
`x̄ = x` and the reduction map `ρ` is injective. For `p > n`, `ρ` is a genuine reduction with at most 2
preimages per coordinate, the collision set having size `p − n = t_p − 1`. **The v1 unit rule therefore
systematically selected the orientation in which the collision structure is absent** — precisely the
structure ARM-B (D5) measures, and a silent scope restriction on the primary arm's features as well.

**Amendment (pre-data).** Both orientations of every 2-cycle are run. The **independence unit remains the
2-cycle** (108 at Tier A, 21 at Tier B); **orientation is a pre-declared stratum** (`p<n`, `p>n`); the
matched contrast is formed and tested **within stratum** (pool sizes: 279 non-amicable at `p<n`, 287 at
`p>n` — both ample for 108 matched pairs). Numbers from the two orientations are never pooled into one
rate without saying so.

**Scope this moves.** Curve count 21 → 216 at Tier A (108 units × 2 orientations) and 42 at Tier B; `Σn`
doubles as tabulated in D1. Statistical `n` for the contrast is unchanged (108 / 21 **units**), because
the two orientations of a 2-cycle are not independent.

---

## D4. v1 §6's divisor-cell range was computed over the wrong set. **CORRECTED.**

**The prereg says** (§6): "`#{k | n−1 : k > 6}` ranges **4 to 35** over the frame (e.g. `n=79`: 4;
`n=6091`: 27; `n=18793`: 35)."

**The error.** That range was computed over the 21 **amicable** units only, not over the frame actually
entering Holm — which includes the matched non-amicable controls and (per D3) both orientations.
Recomputed over the sets that will be run: **Tier B 4 to 57**, **Tier A 4 to 102**.

**Scope this moves.** Holm within unit is applied over up to 57 (Tier B) / 102 (Tier A) cells rather than
35, making the graded arm's per-unit threshold **more conservative** than v1 stated. The §5 `e_min` design
figure is unchanged (it is per-cell, `z* = 4.5`), but the correction is disclosed because v1 published a
wrong number with a scope attached to it.

---

## D5. Second arm registered: measure the banned map, do not use it. **ADDED.**

**The prereg says** (§1, T1): `φ : E(F_p) ≅ Z[ω]/(π_p − 1) ≅ F_n` **is** the discrete logarithm, so `φ` is
banned from any feature. **T1 is not weakened.** It bans `φ` from the *feature path*; it does not make `φ`
unmeasurable, and inside the frame `φ` is computable.

**Amendment (pre-data).** v2 registers **ARM-B**, reported separately from the primary arm and never
merged with it: structural invariants **of the correspondence itself**, output as properties of the
channel, never as a recovered scalar. Illegal (still banned): build a feature from `φ`, ask whether it
predicts `d` — circular. Legal (ARM-B): invariants of the *relation* between `φ` and the T1-legal
surrogates.

**Two of the three candidate invariants were dropped, with algebraic reasons, rather than registered
weakly:**
1. **Non-homomorphy defect `δ(P,Q) = φ(P+Q) − φ(P) − φ(Q) mod n` — dropped, forced.** `φ` is a group
   **isomorphism** (that is what the CM structure map is), so `δ ≡ 0` identically. No control can fire
   against an algebraic identity. **Salvaged as A2-3**, which measures the same defect for the *legal*
   surrogate against the partner-side group law — where F4's coprimality theorem forces "nonzero
   somewhere" but says nothing about support size, which is exactly the gap left open.
2. **Fibre geometry of `φ` against the μ₆ orbits — dropped, forced.** `φ` is injective, so its level sets
   are singletons; and `φ(λP) = ℓ·φ(P)` where `ℓ³ ≡ 1 mod n` is the *definition* of the GLV eigenvalue.
   Both halves are identities. **Salvaged as A2-2**, which asks whether the μ₆ action descends through the
   legal double reduction — not an identity in either direction.
3. **Capacity of the legal family — registered, as A2-1**, in the only non-saturated form. An
   information-theoretic capacity statement about the legal family is **vacuous**, because the family
   already contains injective maps (`P ↦ x`), so its information about `d` is maximal for free. The
   non-vacuous axis is structural: every legal feature factors as `Φ = f ∘ ρ` with `ρ(P) = (x mod n,
   y mod n)`, hence `Γ*(ρ) ⊆ Γ*(Φ)` **for every legal `Φ`**. `Γ*(ρ)` is therefore a **family-level floor**
   — the symmetry every legal feature has for free — and is a statement about the family, not about the
   four members enumerated in §2.

**A disclosure the amendment forces into the open.** Computing `Γ*` at all uses the enumeration index
`j = φ(P_j)`. That is a use of `φ` **on the measurement side**, never in the feature path: `Φ` receives a
point, never `j`. The distinction is load-bearing and is now stated in v2 §1 — a symmetry group `Γ`, once
named, is usable **without** `φ`, which is why the finding would not inherit `φ`'s cost.

**Scope this moves.** ARM-B numbers carry their own scope line: computed where `φ` is computable, i.e.
**in-frame only**. They **do not transport to secp by computability** (there `φ` costs a discrete log); a
structural law about the map could transport, but **only by proof**.

---

## D6. §9 cell 8 (abstention) threshold updated. **CHANGED.**

**The prereg says** (§9 cell 8): abstain if "the observed rate difference is < 0.33".

**Amendment (pre-data).** The floor is now per tier: **Tier A < 0.065**, **Tier B < 0.333**, ARM-B per its
own §5 numbers. The cell itself — its wording, and the rule that abstention is reported as abstention and
is neither a null nor a closure — is unchanged.

---

*(D7–D8 are the v2 → v3 changes. The amended spec is now
`PREREG_amicable_correspondence_bits_v3.md`; v1 and v2 stay frozen. Both were decided pre-data: the Tier A
exact arm was in progress but records `(|Γ*|, |Γ*_inv|, |image|, flags, fibre multiset)` as raw integers
and is rule-agnostic, so no rule below is locked in by the run. No contrast, no amicable-vs-control
comparison, and no §9 cell had been evaluated.)*

---

## D7. The validity gate was stated as an equality; two of four features could not fire. **FIXED.**

**The prereg says** (v2 §2A): "`Φ` is `Γ*`-faithful iff `|image(Φ)| = (n−1)/|Γ*(Φ)|` exactly", and
(v2 §9): "'Fires' = `|Γ*|/|Γ*_forced| > 1` **with the faithfulness gate passed**".

**The cardinality argument (design-time, not a measurement).** `ΦA` and `ΦB` are character-valued, so
`|image| ≤ 3` for every `n`. The equality then requires `|Γ*| = (n−1)/|image| ≥ (n−1)/3`. Any genuine
intermediate symmetry — a `Γ_k` with `6 < k ≪ n`, **which is the hypothesis under test** — makes them
non-faithful by cardinality alone, and under v2's conjunctive firing rule they could then not fire.
**Two of the four frozen hypothesis features were structurally incapable of registering a positive**, and
a real `Γ_k` on either would have been recorded as a non-event. Confirmed as stated.

**The identity v2 stated in too strong a form.** `(Z/n)^*` acts on itself by multiplication **freely**
(`tj = j`, `j` invertible ⇒ `t = 1`), so every orbit has size exactly `|Γ*|` and `(n−1) = |Γ*|·#orbits`.
Each fibre of `Φ` is a union of orbits, giving the **theorem** `|image(Φ)| ≤ (n−1)/|Γ*_inv(Φ)|`, with
equality iff every fibre is a *single* orbit. So v2's equality is not a validity condition — it is the
special case "fibres are exactly orbits", reachable only by features whose alphabet is large enough.
**Correction to the form proposed:** the bound is on `Γ*_inv(Φ) := ker(Γ*(Φ) → Sym(image Φ), t ↦ σ_t)`,
not on `Γ*`. For `Σ_Φ ≠ {id}` — i.e. `ΦD` — `Φ` is not constant on `Γ*`-orbits and the bound does not
apply to `Γ*` at all. Re-verified numerically (`verify_gate.py`): `n ∈ {7,13,19,31,43,67,79}`, 300 random
coarse label maps each, **zero violations**, and equality held **iff** every fibre was a single orbit.

**Amendment (pre-data).**
1. **Gate = the inequality** `|image(Φ)| ≤ (n−1)/|Γ*_inv(Φ)|`, plus `|Γ*_inv|` dividing `n−1`. A violation
   is mathematically impossible ⇒ bug ⇒ **run void**. That is the gate's only job.
2. **Firing** = `|Γ*|/|Γ*_forced| > 1` **and** `|Γ*_forced|` divides `|Γ*|` **and** `DEG` false.
   Orbit-exactness is not a condition on firing.
3. **Orbit-exactness (the equality) is retained as the CLASSIFIER of a positive**, not merely as a
   diagnostic — because it is exactly the condition under which `log₂|Γ*_inv|` is the quantity comparable
   to F2's `log₂6`. §9 cell 1 splits into **1a** (orbit-exact: `Φ` separates the orbits, so a quotient rho
   walk on `Φ`'s values collapses the search space by `|Γ*_inv|`) and **1b** (not orbit-exact: the
   symmetry is real, but no `√|Γ*_inv|` speedup follows from `Φ` alone; `log₂|Γ*_inv|` is an upper bound
   on what a finer invariant readout could collapse, and `Φ` delivers `log₂|image Φ|` bits of narrowing).
   **Both are positive findings; they are different findings and may not be conflated.**
4. **Degeneracy predicate, exact:** `DEG(Φ) :⟺ |image(Φ)| = 1`, equivalently `Γ*_inv(Φ) = (Z/n)^*` (the
   two are equivalent, proof in v3 §2A). This is the only content-free configuration: for a `Λ`-valued
   `Φ` a chance symmetry costs `≈ |Λ|^{−(n−1)(1−1/k)}`, so **a coarse alphabet does not manufacture `Γ*`**.
5. **Mandatory reporting per row:** `(|Γ*|, |Γ*_inv|, |image|, orbit_exact, DEG)` + the exact fibre-size
   multiset; **both** `log₂|Γ*_inv|` and `log₂|image|` quoted, neither called "bits about `d`" without the
   orbit-exactness qualifier.

**Scope this moves.** **Replication thresholds are unchanged** (`≥ 77/108`, `≥ 18/21`), as anticipated:
the change alters which features can *reach* a cell, not how units are counted. No multiplicity adjustment
is needed either — the exact arm's per-row FPR is `< 2^{−(n−1)/4}`, so family-wise error over 4 features ×
216 curves stays numerically zero, and the graded arm's Holm correction is untouched. What does move: `ΦA`
and `ΦB` become able to register a positive at all, and every positive now carries a 1a/1b label that
fixes which number is comparable to `log₂6`.

---

## D8. `N0` is not degenerate as v2 described it; degeneracy control replaced. **FIXED.**

**The prereg says** (v2 §2A): `N0 = ord(Q(P))` is the "degenerate control — on the amicable arm
`#Ẽ(F_n) = p` is prime, so `ord ≡ p`, `|image| = 1`", and §9 cell 9 voids the run keyed to it.

**Measured at spec time (`verify_gate.py`), not assumed.** The `⊥` branch (reduced `x̄` not on `Ẽ(F_n)`)
is a **label** under v2 §2A's own `⊥` convention, and it occurs at a substantial rate: **48/78** at
`(67,79)`, **34/66** at `(79,67)`, **498/966** at `(907,967)`. So `|image(N0)| = 2`, not 1. Moreover the
label map is exactly `N0 = m ∘ ΦA` with `m : {+1,0} ↦ p`, `{−1} ↦ ⊥` (verified: the observed
`(ΦA, N0)` pair set is exactly `{(+1, p), (−1, ⊥)}` on all three curves). **`N0` is a coarsening of `ΦA`**,
hence `Γ*(N0) ⊇ Γ*(ΦA)` by construction — it is redundant with a hypothesis feature, not degenerate, and
it could fire whenever `ΦA` does. The predicate `|image| = 1` does not describe it, and §9 cell 9 was
keyed to a description that does not hold.

**Amendment (pre-data).**
1. **New degeneracy control `N_const(P) := 0`** (the constant map). `|image| = 1`, `Γ*_inv = (Z/n)^*`, so
   `DEG` **must** trigger; if `DEG(N_const)` is false the predicate is not wired ⇒ **run void**.
2. **`N0` is reclassified** as a **disclosed-redundant diagnostic**: not a control, not a hypothesis
   feature, counted in no tally, contributing to no `K`. Retained for grid stability with the identity
   `N0 = m ∘ ΦA` recorded, so the redundancy is disclosed rather than discovered later.
3. **§9 cell 9 is re-keyed** to: a feature with `DEG` true reported as firing, **or** `DEG(N_const)` false
   on any curve, **or** the §2A inequality violated anywhere. Any of the three ⇒ run void.

**Scope this moves.** The frozen hypothesis grid (`ΦA`–`ΦD`) and `K` are unchanged, so no threshold moves.
What changes is that the run now has a degeneracy control that actually can trigger — under v2 the
control could not have caught the failure it was written to catch, which by the project's own standard
would have made that guard uninformative.
