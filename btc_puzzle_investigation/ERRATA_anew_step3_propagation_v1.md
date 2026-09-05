# ERRATA — the A1.1 / Step 3 correction, for the two files a concurrent session owns

**2026-08-02.** Phase 3 of the `A_new` programme propagated the 2026-08-02 grade correction into
`PROJECT_SUMMARY_secp256k1_v2.md` (done, `compile-diff` clean after two defects it caught were fixed).

**This errata covers the remaining two files, which are NOT versioned here on purpose.** A background
task (`task_b151d9f3`, started by the user in a separate session) is editing the *same two files* for a
*different* defect — the withdrawn "Weil restriction" sentence retracted on 2026-07-23. Creating
versions of them here would collide with a session whose state I cannot see. This document is the
authoritative statement of *my* correction so that whoever versions those files merges **both**.

---

## Correction 1 — `POSITIVE_FINDINGS_ADDENDUM_1_v1.md` §A1.1

**Target: lines 73–77**, the three-step proof, specifically step 3:

> *"3. That relation is incompatible with both non-supersingular `p`-rank strata: ordinary (`End⁰` a
> commutative quartic CM field), and `p`-rank 1 in both its forms …"*

**Defect.** The ordinary case is not excluded. *"ordinary ⇒ `End⁰` a commutative quartic CM field"* is
**false** when `A ⊗ F̄_p` is isogenous to `E²`, where `End⁰ = M₂(K)` is non-commutative. That case
appears in neither listed branch.

**Witness** (executed, `anew_step3_witness_v2.sage` / `.log`): `A = E × E^d`, `E/F_p` **ordinary**,
`d` a non-square, `ψ : E^d → E` the twisting isomorphism over `F_{p²}`,
`i : (P,Q) ↦ (ψ(Q), −ψ⁻¹(P))`. It satisfies every hypothesis step 3 uses — `i` on the whole surface,
`i² = −1`, `π i π⁻¹ = −i`, `p ≡ 3 mod 4` — **and is ordinary**, and reproduces `b₁ = 0`.
**0 failures, 30 ordinary curves × 10 primes**, disjoint sample; the load-bearing condition
`π ∘ i = (−i) ∘ π` verified pointwise at `k = 2, 4`.

**Also target: lines 101–104**, which record the owed diligence:

> *"Independent adversarial re-derivation of the two external inputs … has not been run."*

**Update:** external fact **(i)** (the Frobenius-twist relation `π φ = φ^σ π`) is now **discharged** by
that witness. External fact **(ii)** (the surface `p`-rank/`End⁰` dichotomy) is **not re-derived — it
is replaced** by the Cartier derivation, and must be recorded as *retired by replacement*, never as
*verified*.

**Also target: line 88**, which still asserts *"`A_new` is up to isogeny the **Weil restriction** of an
elliptic curve `E'/F_{p²}`"*. **That is the separate 2026-07-23 withdrawal that `task_b151d9f3` is
handling.** Both corrections land in the same bullet; merge, do not overwrite.

**Grade:** `[PROVED — scale-free, curve-independent]` → **`[PROVED — reviewed replacement argument;
2 citation caveats]`**. The *conclusion* stands; the *argument in this file* does not establish it.

## Correction 2 — `RESULT_mu6_cohomology_supersingular_v2.md`

**Target: §1 Step 3, lines 52–71** — same defect, this is the primary statement of it:

> *"**Ordinary (`p`-rank 2).** `End⁰(A_new)` is a commutative field (a quartic CM field). Then
> `π i π⁻¹ = i ≠ −i`. Contradiction."*

**Adjudication, pre-committed before the witness was run and recorded here:** the footnote at
lines 68–71 and the parenthetical at 62–63 argue via `i_a`, the restriction of `i` to an ordinary
**factor**. The witness's `i` **swaps** the two factors and has no such restriction, so **no passage of
§1 reaches the `M₂(K)` ordinary case.**

**Target: §5 lines 152–154** — the "open to an independent eye" clause. Same update as Correction 1:
(i) discharged, (ii) replaced-not-verified. **The independent adversarial re-derivation it asks for
has now been run** — on the replacement argument, not on this one, and it returned clean with two
cosmetic corrections applied.

**Target: §2 lines 95–96** — the same withdrawn "Weil restriction" sentence as Addendum line 88.
`task_b151d9f3` again. Merge.

---

## What replaces the argument, in one paragraph (for whoever writes the new versions)

`𝒞` is the Cartier operator on `H⁰(C, Ω¹)`; `dim V_b = ⌊3b/4⌋ = (0,1,2)`. At `p ≡ 3 mod 4` the grading
gives `𝒞(V₃) ⊆ V₁`, and `dim V₁ = 0`; equivalently, with `t = 3(p+1)/4`,
`deg(x^a f^{p−t}) ≤ (3p−5)/4 < p−1`, so the coefficient `𝒞` reads does not exist. Either way `𝒞`
vanishes on the whole new part `V₁ ⊕ V₃`, so `a(A_new) = 2` and **`A_new ⊗ F̄_p` is superspecial** —
strictly stronger than supersingular. Inputs: `4 ∣ p+1`; `deg f = 3` separable; the standard
superelliptic basis and Cartier formula; `p ∤ deg(E × A_new → Jac C)`. No `End⁰` classification, no CM
input, no `j = 0` input. Scale-free ⇒ valid at `p = 2²⁵⁶−2³²−977`.

**Two citation caveats travel with it and must appear wherever the conclusion does:**
1. **Oort, Math. Ann. 214 (1975), Theorem 2 *together with* Remark 3** gives `a(X) = g ⟺ superspecial`
   **over an algebraically closed field** — so the decomposition is over `F̄_p`, not `F_p`.
2. **Pries, Prop. 3.17** states `g = 2`: `p`-rank `0 ⟺` supersingular for **principally polarized**
   abelian varieties. `A_new` is a Jacobian complement whose induced polarization need not be
   principal. Whether that hypothesis is load-bearing is **unresolved**.

Full record: `RESULT_anew_supersingularity_step3_gap_and_cartier_route_v1.md` and `_v2.md`.

---

## Status of Phase 3

| file | state |
|---|---|
| `PROJECT_SUMMARY_secp256k1_v1.md` → **`_v2.md`** | **DONE.** Six targeted edits + two stale-`unconditional` sites that `compile-diff` caught (Part D closed-doors list; §B.1 Route 2). `compile-diff`: 1017/1029 predecessor lines byte-identical, 46/46 retractions present, 6/6 N-items present, **zero grades moved up, zero losses** |
| `POSITIVE_FINDINGS_ADDENDUM_1_v1.md` | **NOT versioned here** — errata above; concurrent session owns it |
| `RESULT_mu6_cohomology_supersingular_v2.md` | **NOT versioned here** — errata above; concurrent session owns it |
| `POSITIVE_FINDINGS_MASTER_v4.md:156,190` | **no edit needed.** Its `⚠ inherits N2` warning and the N2 row (*"verified 24/24 at small `p`, **not proved for dimension 2**"*) are **closer to correct than what replaced them** in the summary. They stand as written |
