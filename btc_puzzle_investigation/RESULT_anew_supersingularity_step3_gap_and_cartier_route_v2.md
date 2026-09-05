# RESULT v2 — `A_new` supersingularity: the Cartier route REVIEWED; standard facts verified with two open caveats

*2026-08-02. Supersedes `RESULT_anew_supersingularity_step3_gap_and_cartier_route_v1.md`, which is
retained unmodified. v1's findings stand; v2 adds the two gate outcomes owed by
`PREREG_anew_supersingularity_reaudit_v3.md` §3, applies the two corrections the reader found, and
records the citation deltas. **No leakage, ECDLP or key-recovery claim in any part.***

**What is unchanged from v1** — §2 (Step 3's ordinary-stratum gap and the `E × E^d` witness, 0/30
failures, A1 and A5 clean), §4 (the decidable shadow, 287 distinct classes, all controls fired),
§5 (the C4 void). Read v1 for those; they are not restated.

---

## 1. Gate outcome 0a — independent adversarial reader: CLEAN

Isolated context per root `CLAUDE.md` §2b: the reader was given only the derivation and the criteria —
not the session narrative, not the finding it replaces, not its authorship. It was told explicitly it
was **not scored on problems found**.

**Verdict: the claim stands; all 8 checked items correct; no mathematical error.**

It validated its own instrument before ruling, which is the part that makes the verdict worth
something:

| its own check | result |
|---|---|
| `V₂` block vs the independently-computed Hasse invariant of `E` (coefficient of `x^{p−1}` in `f^{(p−1)/2}`) | exact match, 12 primes × 40 curves, **0 mismatches** |
| `p`-rank from Cartier (`rank M³`) vs `p`-rank from point counting (degree-6 L-polynomial via `#C(F_p), #C(F_{p²}), #C(F_{p³})`) | **134 curves, 12 primes, 0 mismatches** |
| `dim V_b = ⌊b·deg f/m⌋` verified by explicit divisor computation for `(m,d) = (2,3), (3,4), (4,3), (5,3), (7,3)` | counts match predictions in every case, summing to `(m−1)(d−1)/2` |
| item 8, "is superspecial too strong?" | `a(A) = 2` at `p ≡ 3 mod 4` and `0` at `p ≡ 1 mod 4`, **100%** on 13 primes × 25 curves, agreeing with point counts |

**Two defects found, both real, both cosmetic — corrected in §3 below:**

1. **Step 3′ was called "independent".** It is not: it shares Step 2 with Step 3. It is independent of
   the **degree count** only. (It is also the cleaner of the two arguments.)
2. **`(1 − ζ₄²)/2` is an abuse of notation.** Read literally as an endomorphism of `Jac(C)` it is
   `(1 − [−1])/2 = 1`. It means `(1 − ι_*)/2` where `ι` is the involution *induced by* `ζ₄²`.

**The mechanism it supplied for item 8** — worth recording, because it answers the objection I could
not answer myself: a 1-parameter family can be uniformly superspecial because **`C` and `E` move while
`A` does not.** `j(E)` sweeps all `p` values in `F_p`, while at `p ≡ 3 mod 4` the `A`-factor
L-polynomial takes only a handful of values, all `F_p`-twists of one geometric object. The `μ₄`
signature `(dim V₁, dim V₃) = (0,2)` is why. Finiteness of the superspecial locus is satisfied by a
**constant** map, not violated.

It also reported a correction to its own work: a first pass claimed `A` ordinary in only 12/25 rows at
`p ≡ 1 mod 4`; that was its own bug (testing `p ∤ c₁` instead of `p ∤ c₂`), corrected to 25/25, and
caught because it disagreed with its validated Cartier computation.

> ⚠ **One aside of the reader's is NOT adopted as data**: that the `A`-factor L-polynomial "takes only
> **4** values, `c ∈ {0, ±p, ±2p}`" — which lists five while saying four. That is precisely the open
> `m`-support question; it is being **measured** (`PREREG_anew_m_support_v2.md`), not inherited.

## 2. Gate outcome 0b — citations: verified, with two caveats that must travel

| fact | source, as actually located | verdict |
|---|---|---|
| **`a(X) = g ⟺ superspecial`** | **Oort, *Which Abelian Surfaces are Products of Elliptic Curves?*, Math. Ann. 214 (1975), p. 35 — Theorem 2 *together with* Remark 3.** Thm 2 is the forward implication only; Remark 3 supplies the converse and states the biconditional ("necessary and sufficient"). Conclusion is an **isomorphism** `X ≅ E₁ × … × E_g`, not an isogeny. | **VERIFIED — with a scope caveat** |
| **`g = 2`: `p`-rank 0 ⟺ supersingular** | **Pries, *The Torelli locus and Newton polygons*, §3.3.1 Prop. 3.17**: `(C) ⇒ (B) ⇒ (A)`, with `(A) ⇏ (B)` first failing at **`g = 3`** (witness: `p`-divisible group `G_{2,1} ⊕ G_{1,2}`, slopes `1/3, 2/3`, `p`-rank 0, not supersingular). | **VERIFIED — with a hypothesis caveat** |
| **which `m` are realizable** | see §4 | **VERIFIED** |

**CAVEAT 1 (Fact 5) — the isomorphism is over `F̄_p`, not `F_p`.** Oort's Theorem 2 requires `k`
algebraically closed, twice (in Notation 1 defining `a(X)`, and in the theorem). It gives
`A_new ⊗ F̄_p ≅ E₁ × E₂`; it does **not** give a decomposition over `F_p`. v1's prereg stated
superspecial over `F̄_p`, so the use is sound — but v1's RESULT text did not say so at every use, and
this file does. Two smaller deltas: my "`g ≥ 2`" hypothesis **is not in the source and is not needed**;
and the citation must be **"Theorem 2 + Remark 3"**, not Theorem 2 alone.

**CAVEAT 2 (Fact 6) — the source assumes principal polarization.** Pries states §3.3.1 and Prop. 3.17
for **principally polarized** abelian varieties. `A_new` is a complementary factor of a Jacobian and
carries an *induced* polarization that need not be principal. The verifier declined to resolve whether
that hypothesis is load-bearing, and I am not resolving it by inference. **This is an open caveat on
Step 5 and travels with every use of the conclusion.** (The elementary Newton-polygon argument for
`g = 2` — `p`-rank 0 ⇒ no slope 0 ⇒ by symmetry no slope 1 ⇒ all slopes `1/2` — appears not to use
polarization, but that is my reasoning, not a citation, and it does not discharge the caveat.)

## 3. The derivation, corrected

Steps 1, 2, 3 and 5 are **unchanged from v1 §3**. The two corrections:

**Step 3′ (restated).** `w³·f⁻¹ = w³/w⁴ = 1/w`, so by Step 2 the image `𝒞(V₃) ⊆ V₁`, which is `0` by
Step 1. ~~independent~~ → **This shares Step 2 with Step 3 and is independent of the *degree count*
only.** It is the shorter of the two arguments; the degree count is a second route to the same
vanishing given Step 2.

**Step 4 (restated).** The addition isogeny `E × A_new → Jac(C)` has kernel inside `Jac(C)[2]`, hence
2-power degree, hence degree prime to odd `p`; it is therefore separable and `φ*` is a
`𝒞`-compatible isomorphism `V₁ ⊕ V₃ ≅ H⁰(A_new, Ω¹)`. The idempotent is **`(1 − ι_*)/2`**, where `ι`
is the involution induced by `ζ₄²` — ~~`(1 − ζ₄²)/2`~~, which read literally as an endomorphism of
`Jac(C)` would be `1`. The `a`-number is **not** an isogeny invariant, but it **is** preserved by
isogenies of degree prime to `p`, which is what is used here.

**Step 5 (scope stated).** `a(A_new) = 2 = dim A_new` ⇒ **`A_new ⊗ F̄_p` is superspecial**, i.e.
`≅ E₁ × E₂` with `Eᵢ` supersingular **over `F̄_p`** (Oort Thm 2 + Rmk 3); hence `p`-rank 0; hence, for
`g = 2`, supersingular — the last step subject to **Caveat 2**.

## 4. What Fact 7 settles, and what it hands to the next run

The Honda–Tate question v1 left open is answered, and **against my hypothesis**:

> **All five `m ∈ {−2,−1,0,1,2}` are realized as characteristic polynomials of abelian surfaces over
> `F_p`, `p > 3`, `p ≡ 3 mod 4`.** For `m = −1` the class is a **simple surface of dimension 2, not
> 4**: `π` is a root of `x⁴ − px² + p²`, `ℚ(π) = ℚ(√−3, √−p)` quartic CM, and every local invariant
> above `p` vanishes (`v(π)/v(q) = 1/2` times an even local degree, at both `p ≡ 7` and `p ≡ 11
> mod 12`), so `e = 1` and `dim = 1·4/2 = 2`. The doubling does occur for `m = −2` — but from the two
> **real** places, not from `p`. `m = +2` is realized only non-simply, as `E × E`.

Sources: Singh–McGuire–Zaytsev Thm 12.1(2) (stated for `n` odd, i.e. exactly `q = p`);
Howe–Nart–Ritzenthaler Table 10.1 + Thm 10.1; own Honda–Tate computation calibrated against
Waterhouse Thm 4.1 across 29 primes. **Weakest link, carried:** for `m = ±1` at `p ≡ 7 mod 12` the
only published support obtained is the SMZ preprint — Xing and Maisner–Nart Table 1 were **not
obtained**, and are the peer-reviewed primaries to get if this becomes load-bearing.

**Reading hazard flagged by the verifier and recorded here:** HNR Table 10.1's caption restricts it to
classes **splitting over `F_{q²}`**, so *absence of a row is not non-existence*; and several sources
state results over `F_q` where the answer **differs between `q` square and `q` non-square**. Our
`q = p` is never a square. Waterhouse's famous "`p ≢ 1 mod 3`" condition belongs to the `q`-square
world and must not be imported.

**Consequence for the next run:** there is **no a-priori obstruction** to `m = −1`. So if the family
`w⁴ = f` never realizes it, that is a fact about **our family**, not a triviality about abelian
surfaces — and HNR Thm 10.1 adds that over `F_p` every simple supersingular class contains a Jacobian,
so the `m = −1` class is populated. This is what `PREREG_anew_m_support_v2.md` measures.

## 5. A correction owed to the earlier artifact

The `experiment-designer` gate, auditing the `m`-support spec, found a **sign flip carried by
`anew_cartier_audit_v2.sage:190`**: it computes `b1 = nE - nC`, whereas `L_C = L_E·L_new` gives
**`b₁ = #C(F_p) − #E(F_p)`**. Gate artifact: at `p = 13`, `f = x³+7`, true `b₁ = −6`, the code gives
`+6`; the three flipped rows are exactly those with `b₁ ≠ 0`.

**No verdict of the 2026-08-02 run changes**: `b₂` uses `b₁²`, and the supersingularity criterion uses
`b₁ mod p`. The defect is confined to the **printed** `b₁` on the `p ≡ 1 mod 4` arm. Corrected in
`anew_m_support_v2.sage`; recorded here rather than silently fixed.

## 6. Grades after both gates

| item | v1 | v2 |
|---|---|---|
| the Cartier derivation | `[UNREVIEWED DERIVATION]` | **`[PROVED — one independent review; two citation caveats open]`** — Caveat 1 (Fact 5 is over `F̄_p`), Caveat 2 (Fact 6 assumes principal polarization). **Not flat `[PROVED]`**: `PREREG_..._v3` §5 forbids that for my own derivation, and the caveats are unresolved |
| `A_new` supersingular at `p ≡ 3 mod 4` | `[VERIFIED]` + `[UNREVIEWED DERIVATION]` | **`[PROVED — reviewed, caveated as above]`** + `[VERIFIED — 287 distinct classes]` |
| `A_new ⊗ F̄_p` superspecial | not stated with scope | **`[PROVED — reviewed]`, over `F̄_p`**, via Oort Thm 2 **+ Rmk 3** |
| external fact (i) `π φ = φ^σ π` | discharged by A5 | unchanged |
| external fact (ii) `p`-rank/`End⁰` dichotomy | owed | **no longer load-bearing** — §3 replaces it and §3 has now been reviewed. Recorded as *retired by replacement*, never as *verified* |
| Step 3 of `RESULT_mu6_cohomology_supersingular_v2.md` | gap found | unchanged — the gap stands; §3 is a different argument, not a repair of it |

**Downstream.** `Hom(E, A_new) = 0` / P13 / Route 2's "blocked" status no longer rests on an
*unreviewed* derivation. It now rests on a **reviewed** one carrying two named citation caveats. That
is a real improvement over v1's position and still **not** the unconditional status
`PROJECT_SUMMARY_secp256k1_v1.md:87` currently asserts ("Now UNCONDITIONAL — N2 discharged by A1.1"),
because the argument that line credits — §A1.1 Step 3 — is the one with the gap. The propagation is
Phase 3 and has not been done.

**Owed:** Xing / Maisner–Nart Table 1 as peer-reviewed primaries for `m = ±1` at `p ≡ 7 mod 12`;
resolution of Caveat 2 (is principal polarization load-bearing in Prop. 3.17?); `compile-diff` before
any master/handover promotion.
