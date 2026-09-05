# RESULT v3 — `A_new` supersingularity is PROVED for the two-prong push; the two caveats do not bite the downstream

*2026-08-20. Supersedes nothing — extends `..._v2.md` (which stands). Purpose: consolidate the
`A_new`-supersingular status that **Prong 1** of the `A_new` two-prong needs, correct an Aug-18
under-count of that status, and show the two open caveats from v2 are **non-load-bearing for the uses
Prong 2 (Brick E) makes of the result.** No leakage/ECDLP/key-recovery claim. The scale banner governs
every MEASURED row cited here; the derivation and the two arguments in §2 are form-level (no measured
input) and are the only things that reach secp.*

**One-line status.** `A_new` is **superspecial (⊇ supersingular) over `F̄_p`, for every `p ≡ 3 mod 4`
and every separable cubic `f`, secp included** — `[PROVED — one independent review + citations
verified, v2 2026-08-02]`. The residual caveats (F̄_p-vs-F_p; Pries principal-polarization) are dealt
with in §2 for the downstream we actually use.

---

## 1. What is actually proved (not "pending") — the record as of 2026-08-02

The Cartier-operator route **is** `RESULT_..._v1.md §3`. It is not a new idea to be checked; it was
derived and reviewed:

- **Derivation (v1 §3).** `C : w⁴ = f`, genus 3. Superelliptic basis `V_b = span{x^a dx/w^b}`,
  `dim V_b = ⌊b·deg f/m⌋` ⇒ `V₁=0, V₂=1, V₃=2`; E-part `= V₂`, new part `= V₁⊕V₃` (dim 2 = dim `A_new`).
  At `p ≡ 3 mod 4`, `𝒞|V₃ = 0` **twice, independently** — by degree (Step 3: `deg(x^a f^{(p-3)/4}) =
  (3p-5)/4 < p-1`, so no coefficient at the index `𝒞` reads) and by grading (Step 3′: `w³f⁻¹ = 1/w` ⇒
  `𝒞(V₃) ⊆ V₁ = 0`). Hence `a(A_new) = dim ker 𝒞 = 2 = dim A_new`.
- **Independent review (v2 §1).** Isolated reviewer, told it was not scored on problems found:
  *"the claim stands; all 8 checked items correct; no mathematical error."* Its own validated
  instrument matched point-count `p`-rank on **134 curves × 12 primes, 0 mismatches**, and it verified
  the operator dimension bookkeeping `dim V_b = ⌊b·deg f/m⌋` **by explicit divisor computation** for
  `(m,d) = (2,3),(3,4),(4,3),(5,3),(7,3)`.
- **Citations verified (v2 §2).** Oort Thm 2 + Rmk 3 (`a=g ⟺ superspecial`); Pries Prop 3.17
  (`g=2`: `p`-rank 0 ⟺ ss). Each with one caveat — the subject of §2.

**Exact-scale confirmation of the inputs at secp** (`p = 2²⁵⁶−2³²−977`, integer-only,
`RESULT_anew_..._v3` check-block):

| input | value at secp | needed |
|---|---|---|
| `p mod 4` | **3** | `3` (Cartier route: `4 ∣ p+1`) ✅ |
| `p mod 3` | **1** | `1` ⇒ `E : y²=x³+7` is **ordinary** at secp ✅ |
| `p mod 12` | **7** | in the `p ≡ 7 mod 12` family ✅ |
| `dim V₁,V₂,V₃` | `0,1,2` | new part dim 2 = dim `A_new` ✅ |

So the form-level derivation applies verbatim at secp, and `E` is ordinary there — the fact §2.1 uses.

---

## 2. The two v2 caveats are non-load-bearing for the downstream

### 2.1 Caveat 1 (conclusion is over `F̄_p`, not `F_p`) — a-fortiori fine for `Hom=0` and easy-DLP

The downstream consumers are **P13 `Hom(E, A_new) = 0`** and **Brick E's easy DLP in `A_new(F_p)`**.
Neither needs the `F_p` refinement:

- `Hom_{F_p}(E, A_new) ⊆ Hom_{F̄_p}(E, A_new)`. At secp `E` is **ordinary** (§1: `p ≡ 1 mod 3`), Newton
  slopes `{0,1}`; `A_new ⊗ F̄_p` is **supersingular**, slopes `{½,½}`. Disjoint slopes ⇒ no common
  isogeny factor ⇒ `Hom_{F̄_p}(E, A_new) = 0` ⇒ `Hom_{F_p} = 0`. The `F̄_p` statement is exactly the
  strength `Hom=0` requires; `F_p` follows for free. Caveat 1 does not weaken P13.
- Easy DLP / MOV embedding degree in `A_new(F_p)` is governed by `A_new`'s Frobenius **over `F_p`** (the
  `m`-support / M17 `k=3` result), and supersingularity-**over-`F̄_p`** is precisely the geometric fact
  that forces the embedding degree small. Caveat 1 does not weaken the Brick E enabler.

`[PROVED — standard slope disjointness; uses only the already-established F̄_p supersingularity + E
ordinary at secp (exact §1).]`

### 2.2 Caveat 2 (Pries Prop 3.17 assumes principal polarization) — the pp route is REDUNDANT

v2 §3 Step 5 reached supersingular by `a=2 → superspecial → p`-rank 0 `→(Pries, g=2)` supersingular,
and only that **last** link carries the pp assumption. That link is unnecessary:

> `a(A_new)=2=g ⟹ A_new ⊗ F̄_p` **superspecial** (Oort Thm 2 + Rmk 3 — already citation-verified in v2,
> whose caveat is *`F̄_p`, not pp*) `⟹ A_new ⊗ F̄_p ≅ E₁ × E₂` with each `Eᵢ` **supersingular** `⟹` all
> Newton slopes `= ½` `⟹ A_new` **supersingular**.

`superspecial ⟹ supersingular` is the definitional implication (a product of supersingular elliptic
curves is a supersingular abelian variety; isomorphism ⇒ isogeny). It needs **no polarization** and
**no Pries**. So the pp hypothesis never enters the chain we use, and **Caveat 2 dissolves.** The
`p`-rank/Pries route survives only as an alternative longer path.

`[PROVED — citation-verified against the original source (2026-08-20).]` An isolated `citation-verifier`
read Oort 1975 (*Math. Ann.* 214, p. 35) verbatim from the Göttingen GDZ scan: **Theorem 2** hypotheses
are exactly *k algebraically closed · X an abelian variety of dim g · a(X)=g* — **no polarization, no
principal polarization**; a(X)=dim_k Hom(α_p,X) is a p-divisible-group invariant and the conclusion is
an isomorphism of abelian varieties with no polarization compatibility asserted. The "principally
polarized" wording in Achter–Pries (arXiv:1403.0023) is that paper's standing ppav *setting*, not a
hypothesis of Thm 2 — confirmed by their own Def 3.1(4) ("decomposition … as an abelian variety without
polarization"). `superspecial ⟹ supersingular` is definitional (isomorphic-to-product ⇒ isogenous-to-
product; Karemaker Def 1.15, Xue–Yang–Yu, Achter–Pries), polarization-free. Our non-principally-polarized
`A_new` over `F̄_p` is within scope of both. **Caveat 2 does not attach to the Oort route.**

**This resolves the paste's open item 4 (Pries pp caveat):** it is load-bearing only for a route we do
not take.

---

## 3. Aug-18 reconciliation — an item-level under-count, corrected

`ANALYSIS_zeta4_cartier_manin_ideas_improvements_v1.md` (Aug-18) proposed the Cartier–Manin degree
argument as a *third route, "pending the single operator-identity check"* — *"confirm the vanishing
coefficient IS the actual `A_new` Cartier entry for `dx/w³, x·dx/w³` … the operator bookkeeping is the
piece to make rigorous."* That check was **already discharged on 2026-08-02**:

- the "operator bookkeeping" is v1 §3 Steps 2–3 + Step 3′ (the coefficient the degree count kills **is**
  the Cartier entry, by the grading `𝒞(V₃) ⊆ V₁`), and
- it was validated by the v2 reviewer's explicit-divisor computation of `dim V_b` (C3, 311/311) and the
  `(m,d)` cases, and cross-checked by C1 (Manin `Tr(M) ≡ p+1−#C(F_p) mod p`, 311/311).
- `cartier_manin_idea_check_v1.py` (Aug-18) re-confirmed a Hasse–Witt coefficient that **C1 already
  covered**.

No new gap existed; the Aug-18 framing lost the Aug-02 `[PROVED-reviewed]` position and re-listed a
discharged check as open. Logged per `feedback_verify_external_critiques` (trace items, not tags): the
frontier's true position — **proved, three routes** (ζ₄-twist §XI.19; character-sum/Stickelberger v9;
Cartier v1 §3) — was intact; the ledger presentation degraded. **`A_new` supersingular at every
`p ≡ 3 mod 4` is held via three independent routes, one of them reviewed.**

---

## 4. Net for the two-prong

- **Prong 1 (the enabler) is complete.** N2 — `A_new` supersingular at secp, the dim-2 extrapolation
  every downstream secp claim quotes — is **discharged for the uses Prong 2 makes**: `[PROVED — reviewed,
  three routes]`, with both v2 caveats shown non-load-bearing (§2). The form-level derivation is
  banner-admissible (a proof, not a measured null), so it transfers to secp; §1 confirms its inputs
  hold there exactly.
- **`Hom(E, A_new) = 0` / P13 / Route-2 "blocked"** now rests on a reviewed derivation whose caveats
  do not bite. This is stronger than v2's "reviewed, two caveats open" and closer to the
  `PROJECT_SUMMARY` line v2 flagged; the remaining daylight is the light §2.2 independent check.
- **Prong 2 (Brick E) is unblocked.** Its enabler (easy DLP in a supersingular `A_new`, MOV `k=3`) is
  on established ground. Next action: `experiment-designer` pre-registration of the `c(d)`-degree
  measurement (mandatory gate — it is a leakage test), then the run at `p=43` over the full group,
  with the planted-degree-2 firing control and the shuffled-fibre matched null. Exact integer
  arithmetic only.

## 5. Honesty ledger / owed gates

- `[PROVED — reviewed]`: `A_new` superspecial/supersingular over `F̄_p`, all `p ≡ 3 mod 4` (v1 §3 + v2).
  Unchanged; not re-promoted here.
- `[PROVED]` §2.1 (Caveat 1 a-fortiori): standard slope disjointness on already-established inputs.
- `[PROVED — citation-verified]` §2.2 (Caveat 2 redundant): the owed check is **discharged**
  (2026-08-20) — `citation-verifier` read the original Oort 1975 text and confirmed Thm 2's a=g ⟺
  superspecial and superspecial ⟹ supersingular are both polarization-free. No **new** citation is
  introduced — the reduction *removes* reliance on Pries. **Both v2 caveats are now resolved.**
- Measured rows (287/311 classes, etc.) carry **no** secp power; the scale banner stands. Only the
  form-level derivation + §2 arguments reach secp.
- `compile-diff` owed before any of this is folded into a master/handover.

*Predecessors: `RESULT_anew_supersingularity_step3_gap_and_cartier_route_v1.md`, `..._v2.md`,
`ANALYSIS_zeta4_cartier_manin_ideas_improvements_v1.md`. Feeds: `PROJECT_SUMMARY` N2 line; Brick E
prereg (next).*
