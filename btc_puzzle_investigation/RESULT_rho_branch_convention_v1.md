# RESULT — the ρ-branch is a sorting convention composed with p mod 4; brick 1B carries no
# information beyond e₄ = p². Brick 2 SURVIVES the same audit and reduces to one elementary identity.

**Date 2026-09-01. Grade: `[PROVED — algebraic derivation + exact measurement + pre-registered OOS
confirmation]` for the deflation; `[VERIFIED — 312/312 cells, 5 primes]` for the brick-2 reduction.**

Scripts (all pass `check_no_float.py`): `rho_artifact_probe_v1.sage` (hypothesis FALSIFIED — kept as
record), `rho_artifact_probe_v2.sage` (refined, confirmed), `rho_f_criterion_v1.sage`,
`rho_oos_163_v1.sage` (+`.log`), `rho_galois_obstruction_v1/v2.sage` (+`galois_61.log`,
`galois_79.log`), `brick2_identity_v1.sage` (+`.log`), `brick2_converse_v1.sage` (buggy — `leg` left
free; kept as record) and `brick2_converse_v2.sage` (corrected).
Audits: `RESULT_lmono_brick1_gkr_inputs_v1.md` §2, `RESULT_lmono_brick2_tensor_shadow_v1.md`,
`PLAN_lmono_monodromy_campaign_v1.md` §4.

---

## 1. The claim under audit

`RESULT_lmono_brick1_gkr_inputs_v1.md` §2: the branch `ρ(a) ∈ {ζ₃, ζ̄₃}` is *globally constant per
prime*, hence "a named new prime-level invariant `ρ_p`", "the tensor glue is prime-rigid", "a
stronger rigidity than brick 2's per-cell statement"; values 1/2/1 at p=43/61/79 "suggest a possible
p mod 4 dependence"; named follow-up: connect `ρ_p` to the `Q(√p, ζ₃)` embedding sign.

The branch is computed in `lmono_brick1_branch_v2.sage` by

```python
def canon(facs):
    return sorted(facs, key=lambda f: tuple(tuple(c.vector()) for c in f.list()))
```

— a lexicographic sort on power-basis coordinate vectors, with `f.list() = [u, −s, 1]`, constant
coefficient **first**.

## 2. Global constancy is FORCED, not measured

Write the two `[2,2]` factors `g₁ = T²−s₁T+u₁`, `g₂ = T²−s₂T+u₂`. Brick 2 gives `s₂ = ρs₁`,
`u₂ = ρ²u₁`. Vieta gives `u₁u₂ = e₄ = p²`, and `e₄ = Kn(p**2)` is **cell-independent** by
construction. Hence

    ρ²u₁² = p²  ⇒  u₁ = ε·p·ρ⁻¹,  u₂ = ε·p·ρ,   ε = ±1

so for *every* cell `a`, independently of `a`,

> **{u₁, u₂} = {ε·p·ζ₃, ε·p·ζ₃²}**, with `ε = ±1` the only free quantity.

Since `u₁ ≠ u₂` always, `canon()` **never reads past the constant coefficient** — and the constant
coefficients do not depend on the cell. Therefore the branch is *forced* constant across cells. The
"prime-rigidity of the tensor glue" is a restatement of `e₄ = p²`.

**Measured (exact), `rho_artifact_probe_v1/v2.sage`:** at p=43 (3 cells), p=61 (3), p=79 (3), p=163
(1) — `{u₁,u₂} = {εpζ₃, εpζ₃²}`, `u₁u₂ = p²`, `u₁ ≠ u₂`: **10/10 cells**.

## 3. ε = leg — the functional equation, not a new sign

`rho_artifact_probe_v1.sage` pre-registered the rule "ε uniform"; it predicted branch 1/1/1 and was
**FALSIFIED at p=61** (observed 2). The refined and correct statement is

> **ε = leg = (−1)^((p−1)/2)**, entering through `e₃ = leg·p·e₁` in `build_L`.

Measured directly: p=43 → ε=−1, p=61 → ε=+1, p=79 → ε=−1, p=163 → ε=−1. **10/10, `ε == leg` in
every case.** This is not an independent fact: `αᾱ = p` gives `e₃ = p·ē₁`, so `e₃ = leg·p·e₁` is
exactly the functional equation `ē₁ = leg·e₁` (e₁ real for `p ≡ 1 mod 4`, purely imaginary for
`p ≡ 3 mod 4`).

## 4. The lex tiebreak is n-inert

Define `F(n)` = the branch predicted under `ε = −1` from the field alone. Because `vec(−v) = −vec(v)`
reverses lex order at the first differing coordinate, `branch(ε=+1) = 3 − branch(ε=−1)` identically.

`ζ₃² = −1 − ζ₃` ⇒ `vec(ζ₃²) = −e₀ − vec(ζ₃)`, so the comparison is decided at coordinate 0:

> **`F(n) = 1  ⟺  v₀(ζ₃) ≤ −1`** in the power basis of `Q(ζ₁₂ₙ)`.

`rho_f_criterion_v1.sage`: over **89 values of n** (5–129 plus the curve orders 139, 147, 199, 208,
219, 243, 252, 259, 313, 327, 364; prime and composite), the identity holds, and
**`v₀(ζ₃) = −1` in every single case** ⇒ `F(n) = 1` identically. The tiebreak carries no arithmetic.

## 5. The law, and the pre-registered out-of-sample confirmation

Combining §2–§4:

> **branch = 1 ⟺ p ≡ 3 (mod 4);  branch = 2 ⟺ p ≡ 1 (mod 4).**

In-sample: reproduces 43→1, 61→2, 79→1 (3/3). **This rule was fitted post-hoc on those three points**
— it is worth exactly one degree of freedom until tested out of sample.

**OOS (pre-registered in `rho_oos_163_v1.sage` before the run, and before the in-flight
`lmono_brick1_branch_v2` job reached p=163):** p=163 ≡ 3 mod 4 ⇒ predicted branch **1**, ε **−1**.

```
p=163 n=139 deg(K)=552 leg=-1 | PREDICTED branch=1, eps=-1
  a=1: MEASURED branch=1 eps=-1 | u1*u2==p^2 ? True | PREDICTION CONFIRMED [652s]
```

**CONFIRMED.** The record's conjectured "p mod 4 law" is real and is *entirely* `χ₂(−1)` composed
with a sorting convention. `ρ_p` is not a new invariant.

## 6. The obstruction is structural: no `Q(ζ_n)`-rational labeling exists

`L*(a)` has coefficients in `Q(ζ_n)`; it splits `[2,2]` only over `K = Q(ζ₁₂ₙ)`. So
`Gal(K/Q(ζ_n)) = {z ↦ z^j : j ≡ 1 mod n, j ∈ (Z/12)*}`, of order 4, acts on the factor pair.
Applying σ to `roots(g₂) = ρ·roots(g₁)` forces `σ(ρ)·ρ = 1`, i.e. **every swapping σ inverts ζ₃**.
Predicted: stabiliser `= {j ≡ 1, 7 mod 12}` (the ζ₃-fixing subgroup), swappers `= {j ≡ 5, 11}`.

Measured (`rho_galois_obstruction_v1/v2.sage`), p=43 (3 cells), p=61, p=79 — **5/5 cells**:

```
{1: 'fix', 5: 'swap', 7: 'fix', 11: 'swap'}   prediction CONFIRMED
```

> **Half of `Gal(K/Q(ζ_n))` swaps the two planes.** Therefore no `Q(ζ_n)`-rational rule can label
> them. `ρ_p` is not "un-canonicalised pending better work" — it is **structurally
> un-canonicalisable from the L-polynomial data**. Any labeling of `W` vs `W⊗ψ` must break Galois,
> i.e. must come from the sheaf side.

This *promotes route B* by elimination: the sheaf isomorphism `W′ ≅ W⊗ψ` is not merely one route to
the labeling — it is the only place the labeling can live.

## 7. Brick 2 audited by the same method: it SURVIVES — and the reduction is ALREADY BANKED as M21

> **PRIORITY CORRECTION (same session).** The reduction below is **not new**. It is
> `POSITIVE_FINDINGS_MASTER_v12` **M21** (`e₂ = e₁²−χ₂(−1)p ⟺ V₂ = V₁²−2χ₂(−1)p`, exact at
> **1171 μ₆-orbit cells across 11 primes 43≤p≤1303**, certified by exact integer convolution
> `f = h₂ − h₁⋆h₁` at 9 primes), together with **P16** (the twist-discriminator PASS is
> *algebraically equivalent* to that scalar identity — "necessary-not-sufficient for
> `H¹≅W⊕W⊗ξ`, NOT an independent 4-dim confirmation"), and the open mechanism question is
> already logged as **N8**. My 312 cells is **less** evidence than what was banked on 2026-08-17.
> I re-derived it because M21 sits at line ~1400 of a 1671-line master that the v13–v18 delta
> chain does not surface. This is logged as the motivating instance for `CLAIMS.md`.
>
> **What survives as new in this section:** (a) the **converse**, verified symbolically — the
> `[2,2]`-with-ρ-rescaling structure is *equivalent* to the identity, not merely implied by it
> (consistent with P16 and sharpening what brick 2's PASS certifies); (b) the **cost finding** —
> brick 2 spent degree-240–792 factorisations on 7 cells to re-measure M21, which the convolution
> route settles exactly and instantly; (c) the ARM-3 decomposition-group result. The `V₂` identity
> itself is M21 and must be cited as M21.

The failure mode that killed 1B is "an observable that re-encodes a forced identity." Brick 2 was
audited for the same defect. It does not have it — and the audit produced a sharper form of it.

**Derivation.** If `roots(L*) = S ∪ ρS` with `ρ³ = 1, ρ ≠ 1`, and `σ₁, σ₂` are the elementary
symmetrics of `S`, then `e₁ = −ρ²σ₁`, `e₄ = ρ²σ₂²`, `e₃ = −σ₁σ₂`, `e₂ = ρ(σ₁²−σ₂)`. Eliminating
`σ₁, σ₂`:

| condition | status |
|---|---|
| `e₃² = e₄·e₁²` | **automatic** from `e₃ = leg·p·e₁`, `e₄ = p²` — carries no information |
| `e₂ = e₁² − leg·p` | the **only** non-automatic condition |

and `e₂ = (V₁²+V₂)/2`, `e₁ = −V₁` turn the second into

> ### **T2 at finite level  ⟺  V₂ = V₁² − 2·leg·p**   ← this is **M21** (v12), not a new result

**Converse verified symbolically** (`brick2_converse_v2.sage`): with `e₁ = t` and `p` free
indeterminates and `leg = ±1` a constant, `g₁·g₂ − quartic ≡ 0` identically in `(t,p)` for all four
`(leg, ρ)` combinations. So the implication runs both ways — nothing is left over.
(`brick2_converse_v1.sage` left `leg` as a free indeterminate, so `leg² ≠ 1` symbolically and it
returned a spurious `False`; kept as record.)

**Measured** (`brick2_identity_v1.sage`), all cells, exact, no field factorisation:

| p | n | leg | `V₂ = V₁²−2·leg·p` | `e₃²=e₄e₁²` |
|---|---|---|---|---|
| 43 | 31 | −1 | **30/30** | 30/30 |
| 61 | 61 | +1 | **60/60** | 60/60 |
| 67 | 79 | −1 | **78/78** | 78/78 |
| 79 | 67 | −1 | **66/66** | 66/66 |
| 97 | 79 | +1 | **78/78** | 78/78 |

**312/312 cells, 5 primes, both `leg` arms — in under a second** (an independent re-confirmation of M21's 1171 cells, not an extension of them), against brick 2's 7 cells obtained
by factorisations over fields of degree 240–792. The `e₃²=e₄e₁²` column is 100% as predicted, i.e.
confirmed inert.

**Is the identity itself automatic?** Not from the constraints tested here (`e₃ = leg·p·e₁`,
`e₄ = p²` leave `e₂` free). Supporting evidence that `u₁ ∈ p·μ` is a genuine measured fact:
purity + CM gives `u₁·c(u₁) = p²`, so `u₁/p` is an algebraic integer iff complex conjugation lies in
the decomposition group at `p`, i.e. iff `−1 ∈ ⟨p⟩ mod 12n`. Measured (`brick2_identity_v1.sage`
ARM 3): **`−1 ∉ ⟨p⟩` at all 9 testable primes** (43, 67, 79, 97, 103, 139, 151, 163, 211; p=61 and
p=127 are anomalous, `n = p`, so `p | 12n` and the test is N/A). So it is *not* forced by purity.

> **This is N8, already open since v12 — restated here with the converse attached.** `V₁` and `V₂` are explicit
> twisted character sums over `E(F_p)` and `E(F_{p²})`. If `V₂ = V₁² − 2·leg·p` is a formal identity
> in `(h₁, h₂)` — it has the shape of a Hasse–Davenport / Frobenius-square relation — then **T2's
> entire finite shadow becomes a theorem outright**, with no GKR rigidity and no sheaf isomorphism
> required. That is a cheaper route to the finite statement than either route A or route B, and it
> was invisible while the observable was buried under degree-792 factorisations.

## 8. Closure statement (to the project's own burden of proof)

**Object closed:** the branch observable as computed by `canon()` in `lmono_brick1_branch_v2.sage`,
the `ρ_p`-as-new-invariant claim, and the conjectured `p mod 4` law.
**Class of observable closed:** any labeling of the two ζ₃-conjugate planes derived from `L*(a)` by a
`Q(ζ_n)`-rational rule (§6 — a theorem, not a failed search).
**Power/scope:** derivation is exact and complete; measurements are exact at 10 cells (u-structure),
5 cells (Galois), 89 values of n (tiebreak), 1 pre-registered OOS point (p=163).

**NOT closed by this document:**
- Brick 2 / T2 — *strengthened*, not closed. §7 assumed it to derive §2, then re-derived it in
  sharper form and extended it 7 → 312 cells.
- The S-visibility question (lead 2) — untouched and now *free-standing*.
- The centralizer conjecture — unharmed as a conjecture; its advertised explanatory reach loses one
  item (§9).
- `dim H¹_c = 4`, purity (N31), the ω-descent, the moment table, non-abelianity — all untouched.

## 9. Regrades proposed for the record

1. **`RESULT_lmono_brick1_gkr_inputs_v1.md` §2** — `[VERIFIED — new prime-level invariant]` →
   **`[RETRACTED — forced by e₄=p² composed with a lex convention; the value is χ₂(−1)]`**. Part A
   (the moment table) is untouched and stands.
2. **Same doc §3** — "the finite evidence is now maximal / cannot get sharper" → **false**. With 1B
   vacuous the finite shadow is brick 2 + descent + ω-descent; and §7 has just made it sharper.
3. **Same doc §3, named follow-up** — "connect `ρ_p` to the `Q(√p, ζ₃)` embedding sign / the
   automatic-√p witness" → **VOID** (§6: no such connection can exist downstream of `L*`).
4. **`PLAN_lmono_monodromy_campaign_v1.md` §4** — the centralizer conjecture is credited with
   explaining four things at once, the fourth being "the S-visibility embedding-sign texture (same
   character)." **Drop the fourth.** `ρ_p = χ₂(−1)`; S-visibility already provably fails the plain
   Legendre law and lives on `ℓ mod 12`. They were never the same character. The conjecture stands;
   the reach used to prioritise routes A/B shrinks by one item.
5. **Not a new open item — this is `N8`** (v12 A.3, "Why does `e₂=e₁²−χ₂(−1)p` hold?"). What this
   session adds to N8: the converse (the identity is *equivalent* to the ρ-rescaling structure, not
   just implied), and the observation that a Hasse-Davenport / Frobenius-square route on
   `hist_k1`/`hist_k2` would close it. **N8 was invisible to this session until the CLAIMS.md
   compile surfaced it** — see §10.

## 10. Discipline notes

- **The generalisable defect.** `canon()` sorts on power-basis coordinate vectors, and the power
  basis differs across primes (`m = 12n` varies). **Cross-prime comparison of such labels is not
  well-defined a priori**; it was stable here only because `v₀(ζ₃) = −1` uniformly. Standing rule
  proposed: *an observable defined through a sorting or labeling convention on field elements must be
  audited for convention-dependence before any of its values are interpreted.* This one passed
  through a session that caught two other analysis-layer bugs.
- **Small-n pattern fitting.** The law was conjectured from 3 primes with one distinguishing value.
  It was real — and trivial. Three points is enough to notice a pattern and never enough to grade it.
- **Falsification record kept.** `rho_artifact_probe_v1.sage` (wrong rule) and
  `brick2_converse_v1.sage` (wrong symbolic setup) are retained deliberately.
- **The disease, caught in-session.** M21/P16/N8 were re-derived from scratch in §7 because the
  master's standing ledger (`v12` PART A) is buried at line ~305–393 of a 1671-line document and the
  v13–v18 *delta* chain never re-surfaces it. Cost here: a redundant derivation. Cost to the L-MONO
  campaign: seven degree-240–792 factorisations to re-measure a 1171-cell banked identity. This is
  the motivating instance for `CLAIMS.md` (single mutable ledger + `check_ledger.py` guard).
- **Pre-existing gap, minor:** `check_no_float.py` flags un-noted true division in
  `lmono_brick1_branch_v2.sage.py` (line 20) and `lmono_brick2_tensor_shadow_v1.sage.py` (line 23) —
  both are the exact `(V1**2+V2)/2` in a Sage cyclotomic field, i.e. false positives of the guard,
  but the rule requires the note. The nine scripts landed with this result carry it.
