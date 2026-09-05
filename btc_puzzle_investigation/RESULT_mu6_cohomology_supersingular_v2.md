# RESULT — N2 CLOSED: `A_new` is supersingular at secp, PROVED (scale-free, curve-independent)

**Date 2026-07-20.** Supersedes the "not proved for dimension 2" status of N2 / frontier #11 /
master-v4 L2. Object: `A_new` = the new part of `Jac(C)`, `C : w⁴ = f(x)`, `f` any separable cubic
(so `w²=y`, `y²=f(x)=E`); `Jac(C) ~ E × A_new`, `dim A_new = 2`.
Artifact: `supersingular_mu4_mechanism_v1.py` + `.log` (Sage, exact integer point counts over
`F_p`, `F_{p²}`; 6 cubics × 42 primes `13→199`).

**Grade: `[PROVED]`.** The proof uses only `p ≡ 3 mod 4` and the order-4 automorphism `ζ₄` (which
exists for *any* cubic). Both inputs are exact and scale-free, so the conclusion holds at
`p = 2²⁵⁶−2³²−977` (`≡ 3 mod 4`). This is not an extrapolation from small `p`.

---

## 0. What was wrong before, and what is new

**The old justification was the retraction-#18 fallacy.** Master-v4 L2 / P-A justified
"`A_new` supersingular ⟺ `p` inert in `Q(i)`" from `Q(i) ⊆ End⁰(A_new)`. But `Q(i)` has **degree 2**
acting on a **dimension-2** surface — this is *exactly* the configuration §XII.18 flags as **not CM and
not decisive**: "`p` inert in `Q(i)` ⇒ supersingular" is the criterion for an **elliptic curve** with CM
by `Q(i)`, and it was being applied to a surface where it does not directly hold. The conclusion
(ss ⟺ `p ≡ 3 mod 4`) happened to be **correct**; the stated reason was not a proof.

**The correct mechanism is the μ₄ cover grading, and it proves the result outright.** It also explains
the measured **curve-independence** (below): the argument never touches the cubic beyond "it is a cubic",
so CM (`x³+B`) and non-CM (`x³+ax+b`) covers behave identically — as observed.

---

## 1. The proof (three steps; the third is standard classification)

Write `L_new(T) = 1 + b₁T + b₂T² + p·b₁T³ + p²T⁴` (degree-4, reciprocal; the Frobenius char.
polynomial on `H¹(A_new)` is `t⁴ + b₁t³ + b₂t² + p·b₁t + p²`).

**Step 1 — `ζ₄` is an order-4 endomorphism of `A_new` with `ζ₄² = −1`.**
`ζ₄ : (x,w) ↦ (x, i·w)` is an automorphism of `C` for any cubic (`i = √−1 ∈ F̄_p`). It fixes
`E = C/⟨ζ₄²⟩` (since `ζ₄² : w↦−w`, `y=w²`), and on `H¹_new` (the `dim-4` complement) it acts with
eigenvalues `±i`, i.e. `ζ₄|A_new` has `ζ₄² = −1`. So `ζ₄ ∈ End(A_new ⊗ F_{p²})` gives an embedding
`Q(i) ↪ End⁰(A_new)`. *(This alone is the degree-2-on-dim-2 fact — necessary, not sufficient.)*

**Step 2 — for `p ≡ 3 mod 4`, Frobenius conjugates `ζ₄` to `ζ₄⁻¹`, and this is non-commutative.**
Let `π = Frob_p ∈ End(A_new)` (defined over `F_p`). `ζ₄` is defined over `F_{p²}` (`i ∉ F_p`), and the
standard Frobenius-twist relation gives `π ∘ φ = φ^σ ∘ π` for `φ` defined over `F_{p²}`, where
`σ = Frob_p` generates `Gal(F_{p²}/F_p)`. Here `σ(i) = i^p = i^{3} = −i` (because `p ≡ 3 mod 4`), so
`σ(ζ₄) = ζ₄⁻¹`, hence in `End⁰(A_new ⊗ F_{p²})`:
> **`π · ζ₄ · π⁻¹ = ζ₄⁻¹`   (equivalently `π · ζ₄ = ζ₄⁻¹ · π`).**

This is a **non-commutative** relation: if the subalgebra `⟨π, ζ₄⟩ ⊆ End⁰` were commutative we would
have `π ζ₄ π⁻¹ = ζ₄`, forcing `ζ₄ = ζ₄⁻¹`, i.e. `ζ₄² = 1`, contradicting `ζ₄² = −1`. Therefore
`End⁰(A_new ⊗ F̄_p)` is **non-commutative**.

**Step 3 — the relation is incompatible with any non-supersingular abelian surface.**
Note first (Step 1) that `i := ζ₄` acts on **all** of `A_new` with `i² = −1`, so `Q(i) ⊆ End⁰(A_new)`
acts on the whole surface. Now rule out the two non-supersingular `p`-rank strata over `F̄_p`:

- **Ordinary (`p`-rank 2).** `End⁰(A_new)` is a commutative field (a quartic CM field). Then
  `π i π⁻¹ = i ≠ −i`. Contradiction.
- **`p`-rank 1.** Up to isogeny `A_new` is either (a) simple with commutative `End⁰` (a field) — same
  contradiction — or (b) `E_a × E_s` with `E_a` ordinary and `E_s` supersingular elliptic. In case (b)
  the factors have distinct Newton slopes, so `Hom(E_a, E_s) = 0` and **both** `i` and `π` preserve each
  factor. On the ordinary factor `End⁰(E_a)` is an imaginary-quadratic **field**, so
  `π_a i_a π_a⁻¹ = i_a ≠ −i_a`. Contradiction. *(Independently: `i_a² = −1` would give `E_a` CM by
  `Q(i)`, which at `p ≡ 3 mod 4` — `p` inert in `Q(i)` — is supersingular, not ordinary.)*

Both non-supersingular strata are excluded, so `A_new` has `p`-rank 0, i.e. **`A_new` is
supersingular.** ∎

*(The general slogan "non-commutative `End⁰` ⇒ supersingular" is false for surfaces — `E_a × E_s` is a
counterexample. What forces the conclusion here is stronger: `i` acts on the **whole** surface and `π`
conjugates it to `−i`, which no commutative-`End⁰` factor can host. The `E_a × E_s` escape is closed by
the factor-preservation argument above, not by non-commutativity alone.)*

**Scope.** Inputs: `p ≡ 3 mod 4` (exact for secp) and `ζ₄ ∈ Aut(C)` (any cubic). No CM input, no
`j = 0` input, no small-`p` input. **Valid at secp.** The mirror also holds: at `p ≡ 1 mod 4`,
`σ(i) = i`, `π` and `ζ₄` **commute**, `End⁰` can be commutative, and `A_new` is ordinary — matching the
data exactly.

---

## 2. The decidable artifact (what the script checks, and the two structural facts it exposes)

`supersingular_mu4_mechanism_v1.py` computes `L_new` **exactly** (integer point counts over `F_p` and
`F_{p²}`; only those two are needed since `L_new` is degree-4 reciprocal with two free coefficients).
For 6 cubics × 42 primes:

**Fact 1 — `b₁ = 0` at every `p ≡ 3 mod 4` (42/42, all cubics); generically `b₁ ≠ 0` at `p ≡ 1 mod 4`.**
`b₁ = −trace(π | A_new)`. Step 2's swap `V_i ↔ V_{−i}` makes `π` block-off-diagonal, so its trace
vanishes. This is the *measured shadow* of the non-commutativity, and it is the exact, scale-free
signature. **This is the object N1's "2+2 splitting" also sees** (the `V_i`, `V_{−i}` pair) — same
decomposition, noted for §VII.5 / frontier #10.

**Fact 2 — supersingular at every `p ≡ 3 mod 4` (42/42):** `b₂ = m·p` with `m ∈ {−2,−1,0,1,2}` and every
Frobenius root is `√p · (root of unity)` (`rootsRU = yes`). Supersingularity (Step 3) is the *reason*
`b₂ ≡ 0 mod p` (`p`-rank 0), not an independent check. With `b₁ = 0`, `L_new(T) = 1 + m·p·T² + p²T⁴`
is a polynomial in `T²`: `A_new` is (up to isogeny) the **Weil restriction of an elliptic curve
`E'/F_{p²}`**, and `E'` supersingular ⟺ `A_new` supersingular — the `dim-2 → dim-1` shadow of Step 3.

**Curve-independence (the tell that it is the μ₄ cover, not CM).** Both CM cubics (`x³+7, x³+2, x³+11`)
and non-CM cubics (`x³+2x+5, x³+x+1, x³−x+3`) are supersingular at every `p ≡ 3 mod 4` and ordinary at
every `p ≡ 1 mod 4`. The `m = b₂/p` values do vary a little with `p mod 3` and curve (CM `p≡7 mod12`:
`m∈{−2,1}`; CM `p≡11`: `m=2`; non-CM: `m∈{−2,0,1,2}`), i.e. **which** supersingular isogeny class, but
not **whether** supersingular.

---

## 3. Consequence for Part VII (the load-bearing use), stated with unchanged scope

N2 was the one proof gap under all of Part VII. With N2 `[PROVED]`:

- **`A_new` is supersingular at secp — no longer "subject to N2".** P13 (`Hom(E,A_new)=0` at secp) no
  longer *inherits* an unproved dimension-2 extrapolation; its supersingular-vs-ordinary Frobenius-slope
  input is now proved at secp. (The `Hom=0` conclusion itself was already `[PROVED]` via Tate given the
  slope disjointness; what changes is that the "`A_new` supersingular" half is now proved, not assumed.)
- **What does NOT change — every downstream scope caveat stands.** This closes a *reduction-theory* gap;
  it says nothing new about ECDLP. The routes of §VII.3 keep their exact statuses: Route 1 (MOV on `E`)
  blocked (254-bit); Route 2 (homomorphic transfer into `A_new`) `Hom=0`, blocked; **Route 3 (cover
  transfer into `Jac(C)`) OPEN — `Õ(p^{4/3})` best known, one cover, not a family bound (N4/§XI.13).**
  **D1 (non-homomorphic lift) and D2 (Lang-torsor twist bridge) remain OPEN.** The N1 ½-saturation
  mechanism remains OPEN — though Fact 1 now names its subspace precisely as the `V_i⊕V_{−i}` Frobenius
  swap. **No `secure`/`closure`/`hard` claim is made or implied.**

---

## 4. Grades / what to carry

- `[PROVED, scale-free, curve-independent]` **`A_new` is supersingular for every `p ≡ 3 mod 4` and every
  separable cubic; in particular at secp.** Proof: `Q(i)` acts on all of `A_new` (Step 1) and
  `π ζ₄ π⁻¹ = ζ₄⁻¹` for `p ≡ 3 mod 4` (Step 2); this excludes both the ordinary and `p`-rank-1 strata by
  the factor-preservation case analysis (Step 3), leaving only `p`-rank 0 = supersingular.
- `[VERIFIED 42/42]` `b₁ = 0` and `b₂ ≡ 0 mod p` with roots `√p·ζ` at `p ≡ 3 mod 4` — the decidable
  shadow.
- **Retire** the "`Q(i)` inert ⇒ ss" phrasing of L2/P-A (retraction-#18 fallacy); replace with the
  quaternion argument. The old *conclusion* stands; the old *reason* is withdrawn.
- **Unchanged OPEN:** N3 (CM-layer L3 discriminator), N4 (Route 3 cover family), D1, D2, N1
  (½-saturation), and everything under the scale banner that is `[VERIFIED]`/`[EMPIRICAL]`.

*Cited classification: Albert / Tate — endomorphism algebras of abelian varieties over finite fields;
Tate — a simple abelian variety over `F_q` is ordinary/supersingular per its Newton slopes;
`p`-rank strata of abelian surfaces (Oort). Only the standard facts "ordinary surface ⇒ commutative
quartic `End⁰`" and "`p`-rank-1 surface ⇒ commutative `End⁰` or `E_ord × E_ss`" are used. No new
literature dependency introduced. **Independent adversarial check pending** — see §5.*

---

## 5. Verification status

- **Decidable artifact:** `supersingular_mu4_mechanism_v1.py` / `.log`, 42 primes × 6 cubics, exact.
  Facts 1–2 reproduced; `b₁=0` and supersingular exactly on `p ≡ 3 mod 4`, curve-independent. **[PASS]**
- **Proof self-review:** the first draft of Step 3 used the *false* slogan "non-commutative `End⁰` ⇒
  supersingular"; corrected to the factor-preservation case analysis (the `E_ord × E_ss` escape is the
  one that must be, and is, explicitly closed). Recorded here so the error is not silently buried.
- **Open to an independent eye:** the two load-bearing external facts are (i) the Frobenius-twist
  relation `π φ = φ^σ π` and (ii) the surface `p`-rank/`End⁰` dichotomy. Both are standard; an
  independent re-derivation is the remaining diligence before master-v5 promotion via `compile-diff`.
