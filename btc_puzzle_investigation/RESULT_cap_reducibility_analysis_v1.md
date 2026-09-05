# RESULT — is the CAP `|V(a)| ≤ 2√p` a theorem, a reduction, or a gap? A reducibility analysis

*2026-07-24. Derivation + literature only (no experiments beyond exact grounding checks of
already-proved algebra). Inputs taken as PROVED per the task and the record:
`weil_deligne_character_bound_v1.md §6′`, `RESULT_weight1_proved_v1.md`,
`RESULT_mu4_eigenvalue_individual_v1.md`, `RESULT_anew_isogeny_type_correction_v1.md`,
`RESULT_n1_phase_cap_v3.md`, `kohel_shparlinski_ants4_2000.pdf`.*

**No leakage, key-recovery, or ECDLP claim. This is a structural question about the analytic size of
one character sum; the CAP makes the readout *less* concentrated than its dimension permits.**

---

## 0. Objects, in one place (all PROVED upstream; not re-derived)

`E: y²=x³+7 / F_p`, `p≡1 mod 3`, `p≡3 mod 4`, `n=#E(F_p)` prime; `d↔P` the iso `Z/n ≅ E(F_p)`.
For `a≠0`:

> `V(a) = Σ_{P∈E(F_p)} χ₂(y_P)·χ_a(P) = −Tr(Frob_p | H¹_c(U, F))`,  `F = L_{χ₂(y)}⊗L_{χ_a}`, `dim H¹_c = 4`.

- Four Frobenius eigenvalues, **exactly** weight 1 (`|α_i| = √p`) — PROVED all `p`.
- Multiset closed under `α ↦ −ᾱ` (from `P↦−P`) — PROVED-FORCED. Forces the pairing into
  `√p·{e^{iθ₁}, e^{i(π−θ₁)}, e^{iθ₂}, e^{i(π−θ₂)}}`.
- Hence `P(t)=det(t−Frob)=(t²−β₁t−p)(t²−β₂t−p)`, `β_j = 2i√p·sinθ_j` **purely imaginary**, each
  quadratic of root-product `−p`. `e₁ = β₁+β₂ = −V(a)`; `e₂ = β₁β₂−2p`; all `e_i ∈ Z[ζ_n]`.

> **CAP:** `|V(a)| ≤ 2√p`  ⟺  `|sinθ₁+sinθ₂| ≤ 1`  ⟺  `|β₁+β₂| ≤ 2√p`  ⟺  `|e₁| ≤ 2√p`.

**Grounding of the load-bearing pieces** (exact-arithmetic, `capchk.py`; `p ≡ 1 mod 3`, `≡ 3 mod 4`,
`n` prime): at `p = 43, 67, 79, 103, 127` every `V(a)` is **purely imaginary** (`Re = 0` to machine
zero), **nonzero**, and `|V(a)|/√p ∈ (0, 2]` with `Nviol = 0`. Second moment is **exact**:
`Σ_{a≠0}|V(a)|² = n` per `a`-average, i.e. `E[(|V|/√p)²] = n/p ≈ 1`; `max|V|/√p = 1.55, 1.80, 1.82,
…, 1.91` climbing toward 2. **These two facts — `e₁ ≠ 0` and second moment `≈ 1` — are the
discriminants used below.** [VERIFIED, five primes; this only re-checks proved algebra, it is not the
basis of anything.]

---

## 1. Is the CAP a known theorem? — **No. Every cited bound gives `4√p`, not `2√p`.**

**Kohel–Shparlinski (ANTS-IV 2000), read directly.** KS `S(ω,ψ,f) = Σ ω(P)ψ(f(P))` has **additive**
`ψ` (Thm 1 proof: "`ψ∘f` defines an Artin–Schreier extension"). Their bounds:
`|S| ≤ Σᵢ mᵢ deg(𝔓ᵢ)·q^{1/2}` (Thm 1), `≤ 2 deg(f)·q^{1/2}` (eq 3), and **single-pole**
`≤ (1+deg f)·q^{1/2}`. **KS does not bound a multiplicative-coordinate twist `χ₂(y_P)`** — that is
exactly the §XI.10 scope gap. So KS gives *nothing* directly, and its analogue constant for a
degree-4 object is `4√p`.

**The record's own Weil–Deligne route** (`weil_deligne §6′`, Kummer sheaf): `g=y` has
`#R = 4` odd-order ramification points `⇒ dim H¹_c = 4 ⇒ |V(a)| ≤ 4√p`. This is the sharp
**cohomological** constant (`= dim H¹_c`), and it is the same `4√p`.

**Deligne Weil II alone**: four weight-1 eigenvalues `⇒ |V| ≤ 4√p`.

> The CAP `2√p` is a **factor-2 improvement over the sharpest cited bound (`4√p`)** and over the
> record's own Weil–Deligne constant. It is **not** a known theorem for this sum. [CITED-checked:
> KS = `4√p`; PROVED-here: `2√p ∉` any bound in the record's citations.]

The factor-2 is **not** produced by the `α↦−ᾱ` pairing. That pairing makes real parts cancel
(`V = 2i(Imα₁+Imα₂)`, verified purely-imaginary) but leaves the *bound* at `4√p`, since each
`|Imα_j| ≤ √p` independently. The CAP is the extra, unexplained statement `|Imα₁+Imα₂| ≤ √p` — a
**correlation between the two conjugate-pair factors** `β₁, β₂`.

---

## 2. Mechanism 1 (Weil restriction / induction from `F_{p²}`): **REFUTED. The weight bookkeeping
resolves against it, and the data confirms.**

This is the crux the task flagged. Worked carefully, in two equivalent ways, both fatal.

**(a) The trace of an induced representation is forced to zero.** If `H¹_c(a) = Ind_{F_{p²}}^{F_p} W`
with `W` a 2-dim rep of the `F_{p²}`-Weil group, and `Frob_p` swaps the two `F_{p²}`-pieces (the
literal "quadratics swapped by `Frob_p`, `β₂ = β₁^{(p)}`" statement), then `Frob_p` lies in the
**non-identity coset** of `⟨Frob_{p²}⟩` in `⟨Frob_p⟩`. For an index-2 induction, the character of any
element outside the subgroup is **identically 0**:
`Tr(Frob_p | Ind W) = Σ_{x: x⁻¹ Frob_p x ∈ H} tr_W(·) = 0` (no conjugate of `Frob_p` lands in `H`).
Therefore

> Mechanism 1 (literal) `⟹ e₁ = Tr(Frob_p|H¹_c) = 0 ⟹ V(a) = 0` for all `a`.

This is **false**: `V(a) ≠ 0` (verified purely-imaginary and nonzero at five primes; and `S → 2` in
`RESULT_n1_phase_cap_v3.md` requires `V` to *approach* `2√p`). So the char poly is **not even**
(`e₁ ≠ 0`), and an induced/Weil-restriction structure of the **whole** `H¹_c(a)` is impossible for
`a ≠ 0`.

**(b) The eigenvalue pattern is wrong for induction.** Induction from `F_{p²}` gives Frobenius
eigenvalues in `±`-pairs `{√γ, −√γ}` (square-roots of the `Frob_{p²}`-eigenvalues `γ`, `|γ|=p`),
i.e. `{α, −α}`. Our pairing is `{α, −ᾱ}`. `{α,−α} = {α,−ᾱ}` **iff `α = ᾱ`**, i.e. `α ∈ {±√p}` real
— the degenerate `θ∈{0,π}` case. So the induced structure is compatible **only** when the object is
untwisted-supersingular, which is precisely the `a = 0` fibre.

**The A_new connection, placed correctly.** The `a = 0` fibre **is** `A_new`: the double cover
`C: z²=y` over `E` gives `z⁴ = x³+7`, and `H¹_c(E, L_{χ₂(y)}) = H¹(A_new)`, the dim-4 object with
**even** char poly `t⁴ + m p t² + p²` (`e₁ = e₃ = 0`). At secp (`m=1`) its eigenvalues are
`√p·{ζ₆, ζ₆², ζ₆⁴, ζ₆⁵}`, which **do** sit in `±`-pairs (`ζ₆⁴ = −ζ₆`, `ζ₆⁵ = −ζ₆²`) — so `A_new`
is induction-*compatible* (consistent with `RESULT_anew_isogeny`: at `m=±2` it is a genuine `E'²`
Weil restriction; at `m=1` it is a *simple* supersingular surface with Frobenius field
`ℚ(√p, ω)` — induction-compatible as a Galois rep but not the Weil restriction of an honest elliptic
*curve*). **Twisting by `χ_a` (`a≠0`) moves the eigenvalues off the `±`-locus** onto the `−ᾱ`-locus
with `e₁ ≠ 0`, which is exactly what *destroys* the induction. So the CAP for `a≠0` cannot borrow
`A_new`'s structure: the structure it would borrow is only present at `a=0`, where `V(0)=0` trivially.

**The weight-bookkeeping trap named.** One is tempted to write "`β₁+β₂ = Tr_{F_{p²}/F_p}(β₁)`, a
trace on a 2-dim weight-1 piece over `F_{p²}`, so `≤ 2√(p²)`." That reading is doubly wrong: (i)
`√(p²) = p`, so it would give `|β₁+β₂| ≤ 2p` — *vacuous*, three orders worse than the CAP, not
`2√p`; (ii) done correctly (case (a)) the induced-rep trace is `0`, not `2p`. **Neither reading
yields `2√p`.** The factor of 2 the task worried about does **not** live in a `√(p²)/√p` weight
conversion; there is no honest induction here at all.

> **Verdict on mechanism 1: refuted.** The precise checkable form ("char poly factors over `F_{p²}`
> with the quadratics `Frob_p`-swapped") is **decidably FALSE** for `a≠0` — it is equivalent to
> `V(a)≡0`, contradicting `e₁≠0`. This is a concrete negative result, not an open question.

---

## 3. Mechanism 2 (the two factors dual / conjugate): **one branch refuted, one already spent.**

- **`W₂ ≅ W̄₁` (complex-conjugate pieces).** Eigenvalues of `W̄₁` are `{ᾱ₁, −α₁}`; matching to
  `{α₂,−ᾱ₂}` forces `θ₂ = −θ₁` or `θ₂ = θ₁+π`, both giving `sinθ₂ = −sinθ₁`, hence
  `sinθ₁+sinθ₂ = 0` and `V(a) ≡ 0`. **Refuted** — same failure mode as mechanism 1, and forbidden by
  `S→2` (it would force the sum to *vanish*, not approach `2√p`). This is exactly the "mechanism
  forcing `β₂` to make `|sinθ₁+sinθ₂|` SMALL" the task warned would be wrong.

- **`W₂ ≅ W₁^∨(1)` (Tate/Poincaré dual).** This is the **functional equation** of `L(C,t,χ)`:
  `H¹_c(a)` paired with `H¹_c(−a)`, realized as the `α↦−ᾱ` closure. It is **already used** — it is
  what supplies the `2+2` pairing and the purely-imaginary `e₁`. It gives **only** `|V| ≤ 4√p`; it
  says nothing new toward `2√p`, because it relates `a` to `−a`, not the two factors *within* one
  `H¹_c(a)`. Consistent, insufficient.

> **Verdict on mechanism 2: refuted (conjugate branch) / spent (dual branch).** Neither closes the
> CAP; the conjugate branch is excluded by `S→2`.

---

## 4. Mechanism 3 (small geometric monodromy / finite-field Mellin transform): **the only mechanism
consistent with the data, but it gives the DISTRIBUTION, not a pointwise cap.**

The right home is **Katz, *Convolution and Equidistribution: Sato–Tate theorems for finite-field
Mellin transforms* (AM-180, 2012).** `V(a) = Σ_{P} χ₂(y_P)·χ_a(P)` is exactly the **finite-field
Mellin (= Fourier) transform** of the function `P ↦ χ₂(y_P)` on the finite abelian group
`E(F_p) ≅ Z/n`, evaluated at the character `χ_a`. Katz's theory attaches to such a transform a
geometric monodromy group `G_geom`, and the values `V(a)/√p` **equidistribute** according to the
trace of a random element of a maximal compact `K ⊂ G_geom`.

**Two facts make this the consistent picture:**
- The eigenvalue pattern `{z,−z̄,w,−w̄}` gives unitarized trace `τ = 2i(Im z + Im w)`, purely
  imaginary, `det = 1`. The CAP is `|τ| ≤ 2`.
- **The second moment is the SU(2) Sato–Tate variance.** `E[(|V|/√p)²] = n/p ≈ 1` **exactly**
  (`Σ_{a≠0}|V|² = n·(n−1)`, from `Σ_P χ₂(y_P)² = n−3` and `Σ_P χ₂(y_P) = 0`). A variance of `1` and a
  support ceiling of `2` are the signature of a **2-dimensional** `SU(2)`-type object (`E[t²]=1`,
  `|t|≤2` for `t=2cosφ`), **not** a generic 4-dimensional one (whose trace variance would be larger
  and whose max could reach 4). The `S→2` saturation is then the statement that the trace support
  *reaches* its `SU(2)` ceiling. **This is the "2-dim isotypic" intuition vindicated — at the level
  of the distribution.**

**But this does not prove the pointwise CAP.** Confirmed against the literature (Katz AM-180; the
vertical Sato–Tate surveys — Sutherland, and *Refinements on vertical Sato–Tate* arXiv:2310.08791):
equidistribution/monodromy describes the **limiting distribution** of the values and restricts
**which** distributions occur; it **does not lower Deligne's pointwise ceiling** for a fixed `p`.
Equidistribution tolerates finitely many outliers up to `4√p` at any fixed `p`. To get a *pointwise*
cap one needs the strictly stronger statement:

> **(★) The image of arithmetic monodromy in the 4-dim standard representation is contained in a
> subgroup `G` such that `|Tr(g)| ≤ 2√p` (unitarized `≤2`) for EVERY `g ∈ G`.**

This is *not* an equidistribution statement and is *not* delivered by Katz's theorems as black boxes;
it is a specific **monodromy computation** (that `G_geom` is the small group whose 4-dim trace tops
out at exactly 2, e.g. an `SU(2)` mapped in so the two conjugate-pair factors are locked together).
That computation is **not in the record and is itself research-grade.** The WebFetch caveat is
explicit that generic monodromy "doesn't lower the maximum below what Deligne guarantees" — so `(★)`
is a claim that we are in the *non-generic small-monodromy* case, which the `SU(2)`-variance evidence
supports but does not prove.

> **Verdict on mechanism 3: consistent, and the correct framework, but a *distributional* match — not
> a proof of the pointwise cap.** It converts the CAP into the monodromy statement `(★)`.

---

## 5. VERDICT

> **(c) GENUINE GAP.** `|V(a)| ≤ 2√p` is **not** reducible to a cited theorem and **not** one
> elementary lemma from the record's proved structure. The record's citations (KS, Weil–Deligne/
> Kummer) give `4√p`; the `α↦−ᾱ` pairing (proved) gives no improvement to the *bound*; and the
> natural "2-dim" mechanisms fail:
> - Weil restriction / induction (mech. 1) is **decidably false** for `a≠0` (`⟺ V≡0`, contradicting
>   `e₁≠0`);
> - conjugate-factor duality (mech. 2a) is **excluded by `S→2`** (`⟺ V≡0`);
> - Tate-dual (mech. 2b) is the already-used functional equation (`4√p`);
> - small monodromy (mech. 3) is the right framework and matches the `SU(2)`-variance data, but yields
>   the **distribution**, not the pointwise cap.

**Positive framing (this is a lever, not a wall).** The CAP is now pinned to **one** precise,
non-generic structural statement — a monodromy containment — and the second-moment evidence says the
effective object behaves 2-dimensionally. That is a sharp, named target, not a diffuse obstruction.

### The sharpest equivalent open statements (any one ⟹ the CAP)

1. **House form (concrete, checkable).** For `n` prime the `a≠0` are a single Galois orbit
   (`σ_c: ζ_n↦ζ_n^c` sends `V(a)↦V(ca)`), so the CAP for all `a` **is**:
   > the algebraic integer `V(1) = Σ_P χ₂(y_P)·ζ_n^{d(P)} ∈ Z[ζ_n]` has **house `≤ 2√p`**
   > (Deligne gives house `≤ 4√p`).
   The gap is exactly the factor 2 in the house of one explicit cyclotomic integer.

2. **Monodromy form (the mechanism).** Statement `(★)` of §4: the arithmetic monodromy of the
   finite-field Mellin transform of `χ₂(y_·)` on `E(F_p)` lands in a subgroup whose 4-dim trace has
   modulus `≤ 2√p` everywhere — equivalently, `G_geom` is the small group (`SU(2)`-type, the two
   conjugate-pair factors `β₁,β₂` locked) predicted by the `E[(|V|/√p)²]=1`, `max→2` signature.

3. **Coefficient form (as `RESULT_weight1 §3` framed it).** In `L(C,t,χ)=1+V t+e₂t²+pV t³+p²t⁴`,
   the CAP is `V² ≥ −4p` (`V` purely imaginary, `V²∈ℝ_{<0}`), i.e. the middle-coefficient constraint
   `−(β₁+β₂)² ≤ 4p` with `β₁,β₂` the two purely-imaginary roots of `z²+V z+(e₂+2p)`. This is the
   integrality-of-`Z[ζ_n]`-coefficients attack named in the record; it is a restatement, not yet a
   proof — nothing forces the two imaginary roots' sum below `2√p` from `e₂` alone.

### What is decidably settled by this analysis (so it is not re-litigated)
- The precise "Frobenius-swapped quadratics over `F_{p²}`" hypothesis is **FALSE** (§2), not open.
- The factor-2 is **not** a weight-bookkeeping `√(p²)/√p` effect (§2 trap) and **not** the `α↦−ᾱ`
  cancellation (§1); it is a genuine correlation between the two conjugate-pair factors.
- Any mechanism forcing `β₂` to *cancel* `β₁` (mechs 1, 2a) is refuted twice over — by `e₁≠0` and by
  `S→2`. The correct mechanism must **allow** `|sinθ₁+sinθ₂|` to approach 1, which only the
  small-monodromy picture (mech. 3) does.

### Scope / honesty
Everything is scoped to the proved inputs and to `n` prime, `p≡1 mod3`, `p≡3 mod4`. The `SU(2)`-variance
grounding is at five small primes and only re-checks proved algebra; it is corroboration of the
framework, not evidence for `(★)`. No statement reaches `p = 2²⁵⁶−2³²−977`, and the CAP itself remains
`[VERIFIED — out-of-sample, 120 primes]` (`RESULT_n1_phase_cap_v3`), **not** `[PROVED]`. This document
does not change that grade; it isolates the single missing statement (`(★)` / house `≤2√p`) and closes
off three wrong roads to it.

---

*Grade: §1 [CITED-checked, PDF read] + [PROVED-here]. §2 [PROVED-here: induced-trace = 0] +
[VERIFIED: `e₁≠0`, five primes]. §3 [PROVED-here]. §4 [CITED: Katz AM-180, lit-confirmed] +
[VERIFIED: second moment `=n`]. §5 verdict (c) GENUINE GAP — author's derivation, no adversarial pass.
The sharpest open statements 1–3 are equivalent reformulations, offered for the next attack.*
