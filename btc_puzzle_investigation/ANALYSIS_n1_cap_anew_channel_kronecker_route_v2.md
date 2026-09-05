# `V(a)` as the `A_new` channel — what survives the twist, and the route that follows

*2026-07-26. Analysis only. **Nothing run, nothing promoted, no grade moves.** No leakage or ECDLP
claim. Supersedes `..._v1.md`: folds in an independent adversarial review of the proof chain
(2026-07-26). Still contains the retraction of two mechanism sketches (§3).*

> **What changed from v1.** An independent reviewer (isolated context, given only S1–S8 + inputs, not
> this document's framing) checked the chain. **Verdict: the skeleton is sound** — the conditional core
> `S5 → S6 → S7` (ideal equality ⇒ unit ⇒ all conjugates on the unit circle ⇒ root of unity) is
> correct, and the S8 reduction is real. It found **two arithmetic slips** (a sign in the trace
> formula; `sin(θ−60°)` not `sin(θ+60°)` — neither touches the `2√p` bound), **one justification that
> was stated wrongly** (S6 must be argued from purity-per-embedding, *not* from Galois permuting the
> four eigenvalues — because the coefficients live in `ℤ[ζ_n]`, not `ℤ`), and **five hypotheses used
> without being named** (integrality; CM-derived-not-asserted; `u ≠ 1`; identifying `μ(L)`; per-cell ≠
> uniform). It also contributed **one constructive lead** for where the `ζ₃` comes from (§4b), and an
> **independent numerical confirmation of the 120° law itself** (§7b), not just of the bound. All folded
> in below and flagged ⟪REV⟫.

---

## §1 — The framing is exactly right, and here is the precise version

`C : w⁴ = x³+7` is the double cover of `E` given by `w² = y`. Decompose `H¹(C)` under the deck group
`μ₂ = ⟨w ↦ −w⟩`:

```
H¹(C)  =  H¹(E)  ⊕  H¹(E, L_{χ₂(y)})
  6     =    2    +    4
```

and the record independently has `Jac(C) ~ E × A_new` with `A_new` an abelian surface, so
`dim H¹_new = 4`. The anti-invariant part is the new part:

> **`H¹_c(E, L_{χ₂(y)}) = H¹(A_new)`, exactly.**

So the **untwisted** `χ₂(y)` sum *is* `A_new`'s Frobenius trace. **Consistency check the record already
supplies, and it is exact:** Lefschetz gives `Σ_P χ₂(y_P) = −tr(Frob | H¹(A_new))`, and **L1
`[PROVED, elementary]` says that sum is `0` at every `p ≡ 3 mod 4`** — which is precisely a
supersingular abelian surface having trace zero. Two independent parts of the record agreeing at
`a = 0`.

**The twist.** `L_{χ_a}` is the Lang-torsor sheaf of the character `χ_a` of `E(F_p)`. The record's own
weight-1 proof records that it is **totally unramified**, so tensoring does not change the
ramification and `dim H¹_c` stays `4`. Hence:

> **`V(a)` is the Frobenius trace on `H¹(A_new)` twisted by the Lang-torsor character `χ_a`, and the
> family `{V(a)}` is the orbit of `A_new`'s `H¹` under the full group of such twists — which is
> `E(F_p)^ ≅ ℤ/n` itself.** At `a = 0` it is `A_new` unmodified.

**⇒ the `2√p` cap is exactly the question: how much of `A_new`'s supersingular rigidity survives the
twist?** That is D2, restated in one line, and `PREREG_D2_lang_hypergeometric_relin_v1.md` (2026-07-20)
has never been run.

⚠ **One thing the framing must not be read as saying.** `L_{χ_a}` is **geometrically nontrivial**, so
the twist is *not* a scalar multiplication of the eigenvalues. If it were, `|V(a)|` would be constant
in `a`, and it is not. The twist is a genuine deformation in a 4-dimensional family, and **a priori
nothing has to survive.** That is why D2 is a question and not a triviality.

⟪REV⟫ **Sign, for the record.** Grothendieck–Lefschetz with `H⁰_c = H²_c = 0` gives
`V(a) = −tr(Frob | H¹_c) = −Σ αᵢ`. The consistency check above already carries the minus; §2 and §4
below are corrected to match. `V(a)` is purely imaginary (the `P ↦ −P`, `χ₂(−1) = −1` symmetry), which
the reviewer reconfirmed to `≤ 7×10⁻¹⁵` at six primes — so the *form* is right; only the sign of the
sine offset was wrong in v1.

---

## §2 — The rigidity budget: what survives, what does not

| property at `a = 0` (supersingular `A_new`) | survives the twist? | evidence |
|---|---|---|
| purity `\|α_i\| = √p` at every embedding | **YES** | `[PROVED — all p]`, weight-1 |
| multiset closed under `α ↦ −ᾱ` | **YES** | `[PROVED — FORCED]` |
| each `α_i` **is** `√p ×` a root of unity | **NO** | the angle becomes free and **equidistributes** (Sato–Tate; `mean\|u\| = 0.408` vs `0.424`) |
| trace `= 0` | **NO** | becomes `−2i√p·sin(θ−60°)` ⟪REV: sign + `−60°`⟫ |
| **the RATIO of the two pairs is a root of unity** | **YES** | the 120° law, `9.5×10⁻⁴⁰`, 357 classes; corroborated independently §7b |

> **⇒ The answer to "how much survives": the ABSOLUTE rigidity is destroyed; the RELATIVE rigidity
> survives. The `2√p` cap is the arithmetic value of that relative rigidity.**

And this explains the `½` saturation (`MASTER_v4` Part VII.5, *"the one measured anomaly with no
account"*): the additive readout `bx+cy` has **4 genuinely free** eigenvalues and reaches `0.876` of
`4√p`; `χ₂(y)` has **2 free ones times `{1, ζ₃}`**, so effectively 2 of 4 — and `½ = 2/4`.

---

## §3 — ⚠ RETRACTION: both mechanisms I proposed are wrong

I claimed the `ζ₃` comes from a `μ₃` symmetry — in `SYNTHESIS_brainstorm_seven_cycles_v1.md §1.3`
(the three 2-torsion points forming a `μ₃`-orbit, `E/μ₃ ≅ P¹` a cyclic cubic cover) and again in
`..._ADDENDUM_1_v1.md §2.4` (an "independent second route" from `μ₃ ⊂ μ₁₂ ⊆ Aut(C)` acting on a
supersingular `H¹_new`). **Checked this session; neither works for `a ≠ 0`:**

```
[λ]* ( L_{χ₂(y)} ⊗ L_{χ_a} )  =  L_{χ₂(y)} ⊗ L_{χ_{aλ}}
equal to the original  ⟺  aλ ≡ a (mod n)  ⟺  a(λ−1) ≡ 0 (mod n)
n prime and λ ≠ 1  ⇒  gcd(λ−1, n) = 1  ⇒  a = 0 ONLY.
```

**The sheaf is `μ₃`-equivariant only at `a = 0`.** The same computation kills the `μ₄` version: `σ`
(`w ↦ iw`) induces `[−1]` on `E`, so it relates `H¹(a)` to `H¹(−a)`, not to itself. What the `μ₃`
action *does* give is `V(a) = V(aλ)` — the known collapse of `n−1` cells to `(n−1)/6`, relating
**different** `a`, never an internal splitting at fixed `a`.

**Both of my "the mechanism is `μ₃`-equivariance" claims are withdrawn.** ⚠ Consequence: the
`j ≠ 0` mechanism control I ranked #1 in the brainstorm is testing a mechanism I have now refuted.
It is still worth running — the 120° law's dependence on `j = 0` is a real question — but it is no
longer a test of a stated mechanism, and should be re-labelled before it is pre-registered.

⟪REV⟫ The reviewer independently reproduced this collapse (`V(a) = V(λa)` to `3×10⁻¹⁴`, `p = 43, 67,
79, 127, 163, 211`, `λ` of order exactly 3 mod `n`) and agrees it relates different `a`, not a fixed
fiber. But it points out that this same fact, read Galois-theoretically rather than
sheaf-theoretically, is the natural home of the `ζ₃` — see §4b.

---

## §4 — The correct restatement, and it is an IDEAL question

Write the four eigenvalues as `{α₁, −ᾱ₁, α₂, −ᾱ₂}`, `|α_i| = √p`. The 120° law says
`θ₁ − θ₂ = 120°`, i.e.

> **`α₂ / α₁` is a primitive cube root of unity — exactly, at every `a`.**

Verified numerically this session: with `α₂ = α₁ζ̄₃`, the ratio has modulus `1.000000000000000`, cubes
to `1`, and reproduces `s₁²+s₁s₂+s₂² = 0.750000000000000` and `|V|/√p ≤ 2` at every angle tested.

⟪REV, e.1⟫ **The statement is representative-dependent; the bound is not.** The decomposition into
`ι`-orbits (`ι : α ↦ −ᾱ`) does not canonically pick which is `α₁` and which is `α₂`: swapping `α₂` for
`−ᾱ₂` sends `θ₂ ↦ 180° − θ₂`, so "`θ₁ − θ₂ = 120°`" moves, while `sin θ₁ + sin θ₂` — hence `V` — does
not. The invariant, label-free form is: **the eigenvalue multiset shares exactly two elements with its
`ζ₃`-rescaling.** *(This is exactly the statistic the prereg freezes, `deg gcd(L*(T), L*(ζ₃T)) = 2`,
which is why the prereg is label-free by construction — the ambiguity here is already designed out
there.)* Both readings the reviewer distinguishes — `α₂/α₁ = ζ₃` and the cross-ratio
`−ᾱ₂/α₁ = ζ₃` — describe the **same multiset** and both give `2√p`; only the wording of the law
differs.

Now the two facts that make this an arithmetic statement:

1. **Purity (`[PROVED — all p]`) says `|σ(α_i)| = √p` for EVERY embedding `σ`.** So
   `|σ(α₂/α₁)| = 1` for every `σ` — the ratio lies on the unit circle at all archimedean places.
   ⟪REV, (b) — the load-bearing correction⟫ This is the **right** justification, and the only one
   that works. The coefficients of `L*` live in `ℤ[ζ_n]`, **not `ℤ`** (the power sums are the
   `V_m(a) ∈ ℤ[ζ_n]`). So a Galois `σ` that moves `ζ_n` does **not** permute the four eigenvalues of
   this cell — it carries them to the eigenvalues of a **different** cell: `σ_k(V(a)) = V(ka)`. Any
   argument of the form "`σ(u)` is again a ratio of two of the four eigenvalues" is therefore **false**
   and must not be used. The conclusion survives only because purity is stated **per embedding, per
   eigenvalue**; that "for EVERY embedding" is doing all the work, and if purity were available only at
   the identity embedding the whole chain would collapse.
2. **Each `±` pair generates `(p)`:** `α·(−ᾱ) = −αᾱ = −p` (checked: `−10007.000000` at `p = 10007`),
   consistent with the record's forced `e₄ = p²`. ⟪REV, (c)⟫ This holds as an **algebraic identity in
   `O_L`**, not merely between complex absolute values, and **closure is what supplies it**: `−ᾱ` is an
   eigenvalue, so `ᾱ ∈ L`, and `αᾱ = |α|² = p` is then an identity of algebraic numbers.

> **⇒ IF `(α₁) = (α₂)` as ideals, then `α₂/α₁` is a UNIT with every conjugate on the unit circle, and
> by KRONECKER'S THEOREM it is a root of unity.**

**The entire 120° law reduces to: do the two eigenvalue-pairs generate the same ideal?** That is not a
symmetry question — it is an ideal-factorization question, which is why every group-action attempt in
§3 failed.

⟪REV, hypotheses that were used but not named — now named⟫

- **Integrality.** `α_i ∈ O_L` is a genuine input; it does **not** follow from purity. It holds here
  because `L*` is monic of degree 4 with coefficients in `ℤ[ζ_n]` (integral), so the reciprocal roots
  are algebraic integers. Without it, "`(α)` is an integral ideal" is unjustified — though S5–S7
  survive verbatim with **fractional** ideals, so this is a cleanliness point, not a hole.
- **CM is derived, not assumed.** `|σ(α)| = √p` for all `σ` (a Weil number) forces `ℚ(α)` to be **CM
  or totally real** by the standard argument (`α ↦ p/α` is an automorphism agreeing with complex
  conjugation at every embedding). So "the splitting field is CM" should be presented as a
  **consequence of purity**, not an extra axiom. The totally-real branch `α = ±√p` is a degeneracy
  (next bullet).
- **`u ≠ 1` must be excluded.** ⟪e.2⟫ If `α₁ = α₂` (equal pairs), then `u` is a root of unity of order
  **1**, and `|V|` is only bounded by `4√p`, not `2√p`. Pinning the order away from 1 is not cosmetic —
  it *is* the bound. *(In the prereg's statistic this case returns `g = 0`, correctly reading as "not
  the law"; see PREREG v2.)*
- **Degenerate pairing.** ⟪(g)⟫ The paired form `{α, −ᾱ, β, −β̄}` is **not** implied by closure alone:
  `ι : α ↦ −ᾱ` has fixed points `±i√p`, so a closed multiset could contain `{i√p, −i√p}` (an `ι`-orbit
  that is **not** of the form `{α, −ᾱ}`). Such eigenvalues must be excluded before writing "two
  half-angles", or handled separately. **Consolation:** in that degenerate case the two fixed
  eigenvalues cancel and `V = ±2i Im β`, so `|V| ≤ 2√p` holds **unconditionally** — the degeneracy
  threatens the *statement* of the 120° law, not the cap. Numerically no observed eigenvalue is at
  `±√p` or `±i√p` (all angles generic), so this is measure-zero, but it belongs in the hypotheses.

---

## §4b — ⟪REV⟫ Where the `ζ₃` plausibly comes from: a Galois fact, not a sheaf splitting

This is offered as a **lead, not a proved step** (the reviewer states it and explicitly did not verify
it yields `(α₁) = (α₂)`). It is the correct successor to the mechanisms retracted in §3: the `μ₃` is
**not** an internal symmetry of the fiber `H¹(a)` — that was refuted — but it **is** present as a
Galois symmetry of the *number* `V(a)`.

- `p ≡ 1 mod 3` and `j(E) = 0`, so `ζ₃ ∈ F_p` and `ω : (x,y) ↦ (ζ₃x, y)` is an `F_p`-automorphism of
  `E`. It fixes `y`, hence fixes `χ₂(y)`, hence `ω^* L_{χ₂(y)} = L_{χ₂(y)}`.
- `ω` acts on `E(F_p) ≅ ℤ/n` as multiplication by some `λ` with `λ³ ≡ 1`, `λ ≢ 1 (mod n)` (order
  exactly 3). This gives `V(a) = V(λa)` — the §3 collapse.
- **The new step:** the arithmetic Galois action is `σ_k(V(a)) = V(ka)` for `σ_k : ζ_n ↦ ζ_n^k`.
  Taking `k = λ`: `σ_λ(V(a)) = V(λa) = V(a)`. So **`V(a)` is fixed by the order-3 Galois automorphism
  `σ_λ ∈ Gal(ℚ(ζ_n)/ℚ)`** — it lies in the fixed field `ℚ(ζ_n)^{⟨σ_λ⟩}`. The same holds for every
  power sum `V_m(a)`, hence for `e₁, e₂` and all of `L*`: **`L*` is defined over that index-3 subfield.**

That is the natural source of a `μ₃` in the problem, and it is arithmetic (about `V(a)` as an element
of `ℤ[ζ_n]`), consistent with the §3 retraction rather than in tension with it. **What it does not yet
do:** show `(α₁) = (α₂)`. Whether "`L*` descends to the `σ_λ`-fixed subfield" forces the two
eigenvalue-ideals to coincide is open, and is the bridge that would connect §4b to the Kronecker step
of §4. Flagged as the most promising unproved lead.

---

## §5 — ★ The record already proved a theorem with exactly this shape

From `RESULT_jacobi_sign_law_stickelberger_v1.md` (2026-07-25), the proof that closed the Jacobi sign
law, quoted in structure:

> **Stickelberger gives `(J) = (p)`** — which **kills the `π²` competitor**, because *"Frobenius
> constrains the FIELD and `π²` differs in the IDEAL."*
> **Then Kronecker ⇒ `J = ζp`, `ζ ∈ μ₁₂`.**
> **Mod the prime above 2 (`i ≡ 1`) forces the `μ₃` part trivial** = the rationality;
> **mod the prime above 3 (`ω ≡ 1`) fixes the sign.**

Every step transfers:

| Jacobi proof | the eigenvalue-ratio question |
|---|---|
| Stickelberger ⇒ `(J) = (p)` | **Stickelberger ⇒ `(α₁) = (α₂)`?** — Frobenius eigenvalues on a Kummer sheaf **are** Gauss/Jacobi sums, which is exactly what Stickelberger factorizes |
| Kronecker ⇒ `J = ζp`, `ζ ∈ μ₁₂` | Kronecker ⇒ `α₂/α₁` is a root of unity |
| reduce mod the prime above 2 ⇒ `μ₃` part **trivial** | pin the order ⇒ `μ₃` part **primitive** (the opposite component of the same `μ₁₂`) |
| reduce mod the prime above 3 ⇒ fixes the sign | pins the `μ₄`/`±` part — already `[PROVED — FORCED]` |

**Same field (`μ₁₂`), same two tools, same three steps.** And the record's hard-won lesson from that
proof is precisely the one I violated twice in §3: *go to the ideal, not to the field or the
symmetry.*

⚠ **Inherited dependency (D2-cite):** Stickelberger's citation is still **UNVERIFIED** after three
failed `citation-verifier` runs, and the open question is whether sources state it for `m = 12` (not a
prime power) and `f = 2`. Any use here carries that debt.

---

## §6 — The gap in the route, stated honestly

**Kronecker gives "a root of unity", not "order 3".** Pinning the order needs a second input, and
there is a real constraint available:

`V(a) ∈ ℤ[ζ_n]`, so the L-polynomial has coefficients in `ℤ[ζ_n]`. But **`ζ₃ ∉ ℚ(ζ_n)`**: for prime
`n`, `ℚ(ζ_n)` contains `ζ_m` iff `m | n` or `m | 2n`, and `3 ∤ n` because **`n ≡ 1 mod 3` is forced**
(the record's own `(L3)`, `4977/4977`).

> **⇒ FORCED, CHECKABLE CONSEQUENCE: the 120° law pushes the eigenvalues OUT of `ℚ(ζ_n)`. The
> splitting field of the twisted L-polynomial must contain `ζ₃` — i.e. it must contain `ℚ(ω)`, the CM
> field of `E` itself.**

That is a decidable per-prime prediction with a clean falsifier, and it is cheap: compute the
splitting field at small `p` and test `ζ₃ ∈ it`. ⚠ **Do not confuse this with item 12** — item 12 says
the *splitting field of `L_new`* is **not** a CM-type discriminator. This is a different object (the
splitting field of the **twisted** polynomial) and it is being used as a **forced necessary
condition**, not as a discriminator.

⟪REV, e.3⟫ **Caveat on "pin the order to 3".** Doing so requires knowing which roots of unity actually
lie in the splitting field `L` — i.e. **identifying `L`** — and nothing in S1–S7 constrains `L`. So
this sub-step is not automatically *weaker* than the original claim; it is a second genuine task. The
`ζ₃ ∉ ℚ(ζ_n)` fact above rules out `μ_n`-only, which is a start, but the full determination of `μ(L)`
is still owed. §4b's "L* descends to `ℚ(ζ_n)^{⟨σ_λ⟩}` and the whole problem carries a native order-3
Galois symmetry" is the most likely place that second input comes from.

⟪REV, e.5 — uniformity⟫ **The chain is per-cell.** The 120° observation is over 357 `(p, a)` cells;
S1–S8 argue one cell at a time, inside a field `L` that varies with the cell. Nothing yet gives the
ideal equality **for all `a` and all `p`** simultaneously. A per-cell exact proof at the frozen sample
(the prereg's job) is evidence; a uniform statement needs the analytic/Stickelberger route, which is
where the reach past `p ≈ 10³` has to come from.

---

## §7 — The decisive test, and it is cheap

**Compute `(α₁)` and `(α₂)` as ideals at small `p` and check whether they coincide** — or, label-free
and far cheaper, the prereg's `deg gcd(L*(T), L*(ζ₃T)) = 2`. The instrument exists —
`n1_twisted_eigenvalues_v1.sage` already produces the four eigenvalues (control C2 fires at `4.4e−16`),
and the `O(p²)` `V₂` route makes the coefficient computation affordable well past the `O(p⁴)` cap.

Pre-committed readings (see `PREREG_n1_120deg_exact_ideal_v2.md`):

- **`(α₁) = (α₂)` / `g = 2` at every tested `(p, a)`** ⇒ the ratio is a unit, Kronecker applies, and
  the 120° law is **exact at those cells**, reducing to pinning the order of a root of unity in `μ₁₂`
  — a Stickelberger computation with a template on file. The cap follows (per-cell; uniformity still
  owed, §6).
- **The ideals differ / `g = 0` at any cell** ⇒ the ratio is not a unit, **Kronecker does not apply,
  and this whole route is dead.** A clean falsifier, and the 120° law would then need a mechanism
  nobody has proposed.

Order of work: (i) the ideal / `g` test above; (ii) the `ζ₃ ∈ splitting field` check of §6, which is
forced and therefore an **instrument check** — if it fails, the eigenvalue computation is wrong, not
the theory; (iii) only then the Stickelberger computation, and only after the citation is re-verified.

⚠ `experiment-designer` prereg before any sweep (the v2 prereg is written and is **held pending that
gate**, which failed once on infra and must be re-run), and read
`PREREG_D2_lang_hypergeometric_relin_v1.md` first — this is D2's territory and it already has a spec.

---

## §7b — ⟪REV⟫ Independent numerical corroboration of the law (not just the bound)

The reviewer, from an isolated context and a self-contained script, reproduced more than the `≤ 2√p`
bound:

- **`V(a)` purely imaginary** to `≤ 7×10⁻¹⁵`; `max_a |V(a)|/(2√p)` `= 0.778, 0.785, 0.695, 0.957,
  0.951, 0.910` at `p = 43, 67, 79, 127, 163, 211` — never exceeds 1.
- **The 120° law directly**, via a *second* power sum: computing `V₂(a)` over `F_{p²}` gives `Σα_i²`,
  hence `Q = sin²θ₁ + sin²θ₂` alongside `S = sin θ₁ + sin θ₂` from `V₁`. The law `θ₁ − θ₂ = ±120°` is
  equivalent to `(S² + Q)/2 = 3/4`. Measured: **`0.750000000` in all 18 cells** (`p = 43, 67, 79`,
  `a = 1..6`), residual `≤ 10⁻⁹`; and `Im(V₂) ≈ 0` (`≤ 3×10⁻¹⁴`) as the pairing predicts.
- **`dim H¹_c = 4`** confirmed by an Euler-characteristic count (`χ_c = −4`, lisse on `E` minus `{O}`
  and the three 2-torsion points), and "`L_{χ_a}` totally unramified" is exactly what pins the 4.

This is an **independent** confirmation of the premise the whole route rests on — and, notably, it uses
the **same `V₂`/`O(p²)` instrument the prereg freezes**, so it also corroborates that the prereg's
instrument computes the intended object. It remains **numerical** (`≤ 10⁻⁹`); making it exact is
precisely the prereg's purpose.

---

## §8 — What this document claims and does not

**Claims (all `[MINE — in-session, UNVERIFIED]` unless marked):**
`H¹_c(E, L_{χ₂(y)}) = H¹(A_new)` with L1 as the `a=0` consistency check; the rigidity budget of §2;
that the `μ₃`/`μ₄` equivariance mechanisms **fail for `a ≠ 0`** (a two-line computation, reproduced
independently by the reviewer — confident); the label-free restatement (multiset shares two elements
with its `ζ₃`-rescaling); the Kronecker reduction `S5 → S6 → S7` (reviewer: skeleton sound); the
structural match to the Jacobi proof; the forced `ζ₃ ∈ splitting field`.

**Does not claim:** that the cap is proved — §4 is conditional on an ideal equality not computed at a
single prime; that Stickelberger applies — its citation is unverified and its applicability to this
object is asserted by analogy, not checked; that the order is 3 — Kronecker gives only "a root of
unity" (§6), and pinning it needs `μ(L)` (⟪REV e.3⟫); **that any per-cell result is uniform in `a, p`**
(⟪REV e.5⟫); the §4b Galois-`ζ₃` lead is a **lead**, not a step.

**Retracts:** the `μ₃`-orbit-of-ramification-points mechanism (`SYNTHESIS_brainstorm_seven_cycles_v1.md
§1.3`) and the `μ₃ ⊂ μ₁₂ ⊆ Aut(C)` mechanism (`..._ADDENDUM_1_v1.md §2.4`). The `A_new`-channel
framing they were attached to **survives and is strengthened**; only the proposed mechanism was wrong.

**Corrects (from v1, per the review):** trace sign and `sin(θ−60°)` (§1, §2 — bound unaffected); the
S6 justification (§4.1 — purity-per-embedding, not Galois-permutes-4-roots); adds integrality,
CM-from-purity, `u ≠ 1`, degenerate pairing, `μ(L)`, and per-cell-≠-uniform as named hypotheses.

**Scale banner #5 governs the empirical rows.** The 120° law is measured at `p ≤ 547`.
