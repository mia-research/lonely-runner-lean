# `V(a)` as the `A_new` channel — what survives the twist, and the route that follows

*2026-07-26. Analysis only. **Nothing run, nothing promoted, no grade moves.** No leakage or ECDLP
claim. Contains a **retraction of two mechanism sketches I gave in this same session's two prior
documents.***

> **What this file does.** Develops the "`V(a)` is the `A_new` channel" framing properly, checks it,
> and follows where it leads. Checking it **breaks** the two mechanisms I proposed for the 120° law
> and replaces them with a different one that is arithmetic rather than group-theoretic — and which
> the record already has a working template for.

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

---

## §2 — The rigidity budget: what survives, what does not

| property at `a = 0` (supersingular `A_new`) | survives the twist? | evidence |
|---|---|---|
| purity `\|α_i\| = √p` at every embedding | **YES** | `[PROVED — all p]`, weight-1 |
| multiset closed under `α ↦ −ᾱ` | **YES** | `[PROVED — FORCED]` |
| each `α_i` **is** `√p ×` a root of unity | **NO** | the angle becomes free and **equidistributes** (Sato–Tate; `mean\|u\| = 0.408` vs `0.424`) |
| trace `= 0` | **NO** | becomes `2i√p·sin(θ+60°)` |
| **the RATIO of the two pairs is a root of unity** | **YES** | the 120° law, `9.5×10⁻⁴⁰`, 357 classes |

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

---

## §4 — The correct restatement, and it is an IDEAL question

Write the four eigenvalues as `{α₁, −ᾱ₁, α₂, −ᾱ₂}`, `|α_i| = √p`. The 120° law says
`θ₁ − θ₂ = 120°`, i.e.

> **`α₂ / α₁` is a primitive cube root of unity — exactly, at every `a`.**

Verified numerically this session: with `α₂ = α₁ζ̄₃`, the ratio has modulus `1.000000000000000`, cubes
to `1`, and reproduces `s₁²+s₁s₂+s₂² = 0.750000000000000` and `|V|/√p ≤ 2` at every angle tested.

Now the two facts that make this an arithmetic statement:

1. **Purity (`[PROVED — all p]`) says `|σ(α_i)| = √p` for EVERY embedding `σ`.** So
   `|σ(α₂/α₁)| = 1` for every `σ` — the ratio lies on the unit circle at all archimedean places.
2. **Each `±` pair generates `(p)`:** `α·(−ᾱ) = −αᾱ = −p` (checked: `−10007.000000` at `p = 10007`),
   consistent with the record's forced `e₄ = p²`.

> **⇒ IF `(α₁) = (α₂)` as ideals, then `α₂/α₁` is a UNIT with every conjugate on the unit circle, and
> by KRONECKER'S THEOREM it is a root of unity.**

**The entire 120° law reduces to: do the two eigenvalue-pairs generate the same ideal?** That is not a
symmetry question — it is an ideal-factorization question, which is why every group-action attempt in
§3 failed.

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

---

## §7 — The decisive test, and it is cheap

**Compute `(α₁)` and `(α₂)` as ideals at small `p` and check whether they coincide.** The instrument
exists — `n1_twisted_eigenvalues_v1.sage` already produces the four eigenvalues (control C2 fires at
`4.4e−16`) — and the ideal computation is a standard Sage call in the splitting field.

Pre-committed readings:

- **`(α₁) = (α₂)` at every tested `(p, a)`** ⇒ the ratio is a unit, Kronecker applies, and the 120°
  law reduces to pinning the order of a root of unity in `μ₁₂` — a Stickelberger computation with a
  template on file. The cap follows.
- **The ideals differ** ⇒ the ratio is not a unit, **Kronecker does not apply, and this whole route is
  dead.** A clean falsifier, and the 120° law would then need a mechanism nobody has proposed.

Order of work: (i) the ideal test above; (ii) the `ζ₃ ∈ splitting field` check of §6, which is forced
and therefore an **instrument check** — if it fails, the eigenvalue computation is wrong, not the
theory; (iii) only then the Stickelberger computation, and only after the citation is re-verified.

⚠ `experiment-designer` prereg before any sweep, and read
`PREREG_D2_lang_hypergeometric_relin_v1.md` first — this is D2's territory and it already has a spec.

---

## §8 — What this document claims and does not

**Claims (all `[MINE — in-session, UNVERIFIED]` unless marked):**
`H¹_c(E, L_{χ₂(y)}) = H¹(A_new)` with L1 as the `a=0` consistency check; the rigidity budget of §2;
that the `μ₃`/`μ₄` equivariance mechanisms **fail for `a ≠ 0`** (this one is a two-line computation
and I am confident in it); the restatement `α₂/α₁ ∈ μ₃`; the Kronecker reduction; the structural match
to the Jacobi proof; the forced `ζ₃ ∈ splitting field`.

**Does not claim:** that the cap is proved — §4 is conditional on an ideal equality that has not been
computed at a single prime; that Stickelberger applies — its citation is unverified and its
applicability to this object is asserted by analogy, not checked; that the order is 3 — Kronecker
gives only "a root of unity" (§6).

**Retracts:** the `μ₃`-orbit-of-ramification-points mechanism (`SYNTHESIS_brainstorm_seven_cycles_v1.md
§1.3`) and the `μ₃ ⊂ μ₁₂ ⊆ Aut(C)` mechanism (`..._ADDENDUM_1_v1.md §2.4`). The `A_new`-channel
framing they were attached to **survives and is strengthened**; only the proposed mechanism was wrong.

**Scale banner #5 governs the empirical rows.** The 120° law is measured at `p ≤ 547`.
