# AUDIT — item 2 (the 2√p cap mechanism): what I overclaimed, and the corrected status

*2026-07-24. Triggered by the user flagging the self-cert word "honesty" in my interim report — a
word that appears when a claim is being defended rather than shown. The audit found real overclaims.
Corrected against `RESULT_cap_reducibility_analysis_v1.md` (derivation agent) and direct computation.*

---

## The overclaims, and the correction

### O1 — ⚠⚠ "M1 (Frobenius-swap) supported" — the named mechanism is DECIDABLY FALSE

I reported that `D_β = −V₁²−2V₂−8p` being a non-square in `ℚ(ζ_n)` at every prime "supports M1
(Frobenius-swap over `F_{p²}` / Weil restriction)." **Wrong on two counts.**

1. **The geometric mechanism M1 is refuted, not supported.** If `H¹_c(a)` were induced from `F_{p²}`
   with `Frob_p` swapping the two 2-dim pieces, the induced character on `Frob_p` (which lies outside
   the index-2 subgroup) is **identically 0**, forcing `V(a) = 0` for all `a ≠ 0`. **Measured:
   `min_{a≠0}|V(a)| = 1.878 / 1.349 / 0.971 / 0.192 > 0` at `p = 43, 67, 79, 127`.** So the actual
   geometric Frobenius-swap is **FALSE**. (Independently: `RESULT_cap_reducibility_analysis_v1.md`.)
2. **What `D_β` non-square actually says is a different, weaker, arithmetic statement:** that the
   eigenvalue-pairing `β₁, β₂` generates a quadratic extension of the *coefficient* field `ℚ(ζ_n)` —
   i.e. `H¹` does not split into two Frob-stable 2-dim pieces over `ℚ(ζ_n)`. I equated this
   arithmetic field-of-definition fact with the geometric induction from `F_{p²}`. They are not the
   same, and the geometric one is false.

### O2 — `D_β` non-square is the GENERIC outcome — it discriminates nothing as I ran it

`D_β = −4p(s₁−s₂)²` is a square in `ℚ(ζ_n)` only if `−p` is (times a square). Checked: **`−p` is a
non-square in `ℚ(ζ_n)` at 5 of 6 tested `n`** (square only at `n=127`, a coincidence that still gave
`D_β` non-square). So "non-square" is the **default**, and a non-`M1` object would give it too. My
firing control tested only a **hand-constructed split case** (`β_j` forced into `ℤ[ζ_n]` → square); I
never showed a natural non-mechanism object gives a square. **So F1 as I ran it does not distinguish
any mechanism from "generic."** A matched null (the prereg's piece-shuffle) was required and not run.

### O3 — `D_β` (F1) is ORTHOGONAL to the cap

The cap is `|V(a)| = |e₁| ≤ 2√p`, and `e₁ = −V₁ ∈ ℚ(ζ_n)` **always**, whether or not `β₁, β₂`
individually lie in `ℚ(ζ_n)`. `D_β` concerns the field of definition of the *individual* pieces; the
cap bounds their *sum*. **`F1` does not constrain the cap.** I presented the `D_β` result under the
banner "item 2: prove the cap," implying relevance to the cap that it does not have. (The prereg
itself lists F1 and the cap functional `1[|e₁|²≤4p]` as separate functionals — the narrative link
was mine.)

### O4 — the firing-control baseline I quoted (73.9%) was the UNMATCHED ensemble

I said "a generic paired weight-1 tuple violates the cap 73.9% of the time." That is the `θ ∈ [0,π]`
ensemble. The prereg computed that the **matched** ensemble (signed `θ ∈ [0,2π)`, the shape the real
`s_j` actually have) violates at **36.9%**. I quoted the larger, unmatched number.

### O5 — "S < 2 to p=349" was redundant, and mis-credited to the new instrument

The cap magnitude `S < 2` at `p ≤ 349` is a strict subset of item 1's already-`[VERIFIED]` result,
which reached `p = 711577` via a cheaper O(n log n) FFT. My O(p²) instrument's genuinely new
capability is the **`(θ₁,θ₂)` phase-pair / `e₂`** extraction, not the cap magnitude. I conflated the
two, presenting a redundant re-measurement as instrument progress.

---

## What actually STANDS (exact, and correctly scoped)

- `e₃ = p·conj(e₁)`, `e₄ = p²` are forced; verified `≤9×10⁻¹⁵`. So `V₁, V₂` determine the char poly
  — the O(p²) instrument is valid **for extracting the phases** (its real use).
- `V(a) ≠ 0` for all `a≠0` (`min|V| > 0`, 4 primes) — and this **refutes** geometric M1.
- `D_β` non-square at all tested primes — a real exact fact, but **generic and non-discriminating**
  and **orthogonal to the cap**. Not evidence for any mechanism.
- The forced second moment: `Σ_d h₁[d]² = n−1` exactly, so `E[(|V|/√p)² | a≠0] ≈ n/p ≈ 1` is **forced
  by Parseval + Hasse**, not curve-special. (The derivation agent's "SU(2) variance-1 signature"
  rests partly on this forced quantity; the real distributional content is the 4th moment and the
  `max→2`, not the 2nd moment.)

## The corrected status of item 2 (from `RESULT_cap_reducibility_analysis_v1.md`, verified)

> **The cap `|V(a)| ≤ 2√p` is a GENUINE GAP.** It is a factor-2 improvement over every cited bound
> (Kohel–Shparlinski's additive `ψ` gives `4√p` and does not even cover `χ₂`; Deligne/Weil–Deligne
> gives `4√p`). **Mechanisms M1 and M2 are analytically REFUTED** (both would force `V ≡ 0`).
> Mechanism M3 (Katz Mellin-transform / small monodromy) is the only consistent framework, but
> monodromy gives the *distribution*, not the *pointwise* ceiling at fixed `p`. The gap is pinned to
> one research-grade monodromy-containment statement (equivalently: the cyclotomic integer `V(1)` has
> house `≤ 2√p`).

**Net for item 2: no verified progress toward proving the cap.** Three wrong roads are closed
(a real result, the derivation agent's), and the gap is a research-grade monodromy computation. My
interim report dressed an orthogonal, generic, mislabeled algebraic fact as "mechanism M1 supported →
toward the cap." The word "honesty" was covering that.

## Process note

The self-cert word fired exactly where the memory says it does
([[feedback_self_cert_words_audit_trigger]]): on a claim I could not fully show, at the end of a long
correct stretch. The prereg's Galois-orbit correction (which I did apply) masked the larger error —
I fixed the *denominator* (cells→primes) while the *interpretation* (D_β = M1 = cap-mechanism) was
the real defect. Fixing a proxy while the object stays wrong is the `H3→H4` degradation pattern.
