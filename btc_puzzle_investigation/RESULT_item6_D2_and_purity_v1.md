# RESULT — ITEM 6: `(D2)` is TWO citations, one already discharged; and A3 "purity at every embedding" is now VERIFIED BY COMPUTATION

**Date:** 2026-08-01. **Script:** `purity_every_embedding_item6_v1.sage`.
**Grade:** label finding `[VERIFIED — documentary]`; A3 `[VERIFIED — exact, p ∈ {43,67,79,127}]`.

## 1. `(D2)` is an ambiguous label — the record uses it for two different citations

| label use | citation | status |
|---|---|---|
| `ANALYSIS_n1_cap_anew_channel_kronecker_route_v1`, `SYNTHESIS_curve_structure_and_new_directions`, `ADDENDUM_2` | **Stickelberger** | **DISCHARGED 2026-07-27** (`ADDENDUM_2 §B2.1`, Katre's text in hand, three caveats) |
| `RESEARCH.md` thread #2, `RESULT_nonarchimedean_purity_statement_v1` | **Weil II / Katz–Sarnak sheaf purity** | **OPEN**, 4 verifier failures |

**And item G's reading list is attached to the wrong one.** `STRUCTURAL_IMPLICATIONS §8 item G` says
*"Discharge (D2) by hand … read Ireland–Rosen Ch. 14 and Berndt–Evans–Williams Ch. 11 directly."*
Those are **Gauss/Jacobi-sum** texts — the natural follow-up for the **Stickelberger** citation, which
`§B2.1` itself names in exactly those words (*"did not open Ireland–Rosen Ch. 14, Washington §6, or
Lang — the natural next textbook if a canonical citation is wanted"*). **They cannot discharge
Weil II 3.2.3, which is Deligne, not a classical textbook.**

So item G, executed literally, would have re-read the follow-up list for an already-discharged
citation while leaving the open one untouched.

## 2. What IS checkable — and why varying `a` was not enough

The record separately carries **A3 = "purity at every embedding", `[CITED]`, UNTESTED**, flagged
load-bearing for the cap chain. Archimedean purity had been verified only as *"`|root| = √p` for
every `a`"* at `p = 43,67,127`.

**That is not the same statement.** The record's own
`RESULT_anew_twisted_eigenvalues_nonabelian_v1` shows the eigenvalue field is **non-abelian**, so the
Galois action is *not* the relabelling `a ↦ ua`, and sweeping `a` does **not** exhaust the embeddings.

## 3. The exact discharge

`R(T) = ∏_{a=1}^{n−1} P_a(T)` is Galois-stable, hence lies in `ℤ[T]`, and **its root set is closed
under every embedding of the splitting field.** So "all roots of `R` have modulus `√p`" **is** purity
at every embedding — and for `R ∈ ℤ[T]` that is decidable exactly:

> `R(T) = T^m·Q(T + p/T)` with `Q ∈ ℤ[S]` having **all roots real and in `[−2√p, 2√p]`.**

Input is the *proved* collapse (`e₂ = e₁² − εp` — the #26 theorem — plus `e₃ = −p·e₁`, `e₄ = p²`), so
`P_a` is determined by `e₁(a) = −V₁(a)` alone. **Nothing is cited.**

| p | n | deg `R` | ℤ-coeffs | `R = T^m Q(T+p/T)` | `Q ∈ ℤ[S]` | `Q` roots real | in band | max ‖root‖−√p |
|---|---|---|---|---|---|---|---|---|
| 43 | 31 | 120 | ✓ | ✓ | ✓ | ✓ | ✓ | **0.000e+00** |
| 67 | 79 | 312 | ✓ | ✓ | ✓ | ✓ | ✓ | **0.000e+00** |
| 79 | 67 | 264 | ✓ | ✓ | ✓ | ✓ | ✓ | **0.000e+00** |
| 127 | 127 | 504 | ✓ | ✓ | ✓ | ✓ | ✓ | **0.000e+00** |

> **A3 moves `[CITED — untested]` → `[VERIFIED — exact]` at these primes, with no appeal to Weil II
> or Katz–Sarnak.** The general-`p` statement still rests on the citation; but the check is
> *decidable and cheap*, so the scope can be widened by compute rather than by reading.

## 4. An instrument fault caught before the verdict was read

The first pass reported `Q has all roots REAL: False` at **every** prime and a spurious
`max‖root‖−√p = 6.1e−01` at p=127. Both were mine:

- `e₁` is constant on μ₃-classes, so each distinct quartic occurs with **uniform multiplicity 3** in
  `∏_a P_a`. That makes `number_of_real_roots()` (**distinct**) < `degree()` (**with multiplicity**)
  *automatically*, and makes degree-504 root-finding ill-conditioned.
- Fixed by taking the **squarefree part** — the Weil property is a property of the root *set*.
  Multiplicity confirmed uniform at 3; the numeric deviation then collapses to exactly 0.

**Also fixed: the script printed its conclusion unconditionally**, i.e. it asserted purity even in
the run where the criteria failed. A conclusion line that does not branch on the verdict is a
liability, not a summary.

## 5. Consequences

- **The `(D2)` blocker should be re-labelled in the record.** "Discharge (D2)" is not one task; the
  Stickelberger half is done and the Weil II half needs Deligne, not the listed textbooks.
- The cap chain's purity input is no longer untested at the computed primes.
- What remains genuinely open: the **general-`p`** sheaf-purity statement (Weil II 3.2.3), which is a
  citation and cannot be discharged by any finite computation.
