# The perfect-square / rigidity theme — built, not dismissed (corrects reconciliation §4)

**Date:** 2026-08-27. **Trigger:** user flagged that the perfect-square theme was waved off too fast,
invoking the φ(n)-AP rigidity precedent from the Lonely Runner work (a perfect equidistance that any
minute permutation destroyed — the fragility was the *tell* the structure was load-bearing). That is
the one-way suppression reflex firing (`feedback_suppression_bias_asymmetric_2026_08_02`). This file
builds the four objects instead of grading them from the armchair. **Supersedes
`ANALYSIS_external_claims_reconciliation_v1.md` §4.**

**Method note (no-float discipline).** Item 2 was first checked with a float script (`sq_theme.py`,
`numpy.roots`) — a lapse, caught immediately: checking a *perfect-square / exact-multiplicity* claim
with float is self-undermining (float reports "distance 0.0" for non-squares too, §3b). It was
**redone exactly** in `scratchpad/sym3_exact.py` (6th-root-of-unity exponent arithmetic — integer /
symbolic only), which both reproduces the result and strengthens it (the exponents are p-independent,
so the proof covers the whole p≡1 mod 3 supersingular class, not one prime). Items 3a/3b use exact
`sympy.discriminant` + `isqrt`; `floatcheck.py` uses float only to *demonstrate its own failure*.

## Verifications (this session)

| # | object | result | grade |
|---|---|---|---|
| 1 | Frob³ char-poly = perfect square ⟺ 120° law | = our **PROVED** identity `e₂=e₁²−χ₂(−1)p` (Galois descent on E[2], `RESULT_26_PROVED_weil_restriction_v1`); the `e₂→e₂+1` breakage is the existing negative control (`ANALYSIS_120deg…v1`) | **PROVED** |
| 2 | Sym³(H¹_new) → deg-10 perfect square | **PROVED exact (p-independent), no float:** eigenvalue 6th-root exponents {2,4,1,5} ⇒ u³=(−1)^e={+,+,−,−}; the 20 Sym³ monomials fall in collapse-classes **{4,6,6,4}** by #(ζ₆-type factors); Frob³ signs = (−1)^(Σe) give **10×(+p^{9/2}) + 10×(−p^{9/2})**, so char poly `= (T²−p⁹)¹⁰ = [(T²−p⁹)⁵]²`. Exponents are p-independent ⇒ holds for the whole class. | **VERIFIED — exact, p≡1 mod 3 class** |
| 3a | deg-5 `Q₅` disc (p=43, x³+7) | **VERIFIED exact:** `disc(Q₅)=3232881138118736415293440000 = 56858430668800²` (exact isqrt). Galois `C₅`. Independent of C2. | **VERIFIED — exact** |
| 3b | deg-23 `Q₂₃` disc (E′/F₄₃, n=47) → A₂₃ | **conclusion correct BY THEORY** (Q(ζ₄₇)⁺ has Galois `Z/23`; an odd-order cyclic group ⊆ Aₙ). **But the cited certification is invalid:** a float "0.0 distance to nearest integer" cannot certify a perfect square at ~758-digit scale — float64 *overflows*, and demonstrably returns "dist 0.0" for a non-square too. | conclusion **CITED-theory**; certification **INVALID (no-float)** — needs `isqrt(disc)²==disc` |
| 4 | cubic-residue class A → `(X²−p)²`, eigenvalues ±√p doubled | = our class-A case (`ANALYSIS_L3…v1`) | **VERIFIED** |

**Correction to reconciliation §4.** I graded Sym³ "wrong object / false for p≡2 mod 3 / overclaim." The
*object* is indeed distinct from our L⁽³⁾ base-change, but the claim is **forced and true** in the
p≡1 mod 3 class (which contains secp, p≡7 mod 12), with exactly the stated {4,4,6,6} multiplicities.
The p≡2 mod 3 caveat still stands (there Frobenius swaps the μ₃-eigenspaces; structure differs, untested).

## The rigidity, taken seriously — and where it stands

The theme is **real and largely PROVED**, not decoration: it *is* the ζ₃/cap chain, the programme's
main positive, and it feeds the cap `|V|≤2√p`. The φ(n)-AP analogy is apt in **shape** (rigidity =
tell). One structural difference decides the leverage question, and it must be stated without
deflating:

- φ(n)-AP was an **extremal/exceptional** configuration — informative about *which* n — fragile to a
  *realizable* perturbation.
- The perfect-square here is a **proved universal identity** — `e₂=e₁²−χ₂(−1)p` holds for **every** a
  and every odd-n curve. It is fragile only to a **non-realizable** perturbation (`e₂+1` is not a
  curve). Its *universality* is precisely why, as it stands, it reads as a **fence** (constant across
  secrets) rather than a **lever** (varying with them): the class-B square value `(T²−p³)²` is
  identical for every a in the class (`ANALYSIS_L3 §5` — "zero information about a").

**The one channel where leverage could still enter is the a-dependence** — *which* square-class a lands
in (A vs B; the collapse order). That is secret-adjacent, but it equals the cubic-residue class =
cubic character χ₃(a), measured at **0 bits toward d** (D1, `POSITIVE_FINDINGS_ADDENDUM_4` D1).

**Not closed (BTC stance: an empirical 0-bit ≠ a dead avenue).** The live, non-dismissive probe: is
there a square-structure observable that separates a *more finely* than χ₃(a) already does — the exact
`Q₅`/`Q₂₃` coefficient vector, the collapse order, or cross-class interference — carrying structure the
cubic character does not? That is the question the rigidity actually poses, and it is open. What is
*not* open: the math of items 1–4 (proved/verified above), and the claim that the *universal* square
value alone (χ₃-blind) is a lever (it is a-constant).

## Owed
- Re-certify the deg-23 (and any large-disc) perfect-square claim with **exact `isqrt`**, never a float
  distance. Flag any other "distance-to-nearest-integer" certifications in the external pastes.
