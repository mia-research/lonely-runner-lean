# Reconciliation of an external 6-section claim paste against the KB

**Date:** 2026-08-27. **Object:** a pasted set of six graded claims (splitting-field
parity / big monodromy / CM-type phase-lock / Sym³ perfect square / Kummer descent /
cubic-twist mult-3 spectrum), checked against `btc_puzzle_investigation/` records and the
secp memories. **Net grade of the paste: a real grounded core, but grades systematically
inflated, two objects absent from the KB, and one item sitting on a standing correction.**
No master edited. Curve arithmetic verified exactly (no float) in `scratchpad/check_curves.py`.

## Verified directly (object-level, exact integers)
- **E′: y²=x³+x+3 / F₄₃ has order 47 (prime).** ✓ = our negative-control curve, finding
  **C3** in `POSITIVE_FINDINGS_ADDENDUM_4_v1.md`.
- **E: y²=x³+14 / F₁₉ has order 13 (prime).** ✓
- **W²+26W+117** has disc 208 = 16·13 → roots −13±2√13, splitting field **Q(√13)** ✓.
- **CM by Q(ζ₁₂)** for A_new, CM-type Φ={σ₁,σ₅} a valid type, ζ₁₂⁴ = ζ₃ ✓ (arithmetic).
- **"square discriminant ⟹ Galois ⊆ Aₙ"** is exactly the criterion of finding **C2**
  (p=43, x³+7 → quintic Q₅, disc = 56858430668800², Galois = C₅).

## Per-section verdict

| § | Paste's object | KB status | Paste grade | Verdict |
|---|---|---|---|---|
| 1 | E′/F₄₃, n=47, [1²³] split; A₂₃; **A₁₈₄ tower** | C3 **[VERIFIED @ ℓ=281,283 only]**; **A₁₈₄ absent** | PROVED | curve grounded, **grade inflated**; 184-dim tower not in KB |
| 2 | **40-dim P₄₀ tower, Sp₄/SL₂ big monodromy**, cycle types ℓ=3,11,19,23,53 | **absent**; our object is **rank-4 SL₂·μ₃·{±}, a CONJECTURE** (`PLAN_lmono_monodromy_campaign_v1`) | VERIFIED | **object absent** + invalid inference |
| 3 | CM Q(ζ₁₂); α₂/α₁ = ζ₃ | CM-type ✓; **ERRATA on ζ₁₂** (`ANALYSIS_L3…v1 §3a`; `feedback_verify_root_system…`) | PROVED | ✓ as CM-endomorphism action; **overclaim + ζ₁₂ flag** |
| 4 | **Sym³(H¹_new)** deg-20, mult 4,4,6,6, =[Q(T)]² | **different object**; ours is L⁽³⁾ Frobenius base-change of deg-4 N_a = (T²−p³)² **[VERIFIED-scope]**, mechanism **CITED** | PROVED | wrong object; **false for p≡2 mod 3 (0/40, our D2)** |
| 5 | ζ₄₇⁺ Kummer descent, ℓ≡±1 mod 47 → [1²³] | C3 (2 primes) | PROVED | grounded, **grade inflated** |
| 6 | p=19 twist, n′=13, Q₆=(W²+26W+117)³, Q(√13) | **not in KB**; C2 is the p=43 analogue (same μ₃ mult-3 mechanism) | PROVED | not in KB, **consistent by analogy**, arithmetic clean |

## The three load-bearing problems
1. **ζ₁₂ (§3, §4) is on a standing correction.** The Frobenius eigenvalues of A_new are
   **√p·(primitive 3rd/6th roots)**, verified against the defining polynomial (`ANALYSIS_L3
   §3a ERRATA`; dedicated memory `feedback_verify_root_system_against_defining_polynomial_2026_07_20`).
   ζ₁₂ is legitimate ONLY for the CM field / the CM-endomorphism action on Cot₀ — not for
   Frobenius eigenvalues. §3's α₂/α₁=ζ₃ is right *as a ratio of ζ₁₂-embeddings* but our own
   D3 flags conflating the within-block ratio α₂/α₁ with the between-block phase ᾱ/α.
2. **The perfect-square (§4) is residue-conditional, not "forced."** Our D2 proves it FALSE
   for p≡2 mod 3 (0/40 twists). secp is p≡7 mod 12 ⊂ p≡1 mod 3, so it applies there — but
   the paste drops the hypothesis and over-grades a CITED mechanism to PROVED.
3. **Two objects (A₁₈₄ tower §1, P₄₀/Sp₄ §2) have no home in the KB.** Our monodromy object
   is rank-4 SL₂·μ₃, a conjecture under campaign with an owed GKR computation — not a
   verified degree-40 Sp₄. And "even cycle types ⊆ Aₙ ⟹ non-abelian" is a non-sequitur:
   Aₙ-containment is consistent with abelian groups too (the paste's own §1 puts ℤ/23 ⊂ A₂₃).

## Ledger context (unchanged by the paste)
None of these structures is recorded as an ECDLP lever: the perfect square is the
a-independent scalar p^{3/2} carrying zero info about the secret (`ANALYSIS_L3 §5`); the
joint set is "mapped to an exact fence, not a lever" (`secp_joint_set_structure_map` memory);
D1 = 0-bit extraction. The paste makes no ECDLP claim; if built toward one, that is the ledger.
