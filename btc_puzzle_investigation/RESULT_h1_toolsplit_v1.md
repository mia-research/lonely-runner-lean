# RETRACTED — H1 was already proved (v2, 2026-07-21); this document's "open" premise is false

*2026-07-24. This file originally framed H1 as OPEN and presented a "reduction" and "one-tool
refutation" as new work. **That premise is wrong.** H1 = P1 = `(−1)^N = χ₂(2)` is a COMPLETE THEOREM
in `RESULT_flap_lemmas_P1P2_proofstatus_v2.md` (2026-07-21). Retained only as a record of the error.*

## What actually happened
- **H1 was proved two days earlier.** `RESULT_flap_lemmas_P1P2_proofstatus_v2.md`, Steps 1–6:
  `N = μ_ρ − M`; `μ_ρ` odd; `M = W` (multiplication by ρ); `W = S(ρ) − S(ρ−1)`; Eisenstein's lemma
  (with the even-`a` case `S(2b)=2S(b)+μ_b`); assemble via `χ₂` multiplicativity ⇒ `(−1)^N = χ₂(2)`.
  Correct and complete.
- **I did not read it.** I took the "open" framing from `NEXT_DIRECTIONS §2/§4` and
  `OPEN_ITEMS_LEDGER #8` — both **stale** — and re-derived the whole theorem.
- **My "crux" `G(a)+μ_a ≡ (a−1)(p²−1)/8 mod 2` is a repackaging of v2's Step 5**, unifying its
  odd/even split into one line. Same tools (Eisenstein / Gauss floor sum), same result. **No new
  theorem.** (It is verified exhaustively — 29077/29077 — but it verifies an existing result.)
- **The "one tool" refutation** (`(†)` needs class numbers, H1 needs Eisenstein) is a **correct
  framing but not a discovery**: v2 already proved H1 with Eisenstein's lemma, not the class-number
  machinery. My `h`-independence argument is a clean way to *state* the orthogonality; it did not
  find it.

## The only real byproduct — a record inconsistency, now fixed
`NEXT_DIRECTIONS §4`'s "two open items, one tool" and `OPEN_ITEMS_LEDGER #8` listed H1 as open,
contradicting v2's Jul 21 proof. Ledger #8 conflated the **proved** H1 lemma
(`|T⁺|≡0 mod6 ⟺ χ₂(2)=1`) with the **genuinely open** `L1` (`|Σ_{T⁺}χ₂|=F4`). Corrected in
`OPEN_ITEMS_LEDGER_v1.md`.

## Process failure (recorded, not excused)
Third un-checked-prior-work miss this session (v38 for `(†)`'s setup; v2 for H1 entirely). The fix is
mechanical: **read the flap/FLD `RESULT_*` files before any flap work.** The `H1 = F(ρ)−F(ρ²)`
reduction and the numerics in the original draft are all correct — they just re-derive `RESULT_flap_
lemmas_P1P2_proofstatus_v2.md`, which is where the credit belongs.
