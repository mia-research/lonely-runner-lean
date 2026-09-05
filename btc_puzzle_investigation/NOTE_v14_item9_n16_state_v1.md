# NOTE — v14 §VI item 9 (N16) is stale on both clauses: cross-check discharged 2026-08-18 (re-verified first-hand 2026-08-21); eps==ε_LBE placed by the 2-D DLP reduction; live residue = the range→carry skew, now exact

**Date 2026-08-21.** Session (e). For the next master pass to fold; no grade in v14 is *wrong* — the
item lists as owed work that is three days done.

## The staleness

`POSITIVE_FINDINGS_MASTER_v14.md` §VI item 9: "N16 `eps == ε_LBE` + the owed `|u−v|≤½ == build.eps`
cross-check on the project script." Both clauses were resolved by three 2026-08-18 files that v14's
source pass did not consume (`RESULT_n16_eps_object_identity_crosscheck_v1.md`,
`RESULT_eis_carry_2d_dlp_reduction_v1.md`, `REVIEW_eis_carry_framing_suppression_v1.md` — same
seam-class as the addendum losses; v14 Part 0.1 does not list them):

1. **`|u−v|≤½ == build.eps`: DISCHARGED 2026-08-18** — 200,000/200,000 IDENTICAL on all three
   comparisons + both real puzzle keys, with the conjugate-basis mechanism (`BP_SECP = A_SP − B_SP`).
   **Re-run first-hand this session: reproduced exactly** (200000/200000, core fraction 0.748925).
   The `CONFIRMED_core_gate_carry_epsilon_zero_v3` conditional is cleared at the `[VERIFIED — exact]` bar.
2. **`eps == ε_LBE`: PLACED (conditional negative)** — `RESULT_eis_carry_2d_dlp_reduction_v1` proved
   ε_LBE = the overflow bit of the GLV halves `(a,b)`, computable cheaply from a candidate `d` but
   2-D-DLP-gated from the public point; so no public per-point map (incl. `eps`) equals it, under
   ECDLP-hardness. Scope corrected same day by the REVIEW: generic-`d` statement; for range-restricted
   keys the gate is at the RANGE difficulty (kangaroo `2^{(k-1)/2}·√6`), and the T2c range route +
   amicable second-equation are OPEN, not dead.
3. **Live residue, advanced this session** — `RESULT_t2c_range_carry_skew_exact_v1.md`: the
   range→carry skew is now an EXACT law ($P_{127}=0$, $P_{128}=0.878$, $P_{129}=0.810$, oscillating
   to ½ by ~145; public interval partition of the range at the strong-skew ks), `[VERIFIED — exact
   integer counts]`. Honest applicability: no exponent movement at any live target (exposed-pubkey
   targets are in the equidistributed regime; the strong-skew ks are address-only/hash-barred).

## Suggested ledger edit (next pass)

N16 row → "cross-check DISCHARGED ([VERIFIED — exact], first-hand re-verified); `eps==ε_LBE` placed
([PROVED — reduction], generic-d; range-scoped open); live continuation = T2c exact skew law + √6
composition + N15 joint readout." Also add the three 2026-08-18 files to the Part 0.1 consumed list.
