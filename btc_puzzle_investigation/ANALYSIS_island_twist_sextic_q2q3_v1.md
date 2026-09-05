# ANALYSIS — island exploration Q2 (twist island / amicable) + Q3 (sextic character)

**Grade: Q2 `[VERIFIED — group is the unique prime face, 3/3 curves]` + `[SYNTHESIS — amicable = carry↔island]`;
Q3 `[structural null — island determines π_n but does not display the symbol]`.** Date 2026-08-17. Follows
`ANALYSIS_island_frobenius_tie_v1`, `RESULT_group_carry_gate_v1`. Grounded in `KNOWN_FACTS_v4` §4. No master
edited.

## Q2 — the twist island (c=−1, n_t) and the amicable pair
The six sextic twists have Frobenius `π_p + u`, `u ∈ μ₆ = {±1, ±ω, ±ω²}`, orders `N(π_p+u)`. By the same
Eisenstein-reduction argument as `RESULT_group_carry_gate_v1`, **each face carries the ¾/3-16 gate** (the
carry law is intrinsic to ℤ[ω] reduction). But:
- **Only the group face `u=−1` (π_n=π_p−1) is prime-order.** Verified: among the six orders, exactly one is
  prime and it equals `n` — p=43 `{31,36,39,49,52,57}`→31; p=61 `{48,49,61,63,75,76}`→61; p=103
  `{84,91,97,111,117,124}`→97. (Matches `KNOWN_FACTS_v4`: "only `π_p−1` has prime norm =n".)
- **Consequence:** the clean *prime-order* ×λ island (order-3 `λ`, clean `CF(λ/n)` three-gap) is **unique to
  the group face.** The other five faces have composite modulus → `λ` need not have order 3, the three-gap /
  CF structure is not clean. The "twist island" exists but is a composite-modulus object, structurally poorer.
- **The amicable pair `(p,n)` = the two prime faces of `Q(c)=N(π_p−c)`:** `Q(0)=p` (FIELD, the carry/lift
  gate on `L_p`) and `Q(1)=n` (GROUP, the ×λ island + its gate on `L`). The longest consecutive-prime run of
  `Q(c)` is `{0,1}` (`KNOWN_FACTS` §4). **So the amicable `(p,n)` IS the field↔group duality — the carry and
  the island are the two amicable partners.** That is the tie the question asked for: the amicable pair is not
  a separate coincidence, it is the pair of prime Frobenius faces that carry the two gates.

## Q3 — does the island geometry SEE the sextic character `[7/π_n]₆`?
`[7/π_n]₆ = 7^{(n−1)/6} mod n` — computed (p=43,B=7,n=31 → 5; p=67,n=73 → 72; etc.; each a 6th root of 1
mod n). Verdict: **NO, not as a geometric display.**
- The symbol requires the extra datum **`7`** (the curve coefficient). The island — gaps, ×λ rotation, carry
  gate — is built from `(n, λ, I)` and **never references 7**.
- The island **determines `π_n`** (its gaps *are* `π_n`'s coordinates), and `[7/π_n]₆` is then computable
  from `π_n + 7`. But it is a **Hecke/L-function object** (depends on `π_n` AND the curve's `7`), not an
  island/carry geometric feature. Island = group-lattice object (`π_n`); sextic symbol = Hecke object
  (`π_n` and `7`). **Different data** — the island sees `π_n`, not the curve-specific residue of 7.
- Honest (not a dismissal): "does not display" is scoped to the observables built here (gap word, carry `ĉ`,
  gate rate), which are `7`-free by construction. A DIFFERENT observable that *feeds in* the point `[7]G` or
  the lift of 7 could carry the symbol — untested; that would be a carry-of-7 object, not the island itself.

## Net across Q1–Q3
- **Q1 `[VERIFIED]`:** the group lattice carries an `ε=0` gate identical to the field carry (¾, `{¾,⅛,⅛}`,
  `3/16`) — `RESULT_group_carry_gate_v1`. The gate is intrinsic to ℤ[ω] reduction, so it lives on every face.
- **Q2 `[VERIFIED + SYNTHESIS]`:** the group is the *unique prime-order* face; the amicable `(p,n)` is exactly
  the field(carry)↔group(island) duality.
- **Q3 `[structural null, scoped]`:** the island determines `π_n` but does not display the sextic Hecke
  symbol, which needs the extra datum `7`.
- **Unifying picture:** `Q(c)=N(π_p−c)` is one Frobenius with many faces; the carry gate rides on all of them;
  `c=0` (field) and `c=1` (group) are the two prime faces = the amicable pair = carry ↔ island.
