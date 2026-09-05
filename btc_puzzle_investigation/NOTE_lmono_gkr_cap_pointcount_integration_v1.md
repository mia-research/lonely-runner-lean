# NOTE — folding the ζ₃/cap trace identity into the L-mono GKR campaign (cross-session integration)

**Date 2026-08-25.** Cross-session input (relayed via the user): *"the ζ₃/cap items reinforce the
L-mono GKR campaign (independent point-count witness), and add the p mod 4 regime split — merge into
that frontier."* This NOTE grounds and records that merge. It does NOT edit
`PLAN_lmono_monodromy_campaign_v1.md` (that PLAN is v1; the owning session should fold §A/§B below into
its §2 banked-inputs table / §5 proof routes). **No grade moves.**

## The campaign, in one line
`PLAN_lmono_monodromy_campaign_v1.md` aims to prove the **ζ₃ relative rigidity** — the per-cell 120° law
`α₂/α₁ = ζ₃` (equivalently the `[2,2]` cross-plane trace identity `Tr(π_a|W') = ζ₃·Tr(π_a|W)`, T2) — is
**forced** by the twist family's monodromy (T3 ⟹ T1/T2), via Katz rigidity / Goursat–Kolchin–Ribet, for
`p ≡ 7 mod 12 ⊇ secp`.

## A. The ζ₃/cap item is an INDEPENDENT point-count witness for T1/T2
`RESULT_n1_cap_reduces_to_one_identity_v1.md` proves (symbolically, verified per-cell at 22 primes) that
the uniform 120° law **and** the cap `|V_y(a)| ≤ 2√p` both reduce to ONE explicit identity between the
`F_p` and `F_{p²}` power-sum traces:

> **S₂ = −S₁² + 2·χ₂(−1)·p**,  with  `e₂ = e₁² − χ₂(−1)p ⟺ θ₂−θ₁ = 120° ⟺ α₂/α₁ = ζ₃`.

`S₁, S₂` are trace-of-Frobenius power sums = **point-count data**. So the campaign's target relation
(ζ₃ pairing of the two rank-2 planes) has an **elementary, point-count-level witness that is independent
of the monodromy machinery**: it confirms the phenomenon T1/T2 *holds* (per-cell, 22 primes) by trace
arithmetic alone. It does not prove the *forcing* (that is the campaign's Katz/GKR job) — but it is an
independent anchor that the target is true, and a cross-check any monodromy proof must reproduce.
**Where it plugs in:** a new row in PLAN §2 (banked inputs), grade `[PROVED — symbolic + per-cell, 22
primes]`, file `RESULT_n1_cap_reduces_to_one_identity_v1`; and a consistency check in PLAN §5 route A
(the tensor-structure shadow test §5.2 should reproduce `S₂ = −S₁² + 2χ₂(−1)p`).

## B. The p mod 4 regime split (the new structure to carry)
The identity's sign factor is `χ₂(−1) = (−1)^((p−1)/2)`:
- **p ≡ 1 mod 4** ⇒ `χ₂(−1) = +1` ⇒ `S₂ = −S₁² + 2p`; the reduced-quadratic discriminant is `3(4−ε²)`
  with one sign convention.
- **p ≡ 3 mod 4** ⇒ `χ₂(−1) = −1` ⇒ `S₂ = −S₁² − 2p`; the conjugate regime.

**secp:** `p ≡ 7 mod 12 ⇒ p ≡ 3 mod 4 ⇒ χ₂(−1) = −1` — secp sits in the **minus** regime. The campaign
currently states T1/T2/T3 for `p ≡ 7 mod 12` (the `χ₂(−1)=−1` arm, incl. secp) and anchors `a=0` at the
supersingular baseline `α=√p·ζ₆²`. The `p ≡ 1 mod 4` companion (`χ₂(−1)=+1`) is the second regime; the
120°/cap phenomenon and its ζ₃ pairing hold in BOTH, but the trace identity and the discriminant sign
differ by `χ₂(−1)`. **Where it plugs in:** PLAN §1/§2 should carry the regime split explicitly — the
ζ₃-rigidity target is uniform, but the point-count witness (§A) and the `a=0` baseline are
p-mod-4-dependent through `χ₂(−1)`. This matters for the D2 certificate's parity-dependent closure
(`RESULT_d2_twist_rigidity_certificate_v1` already notes "exact on both mod-12 arms"; the mod-4 split is
the finer companion).

## Suggested concrete edits to `PLAN_lmono_monodromy_campaign_v1.md` (for the owning session)
1. §2 banked inputs — add row: *"cap/120° trace identity | `S₂=−S₁²+2χ₂(−1)p`, per-cell 22 primes,
   forces the cap as its discriminant + the ζ₃-pairing as its equivalent | `[PROVED — symbolic +
   per-cell]` `RESULT_n1_cap_reduces_to_one_identity_v1`"* — flagged **independent point-count witness**
   for T1/T2.
2. §1 — annotate the `p≡7 mod12` scope with the `χ₂(−1)` = p mod 4 regime split (secp = `−1` arm);
   state T1/T2/T3 as uniform across regimes, the witness + `a=0` baseline as regime-dependent.
3. §5 route-A checklist — add: the tensor-structure shadow must reproduce `S₂=−S₁²+2χ₂(−1)p` in both
   regimes (a decidable numeric cross-check).

## Guard
This is INTEGRATION of an already-`[PROVED]` trace identity into the campaign's evidence base and scope
annotations — it does **not** advance the campaign's open gap (the *forcing* of ζ₃ by monodromy, still
a formulation, not a proof). No grade moves; no claim that the campaign is closer to done than its own
§4/§5 state. Object-matched: the witness confirms T1/T2 *hold*; the campaign must still prove they are
*forced*. (Refuting/《confirming》a phenomenon ≠ proving its mechanism.)
