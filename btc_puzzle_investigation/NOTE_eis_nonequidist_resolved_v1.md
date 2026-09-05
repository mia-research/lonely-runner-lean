# NOTE — the flagged "non-equidistribution of x([d]G) in the Eisenstein torus" is RESOLVED: my lift-convention bias + a Weil-decaying small-p effect; ZERO at secp in the canonical convention

**Date 2026-08-21; AUDITED/HARDENED 2026-08-22 (user-challenged — see §v2 below).** Governs: the flagged
observations in `RESULT_m40_n15_exact_accounting_v1.md` (§Flagged) and
`AUDIT_ideation_agent_claims_firsthand_v1.md` (Part B2). Scripts: `eis_nonequidist_followup_v1.py`
(+ `.log`), `eis_nonequidist_audit_v2.py` (+ `.log`), + the inline canonical check.

## The resolution (three checks, exact features)

1. **Convention.** My `±2`-neighborhood min-max square-centering is a NONSTANDARD centering: on the same
   uniform-x sample its secp core rate is 0.7776 vs the project-canonical 0.7520 (reproduced: 0.7542),
   and the bias is **p-dependent** (all-x core 0.7525 at p=10⁵ vs 0.7776 at secp — basis-shape dependent;
   pure Babai without the search gives 0.9899 — the parallelogram, not the square). The canonical
   machinery (`lift_uv` + `strip_pred`, verified ⟺ `build.eps` at 200,000/200,000 in
   `RESULT_n16_eps_object_identity_crosscheck_v1.md`) is the reference.
2. **Source of x (canonical convention, secp, N=20,000 each):** uniform-x core rate **0.7542** vs
   curve-x **0.7540** — delta **−0.0002 = 0.05σ**. The QR-support conditioning of the x-map produces
   NO detectable torus deformation at secp.
3. **p-scaling of the real (small-p) effect** (full enumeration, valid primes p≡1 mod 3): the
   support-conditioned deviation decays like ~p^{−1/2} — |dev| ≈ 0.12 @ p=43 → 0.02 @ p≈10³ →
   0.004 @ 10⁵ — the Weil-suppression scaling for the incomplete character sums behind it
   (Σ_region χ₂(x³+7)). At secp it is ~2^{−128}. *(The first run's "growing deviation" trend was an
   artifact of four primes ≡ 2 mod 3 — no cube root of unity, invalid lift — visible as insane rows;
   corrected.)*

## Verdict

- **The flagged observation does NOT survive as an secp-scale arithmetic signature.** The x-map's
  image measure in the Eisenstein torus is equidistributed at cryptographic scale in the canonical
  convention — a *confirmation* of the equidistribution heuristic (positive information), with the
  small-p deformation real, characterized, and Weil-suppressed.
- **Impact on the session (g) results:** none of the M40/N15 conclusions move. The tuple-budget rates
  shift by ~±2.5pt under the canonical convention (H(e) → ≈1.06 per Cap-Law ¾:⅛:⅛; H(tuple) shifts
  ≲0.06 bits) — the conclusions (O(1) ≈ 4.4-bit budget, negative synergy) are robust to the convention.
- **Discipline note:** the flag was raised honestly and resolved against my own instrument — the
  convention check was run because it was named first. The counter-prior cuts both ways: do not inflate
  one's own artifact into a "genuine signature," and the test, not the mood, decides.

## §v2 — AUDIT (2026-08-22, user-challenged): the v1 closure was under-scoped; hardened 10×, canonical predicates — closure CONFIRMED

The v1 canonical check covered **only the core predicate at N=20k** — a real gap (the flag had two
components; a deformation could leave the hexagon rate fixed while deforming the disk rate; and a
⅓-size effect could hide at that power). The audit (`eis_nonequidist_audit_v2.py`) reran everything on
the **project-canonical machinery itself** (`int1_frame_operator_v1.build_secp`: its own `eis`, `eps`,
`enorm`):

**Part 1 — secp, N=200,000 per source (power: resolves ≥0.3% effects, σ ≈ 0.0015):**

| predicate | uniform x | curve x = x([d]G) | delta | z |
|---|---|---|---|---|
| `eps==0` | 0.75019 | 0.74955 | −0.00064 | 0.47σ |
| `eps==1` | 0.24980 | 0.25044 | +0.00064 | 0.47σ |
| `s < 3/16` | 0.68044 | 0.68054 | +0.00009 | 0.06σ |
| `s < 1/4` | 0.80288 | 0.80251 | −0.00037 | 0.29σ |

**Every delta < 0.5σ on both predicate families.** The canonical rates sit exactly on the continuum
(0.75019 / 0.68044 vs 0.75 / 0.68017) — confirming the canonical convention is unbiased and mine was
the deviant instrument.

**Part 2 — canonical scaling (generic `build(p)`, FULL enumeration):** sup-minus-all deviations decay
+0.140@43 → ±0.01@547 → ±0.002@20011 → **−0.0013@100003** (both predicates) — the Weil ~p^{−1/2}
suppression confirmed canonically; canonical all-x rates converge to continuum (0.75011 / 0.68033 @ 10⁵).

**Bonus precision finding:** the canonical `eps` is effectively **BINARY at secp — ¾ : ¼ : 0**
(class 2, the deep flap, is structurally empty at scale: carries beyond ±R1, ±R2 cannot occur when the
lift is ≪ basis lengths). The Cap-Law "¾:⅛:⅛" is a different (sign-refined) partition. Consequence for
the (g) budget: canonical H(e) = 0.811 bits (not 1.0) — the tuple budget shifts to ≈ 4.2 bits;
conclusions (O(1) budget, negative synergy) unchanged.

## Verdict after the audit

The closure now clears the burden bar in full: **object** — canonical `eps`-classes and `s`-rates of
`x([d]G)` vs uniform `x`; **observable class** — marginal Eisenstein-torus rates of the canonical lift;
**power** — 200k/σ0.0015 at secp + full enumeration to 10⁵; **scope** — secp-sampled, generic-prime
enumerated. The anomaly is not there in the canonical world. **As an N15 filter feed, marginal torus
rates are dead on information grounds independent of this audit**: even a 0.1% marginal rate bias would
carry ~2×10⁻⁵ bits, three orders below the record's 0.033-bit filter floor — any alignment filter must
live in joint/structured readouts (the (g) accounting).
