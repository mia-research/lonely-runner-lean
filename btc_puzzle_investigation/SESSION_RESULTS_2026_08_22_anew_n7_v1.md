# SESSION RESULTS 2026-08-22 — A_new lever characterization + N7 deficit locus narrowing

Staged for the next master pass to fold (do NOT treat as promoted; grades attach per RESULT file).
All gates this session (experiment-designer ×2, memory-drafter, compile-diff) ran to completion —
nothing provisional. Two threads: A_new (a lever, characterized/mostly-closed) and N7 (an unexplained
positive, narrowed). No ECDLP / key-recovery / leakage claim anywhere.

---

## Thread 1 — A_new as a leakage lever: characterized and mostly closed (with proofs, not failed searches)

Prompted by a strategy review that ranked A_new #1; the source-first pass then found much of it already
worked, and the rest resolved to bounded nulls / a proved obstruction.

- **Pairing / MOV transfer — PROVED dead (re-verified).** Corollary C (`RESULT_anew_bridge_end_to_end_corollary_v1`):
  the end-to-end field always contains MOV's, and MOV on secp is useless (embedding degree (n−1)/6 ≈ 254-bit).
  I re-verified the field-degree identity independently: **2124/2124 cells, 0 mismatches.** `[PROVED]`.
- **ℓ-inversion / GLV-halves lever — already run** (`RESULT_isotypic_trace_lever_status_v1`): affine and
  quadratic factorings through the GLV halves are inconsistent at p=43 (POSCTRL fires, NEGCTRL fails). The
  user flagged this as under-powered (p=43, 15 pts, [PROVISIONAL]) — correctly; it does not close the avenue.
- **R1 scale engine — BUILT (the pre-reg slot-1 blocker discharged).** The prior "Sage hangs above p=43" was
  the O(|A_new|) dlog table + `.order()`, NOT the genus-3 group law. Skipping both, the construction runs to
  p≈2011+ in Sage, no hand-rolling. Generator `scratchpad/anew_p43_validation/powered_gen.sage`; |A_new|=p²+p+1.
- **f5 (ℓ=3 torsion) + f6 (w-coord) — powered Outcome B** (`RESULT_anew_f5f6_powered_outcomeB_v1`): two
  ~6000-scale primes, N_test≈490, plant floor π=1/8; no first-order `d mod m` leak. Bounded closure of these
  two cheap channels.
- **Multi-prime torsion (ℓ=7,19) — reduced-scale exploratory null** (`RESULT_anew_multiprime_torsion_exploratory_v1`).
- **Pairing invariants f1–f4 — NOT built; scoped** (`SCOPE_miller_pairing_v1`): Sage exposes no pairing;
  Miller on the genus-3 plane-quartic Jacobian is feasible but runtime-heavy (~10–20s/pt). **Reassessed as
  likely-null:** f1–f4 read a coordinate of ζ_d = ζ_base^{ℓ(d)}, so a statistical bias there would be an
  F_{p³}-DLP bit-security weakness — the same barrier as Corollary C, not an independent channel.
- **Net:** A_new is a characterized, mostly-closed region — pairing PROVED dead, cheap channels bounded,
  f1–f4 expected-null by the DLP barrier. Not a lever. Documented owed: f1–f4 build (low expected value),
  a d-dependent A_new-structure-free matched control (current S_closed is constant → premise-check only).

## Thread 2 — N7 sub-Rayleigh deficit: locus drill → branch B (global/moment effect), mechanism narrowed

Pivoted here as the stronger target: an *observed, unexplained positive* (mean|U| ~0.1% below matched null,
~8% near-zero excess, Σ|U|² exactly conserved, persistent). Pre-reg `PREREG_subrayleigh_deficit_locus_c_channel_v1`;
result `RESULT_subrayleigh_deficit_locus_c_channel_v1`.

- **The near-zero excess has NO clean (b,c) geometric locus.** Char-vs-null allocation over 5 strata × 3 τ ×
  30 primes: c-axis, c=±b diagonal, bulk c-halves, and c-sign (S-C2) all null char-specifically. **Branch B:
  the excess is a global / moment effect, not a geometric locus.** Next probe (pre-committed): the
  **imaginary-part isotype** and **higher-order phase invariants**; co-occurrence arms S-Cpair/S-mu6 deferred.
- **Weak secondary lead (named, not a finding):** a char-specific *depletion* of near-zeros on the c=0
  (x-only) b-axis, za −4.7/−6.9 at τ=0.10/0.15, √N-rising, NC-floor-clean, **but not τ-robust** (τ=0.05).
- **Two integrity catches (the drill's controls working):** (1) the P5 plant caught a **rate-leak** in the
  first X² (the deficit's own 8% rate excess masqueraded as concentration) → fixed with a rate-invariant
  conditional-multinomial X²; (2) the matched control caught a **forced anisotropy** — char-vs-uniform gave
  c-axis Stouffer **+186**, √N-rising, dominant at all 30 primes, which would have read as a decisive
  "sharpened law," but char-vs-null shows the null piles onto that axis *more* than char. Geometry, not signal.

---

## Owed / open (for the next pass)
- N7: phase-invariant probe (imaginary isotype / higher-order) — where the mechanism now points; needs its
  own pre-reg. b-axis depletion follow-up (τ-robustness + mechanism). S-Cpair/S-mu6 co-occurrence arms.
- A_new: f1–f4 Miller build (low expected value, scoped); d-dependent matched control.
- Memory: consider a feedback note on the two catches (rate-leak-in-isotropy-statistic; forced-anisotropy-
  vs-char-specific = char-vs-uniform is the wrong contrast) — route through memory-drafter.
- Master fold: v15 would carry Thread 1 (A_new closure grades) + Thread 2 (N7 branch-B narrowing); gate with
  compile-diff at promotion.
