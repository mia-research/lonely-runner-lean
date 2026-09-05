# RESULT — multi-prime torsion channels (ℓ=7,19): reduced-scale EXPLORATORY null (not the powered verdict)

**Date:** 2026-08-22. Runs the invariant menu of `PREREG_anew_multiprime_torsion_v1.md` at REDUCED scale
(N~270), as the cheap first look before any powered per-ℓ ladder. **Exploratory, NOT the pre-reg's
powered verdict** (which needs N_test≥490 at ≥2 primes per ℓ). No grade promoted.

Generator: `powered_gen.sage` (now emits f_ℓ for every prime ℓ | |A_new|, 3<ℓ≤97). Stats: `val_stats.py`.

## Why the existing powered primes couldn't be reused (pre-reg finding)
`ℓ | p²+p+1 ⇒ ℓ=3 or ℓ≡1 mod 3`, and |A_new| factors differently per prime. The two powered primes
already run for f5 do NOT carry this menu: p=5827 → |A_new|=3·13·433·2011 (only ℓ=13, unreplicated);
p=5839 → 3·11366587 (menu empty). So the class needs its own per-ℓ prime ladder.

## Reduced-scale result (N~270; plant floor ~π=1/4 at this N)

| prime | N | ℓ tested | f_ℓ → d mod m | collapse |
|---|---|---|---|---|
| 1579 | 271 | 7 | no fire; min p=0.066 (m=5) | floor |
| 1663 | 278 | 7 | no fire; min p=0.13 (m=7) | floor |
| 1831 | 292 | 7, 19 | no fire (both ℓ); all m in null band | floor |

- **f_7 across 3 primes: null** — no E=0, no significant recovery (smallest p=0.066, unremarkable over
  the cells × 3 primes). **f_19 (1 prime): null.** Collapse (the FP control) at floor throughout.
- Consistent with the parent f5 (ℓ=3) result: the small-torsion CRT components of Q_d = S([d]G) carry no
  detectable first-order `d mod m` information.

## Reading (banked progress, form-at-scope)
The ℓ=3 (parent, powered), ℓ=7 (3 primes, reduced), and ℓ=19 (1 prime, reduced) torsion channels are
**consistently null**: no first-order leak down to ~π=1/4 at N~270 (ℓ=7,19) / ~π=1/8 at N~490 (ℓ=3).
This narrows the small-torsion direction; it does **not** close A_new. The pre-reg's formal powered
Outcome B for ℓ>3 is **not yet reached** (reduced scale only) — banked as exploratory.

## Owed / decision
- To formalize the powered Outcome B on ℓ=7: two powered primes carrying ℓ=7 (p=5779/5791/6199/6211/6367
  located) at N_test≥490 (~20–40 min compute). Likely Outcome B on current evidence.
- The **untested high-resolution channel** remains the F_{p³} pairing invariants f1–f4 (scoped in
  `SCOPE_miller_pairing_v1.md`: feasible, runtime-heavy; recommended first at reduced scale).
- Matched-control gap: S_closed is premise-only for all ℓ (zeroes the whole A_new part); a d-dependent
  A_new-structure-free control is owed (pre-reg §self-audit (c)).

*No ECDLP/leakage claim. The exploratory null bounds ℓ=7,19 at reduced power/scope only; A_new stays OPEN,
with f1–f4 the named high-value next probe.*
