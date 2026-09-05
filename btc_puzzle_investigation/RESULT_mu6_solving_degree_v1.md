# RESULT — µ₆/ω-symmetry does NOT lower the Semaev last-fall degree (quo-matched): scoped COMPONENT NULL, not an avenue closure

**Date:** 2026-08-13. **Executes:** `PREREG_mu6_solving_degree_v1.md` (frozen, verbatim) — probe P2.
**Driver:** `mu6_solving_degree_v1.py` (Sage 10.9), SHA-256 `a5769101504f94ba16f23f9e354f35ba73637e69c997fab1ab8259a40ee6d060`; extends `semaev_elimination_v1.py`'s `macaulay_stats` by the read-out `d_LF = max{D: fall(D)>0}` only (exact GF(p) linear algebra unchanged). Float guard `check_no_float.sh` exits 0 (signal path integer/GF(p); float only in the sign-flip bookkeeping carve-out). Raw logs: `scratchpad/mu6_step2c.out` (primary, 6 primes), `scratchpad/mu6_step2d.out` (primary+β, 4 primes).

## The question and the pre-closed traps

Does the exact ω-covariance `S_{m+1}(βx₁,…,βx_m,βx_T)=β^κ S_{m+1}` (β³≡1, j=0/CM) LOWER the **last-fall degree** `d_LF` (the binding solving-degree invariant, Caminata–Gorla: solving degree ≥ last-fall degree — CITATION OWED) of the point-decomposition ideal vs a #E-matched non-CM curve? The PREREG pre-excluded the forced statistics: `d_ff` (first-fall) and inconsistent-`d_solv` are leading-form invariants, curve-independent → zero power (Trap A); raw `d_solv` re-expresses the known R1 yield (Trap B). Primary = `d_LF` on **quo-matched** pairs.

## Instrument gate (PREREG §4) — PASSES

| check | result |
|---|---|
| firing plant (split field-eqs vs dense, same Sx & degrees) | `d_LF`: split=20 **<** dense=21 → **FIRES** (reads a 1-degree drop) |
| Trap-A confirmation | `d_ff` = **12 for both** (forced/curve-independent, as predicted) while `d_LF` differs → `d_LF` sees structure `d_ff` is blind to |
| negative control (two independent dense systems) | `d_LF`=21, 21 → **Δ=0** (no spurious signal) |
| `d_LF` liveness across configs | takes distinct integers 19/20/21/34/35 across (|V|, prime) — a live, varying statistic |

*Disclosed plant limitation:* the plant's "high" side was inconsistent (dim=−1), so its 1-degree gap crosses the consistency boundary; instrument liveness is independently carried by `d_LF`'s observed integer variation + the Δ=0 negative control. A consistent-vs-consistent certified-gap plant is the sharpening follow-up.

## Results — both arms exactly zero, quo-matched

**PRIMARY `Δ = d_LF(j0) − d_LF(#E-matched nonCM)`, quo-matched (m=3, |V|=4, `Dmax=24`):**

| p | #E-gap (cap<2√p) | shared quo | j0 `d_LF` | nonCM `d_LF` | Δ |
|---|---|---|---|---|---|
| 523 | 9 ✓ | 6 | 20 | 20 | 0 |
| 541 | 16 ✓ | 6 | 20 | 20 | 0 |
| 547 | 15 ✓ | 12 | 19 | 19 | 0 |
| 571 | 12 ✓ | 6,9 | 20 | 20 | 0 |
| 577 | 15 ✓ | 6,7,16 | 20 | 20 | 0 |
| 601 | 16 ✓ | 6 | 20 | 20 | 0 |

Pooled: **N=6, all Δ=0**, sign-flip two-sided p=1.0.

**β ARM — sharp ω-isolation, within-j0 (β-invariant V vs random V, |V|≈9), quo-matched:**

| p | shared quo | βInv `d_LF` | random `d_LF` | Δ_β |
|---|---|---|---|---|
| 523 | 12 | 34 | 34 | 0 |
| 541 | 6 | 35 | 35 | 0 |
| 547 | 6 | 35 | 35 | 0 |
| 571 | 6 | 35 | 35 | 0 |

Pooled: **N=4, all Δ_β=0**, sign-flip two-sided p=1.0. **The unmatched β arm had given Δ_β=−1 — that was ENTIRELY the yield/quo confound (Trap B); quo-matching removes it and the ω-effect on `d_LF` is exactly zero.**

## Grade, power, scope (PREREG §9 row C)

**`[EMPIRICAL — scoped component null; PROVISIONAL, citation-verifier owed]`.** **Object:** the last-fall degree `d_LF` of the consistent Semaev point-decomposition ideal. **Class:** the binding solving-degree invariant of prime-field summation-poly index calculus. **Power:** the instrument resolves a 1-degree drop (plant) and `d_LF` varies by integers across configs; the observed ω-effect is **exactly 0** (integer equality, not noisy-small) on both arms → a ≥1-degree reduction is excluded at this scope; a sub-integer effect is below resolution (§5). **Scope:** m=3; |V|=4 (primary) and |V|≈9 (β); primes {523,541,547,571,577,601}; quo-matched; #E-matched (|gap|<2√p). At matched quo, µ₆/ω-symmetry does **not** lower `d_LF` beyond the yield-matched baseline; cross-curve and the sharp within-j0 arm agree.

**NOT A CLOSURE of the CM/Semaev avenue** (Trap C, binding). Solving degree is ONE component of total index-calculus cost (`≈ relations × (1/yield) × cost/solve + linear algebra`); this null bounds only that component. Left explicitly open: **(i)** the µ₃-**graded staircase / syzygy-module structure** — the un-projected subspace (§1 caveat): a scalar-`d_LF` null does not close whether the ω-action reshapes *which* syzygies resolve when; **(ii)** m=4/5 (S₅/S₆) — VOID-intractable here (S₆ build >240s), so the null does NOT extend to the un-reached m where an ω-effect could be stronger; **(iii)** the R1 **yield** channel is a separate, real positive (grows ~log|V|) untouched by this; **(iv)** the full IC-cost accounting combining yield + solving degree + linear algebra.

## Owed gates (before any grade moves up — a null moves none, so this stands)

- `citation-verifier` on **Caminata–Gorla** (solving degree ≥ last-fall degree, eprint 2021/1611) and on "no competitive prime-field summation-poly index calculus known" (Semaev; Amadori–Pintore–Sala 2017). Per `CORRECTION_semaev_cm_yield_mechanism_literature_v1.md`, the extension-field LFD "stays exponential" literature must NOT be cited as a prime-field secp bound.

## Follow-ups (named, not run)

1. **µ₃-graded staircase probe** — measure the ω-isotypic decomposition of the Gröbner staircase / syzygy degrees (the subspace a scalar `d_LF` cannot see), the correct object for "symmetry supplies syzygies."
2. **Consistent-vs-consistent certified-gap plant** — strengthen §4 by planting a KNOWN `d_LF` gap between two *consistent* quo-matched systems.
3. **Widen (m,|V|,prime band)** where tractable; the shape question (constant vs growing drop) is moot while Δ≡0 but would matter if any cell fired.

## stdout (reproduced, key lines)

```
[FIRING PLANT] I_low(split): d_ff=12 d_LF=20 | I_high(dense): d_ff=12 d_LF=21  => FIRES
[NEGATIVE CONTROL] gen1 d_LF=21  gen2 d_LF=21  => Delta_neg=0
PRIMARY Δ (j0 - nonCM, quo-matched): N=6 Δ=[0,0,0,0,0,0]  signflip two-sided p=1.0000
BETA    Δ_β (betaInvV - randomV, quo-matched): N=4 Δ=[0,0,0,0]  signflip two-sided p=1.0000
  p=523: j0_dLF=20 ncm_dLF=20 Δ_prim=0  Δ_β=0 [βInv@q12=34 rnd=34]
  p=541: j0_dLF=20 ncm_dLF=20 Δ_prim=0  Δ_β=0 [βInv@q6=35 rnd=35]
```
