# G1.H Stocktake and Decision Memo (v1)
**Date:** 2026-03-03  
**Scope:** Gap 1 only (prime `n`, one-divisible all-distinct templates).  
**Objective:** choose one theorem-grade route to control/eliminate `E_tm2(F,M)` in `G1.H`.

## 1) Stocktake: innovation -> G1.H term map

| Innovation / artifact | Maps to | Status | Keep? | Reason |
|---|---|---|---|---|
| TM1/TM2/TM3 mechanism (`v11` §14) | `Delta_tr` | PROVED | Yes | Supplies transition law and class-compatibility structure needed for transition-loss accounting. |
| D.1'/G1.B cell cap (`v11` §16.7, §17.7) | `K_loc` | PROVED | Yes | Gives per-cell local cap and explicit endpoint constant. |
| G1.C aggregate cap (`v11` §17.8) | `K_loc` | PROVED | Yes | Converts cell caps into global local constant form. |
| Event-cell partition / boundary-set machinery (`v11` §17.8 + boundary certifier) | `K_loc`, `Delta_tr`, `E_tm2` localization | IMPLEMENTED | Yes | Provides exact partition where obstruction/control terms can be measured and proved. |
| Structural path lemma S2 (`lrc_case2_structural_necessity_chain_v1.md`) | `Delta_tr` | PROVED | Yes | Justifies one-parameter event walk; enables global transition counting rather than product-state counting. |
| BSM prime z-property lemmas (`lrc_s3_proof_prime_n_v1.md`) | `E_tm2` control (supportive) | NON-CANONICAL for final closure | Keep as support only | Useful local residue behavior intuition, but anchor-sum closure route is not canonical for Gap 1. |
| U_s / odd-Bonferroni moment tracks (`lrc_case2_us_lemmas_v1.md`, `lrc_case2_universal_crt_attempt_v2.md`) | Alternative global occupancy bounds | EMPIRICAL/OPEN | No (for immediate G1.H) | Not yet theorem-grade for this route; prior C2-main(C) failure indicates high risk of detour. |
| C2-main(C) and low-order aggregate inequalities | N/A | DISPROVED | No | Explicit counterexample; not reusable for closure. |
| Anchor-only and lower/top-only shortcuts (`lrc_gap1_g1g2_blockers_v1.md`) | N/A | DISPROVED for target role | No | Insufficient alone by explicit counterexamples. |

## 2) Diagnostic evidence relevant to `E_tm2`

A direct obstruction scan using the boundary/event-cell kernel over existing one-divisible check artifacts (`39,946` rows total) gave:

- Prime `n`: obstruction rows `0` for `n in {5,7,11,13,17,19}` (checked windows available in-pack plus low-prime diagnostic).
- Composite `n`: nonzero obstruction observed (notably `n=8,10`; mixed behavior at `n=9`).

Interpretation:

- For the prime Gap-1 scope, `O_tm2(F,M)` appears to vanish in all tested data.
- Composite obstruction behavior is real, but it is outside the immediate Gap-1 prime target.

Scope guardrail:

- This is support evidence only; not a proof dependency.

## 3) Chosen route for `E_tm2` (single route)

### Route EZ (chosen): prove `O_tm2(F,M)=empty` on canonical bands for prime one-divisible all-distinct templates

Target theorem package to add (names suggestive):

1. **Low-band fixed-cover lemma.** On `I_lo`, fixed-side bad residue union is exactly
   `U_fix(b) = {0} union {-e^{-1}: e in E_fixed}`.
2. **High-band fixed-cover lemma.** On `I_hi`, fixed-side union is
   `U_fix(b) = ({0} from at least one fixed speed) union {e^{-1}: e in E_fixed}`.
3. **Cardinality consequence.** Because `n` is prime and fixed residues are distinct (`|E_fixed|=n-3`), inverse residues are distinct, so `|U_fix(b)|=n-2` and therefore `|R_fix(b)|=2` on every event cell in `I_lo union I_hi`.
4. **Obstruction elimination.** `O_tm2(F,M)=empty`, hence `E_tm2(F,M)=0` in `G1.H`.

Then `G1.H` reduces from obstruction-aware to pure transition-vs-local form:

`C_bad(I_tot) <= |I_tot|/n + K_loc(F,M) - Delta_tr(F,M)`.

This removes the current bottleneck term entirely.

## 4) Why this route is preferred now

- It directly attacks the exact open bottleneck (`E_tm2`) in current canonical `G1.H`/`G1.G.2` framing.
- It reuses already-proved canonical ingredients (`§16.9`, `§17.15`, TM machinery) with minimal new machinery.
- It avoids known-failed paths (anchor-only and coarse odd-order aggregate tracks).
- It matches observed prime-scope behavior in all current diagnostics.

## 5) Execution checklist (short)

1. Insert theorem `G1.TM2-prime-band` proving `O_tm2(F,M)=empty` for prime one-divisible all-distinct on canonical `I_tot`.
2. Patch `§17.14` replacing `+E_tm2(F,M)` by `0` under that theorem.
3. Update claim/status rows: promote obstruction elimination in prime Gap-1 scope.
4. Keep composite obstruction remarks out of Gap-1 closure claim text.

## 6) If route EZ fails

Fallback is not a new framework; it is a weakened version of the same route:

- prove a uniform explicit bound `E_tm2(F,M) <= C_F` (or `<= C(n)`) from endpoint/intersection structure,
- then absorb this into `K_loc` and proceed with `Delta_tr` inequalities.

This preserves scope and avoids returning to disproved aggregate candidates.
