> **CORRECTION (2026-08-11, caught under review — a suppression):** part (a) below conflated TWO `j`s.
> The **scalar** orbit-index (`d=(−1)^s λ^j d0`) is trivially 0 for small keys (`d0=d`), but the
> **PUBLIC χ3-index** of `x([d]G)` (tool 1, ~1.58 bits) **VARIES uniformly for small keys** (measured
> d=1..40: {0:15,1:13,2:12}). So "puzzle keys give j=0 / the orbit structure gives nothing" is WRONG
> for the public readout — it mislabeled a live public bit as zero. Only the OPEN_d2 **carry** is
> degenerate. Part (b) tested public-χ3 → `d mod 3` but UNDER-POWERED (2 small curves, V_detect≈0.2) and
> a raw table hints at non-uniformity (χ3=2 row 32/37/43) — so the public-readout→d-residue route is
> **OPEN and under-tested, NOT dead.** Superseded framing; a properly-powered test is owed.

# RESULT — T2c (OPEN_d2 known-range route): DEGENERATE for puzzle keys (a), and j does not leak d mod 3 (b)

**Date:** 2026-08-11. **Runs `PREREG_j_range_to_dmod3_v1.md` (frozen) verbatim.** Track 2c — the last
non-circular d-carry route. **Artifacts:** `scratchpad/t2c_degeneracy_v1.py`, `scratchpad/t2c_leak_v1.py`
(+ `.log`). Signal path exact int; only the `gstat` G-statistic is float (ranked vs integer permutation).

## Part (a) — structural degeneracy `[VERIFIED-instance (5 curves) + EMPIRICAL-scaling to secp]`

For a key `d` in bit-range `[2^{b−1},2^b)` with `2^b ≪ m`, `d` is its own `⟨±λ⟩`-orbit-min, so the
OPEN_d2 decomposition collapses: `d0=d`, `j=0`, `s=0`, carry `⌊d0 λ^j/m⌋=0` ⇒ `d mod 3 = d`, a tautology
with **zero constraint**. Enumerated crossover `b*(m)` (all-degenerate at or below):

| p | m | ⌊log2 m⌋ | b* (all-degenerate ≤) |
|---|---|---|---|
| 547 | 547 | 9 | 3 |
| 907 | 967 | 9 | 4 |
| 1303/1669 | 1249/1663 | 10 | 4 |
| 2089 | 2143 | 11 | 5 |

Scaling `b*(m) ≈ ⌊log2 m⌋ − 6` (orbit-min of ~6 near-uniform siblings survives while `d ≲ m/7`).
**Secp corollary** (`m≈2²⁵⁶` ⇒ `b*≈250`): every feasible BTC-puzzle key (`≤ ~130` bits) is deep in the
degenerate regime ⇒ `carry=j=s=0`. **This is the deterministic explanation of the ARSENAL's observed
"all 82 solved keys give c=0, j=0, s=0"** — small-key orbit-minimality, quantified, not coincidence.
The known-range→partial-carry mechanism needs `d` near `m` (a sibling smaller than `d`); it gives
exactly **zero** for the puzzle regime. (secp step is EMPIRICAL-scaling, not proved for all m.)

## Part (b) — leakage `[EMPIRICAL — SCOPED NULL; plant-fired, powered]`

Does the public `j = χ3`-index predict the secret `d mod 3`, quotiented to one representative per
`⟨±λ⟩`-orbit (removing the per-curve φ-forced coupling `d mod3 → (λ mod3)·d mod3`)?

| p | m | U (orbit-reps) | G(j, d0 mod3) permutation p | plant pos_ok | detectable V |
|---|---|---|---|---|---|
| 547 | 547 | 91 | 4298/5001 ≈ 0.86 | True (G_pos=199.7) | 0.26 |
| 907 | 967 | 161 | 4082/5001 ≈ 0.82 | True (G_pos=353.5) | 0.19 |

C1 (within-stratum permutation) control; negative plant `G_neg` in the control band; base rate `d mod 3`
≈ 1/3 (exact marginals reported). **No scan hit.** Pre-committed (§8): **SCOPED LEAKAGE NULL** — the
public `χ3`-index does not predict `d mod 3` beyond 1/3, quotiented cross-orbit, on `y²=x³+7` at
`p∈{547,907}`, U-power detectable `V ≤ 0.26`, plant fired. Conditional phrasing; the below-`b*`
degenerate stratum is a tautology (part a), not a leak.

## Net for the T2 track (recorded straight, scoped)

The OPEN_d2 known-range route joins the eps/carry family as a **powered, pre-registered scoped null**:
- The public Cap-Law flap covariants do not supply the d-carry (`RESULT_eps_to_d_constraint_v2.md`).
- The OPEN_d2 carry is **degenerate** for puzzle keys and the public `j` does not leak `d mod 3` cross-orbit.

So the T2 "public curve-structure → d-carry / d mod 3" avenue, via every feature tested, is null at scope.
**Not enlarged:** larger `p`, other public functions of `x`, multi-point/joint readouts, and **Track 1**
(the `c=±b` phase probe on the −13.99σ deficit — a different object) are untouched. The one durable
positive from the track: `eps` and `j` are public, exact, scale-reaching structural readouts of `x`; they
are simply not the d-carry, and the linchpin-gate distinction (flap vs carry) and the degeneracy law
(part a) are real characterizations of *why*.

## Owed gates
`experiment-designer` pre-registered this (both parts). `citation-verifier` on OPEN_d2 / Cap-Law inputs
before any grade moves up. `compile-diff` if folded into a master.
