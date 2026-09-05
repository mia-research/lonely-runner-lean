# RESULT — H2 (x-closure) IS β/CM-specific, mechanism = GLV relation-triples (do-not-close #4 discharged, CM-affirming; M26 upgraded)

**Date:** 2026-08-24
**Author:** ZCode (Claude). Executes `PREREG_h2_order3_structure_control_v1.md` (mandatory
experiment-designer gate) — the owed β-orbits vs random-order-3-orbits control for M26 /
do-not-close #4.
**Run (frozen, this session):** `h2_order3_control_run_v1.py`, E: y²=x³+7 over
p∈{211,307,421,631,907,1093} (≡1 mod 3, j=0), m=3, |V|∈{9,12}, S=18 instances/arm, K=30 generic
split-order-3 Möbius maps/instance, B=999. Raw: `h2_order3_results_v1.jsonl`. Analysis:
`analyze_h2_order3_v1.py`.
**Grade:** `[VERIFIED — matched control, mechanism identified]`, scoped to these primes / |V| / m.
**Bottom line:** the M26 x-closure boost is **β/CM-specific** — β-orbits beat generic split-order-3
orbits at the permutation-null floor (perm_p=0.001, both |V| arms) — and the mechanism is the **GLV
endomorphism relation** `P + λP + λ²P = O` (each β-orbit is a relation-triple). M26's CM label
**survives and is upgraded**; do-not-close #4 discharged in the CM-affirming direction.

---

## 1. Preconditions (all met)

| check | result |
|---|---|
| **P-a** (φ=β, β² must give quo(Vinv) EXACTLY) | **36/36 instances exact** — pipeline integrity confirmed; the only quo-preserving Möbius maps are the automorphisms β^i |
| **P-b** (quo rises with #relation-triples) | **6/6 primes non-flat/rising** — e.g. p=211 `[6,24,30,75]`, p=421 `[9,21,30,75]`; the instrument sees relation structure, of a controlled size |
| **Tie-guard** (abstain if ≥50% ties) | |V|=9: 0.19; |V|=12: 0.07 — both **pass**, arms powered |
| **R2 reproduction** | boost present: p=211 R2=1.609 (in the 1.6–2.2 band), ensemble β wins 755/1080; single-seed anchors are noisy (some negative) — which is exactly why the design pools 36 instances and uses a permutation null rather than trusting one anchor |

## 2. Primary statistic — CM-specific at the permutation floor

Signed-win `W_obs = Σ 1{quo(Vinv)>quo(V3(φ))} − 1{quo(Vinv)<quo(V3(φ))}`, map-label permutation null.

| |V| | S | W_obs | tie-rate | perm_p | R3_med (β/generic quo ratio) |
|---|---|---|---|---|---|
| 9 | 18 | 224 | 0.19 | **0.0010** | 0.405 (×1.50) |
| 12 | 18 | 344 | 0.07 | **0.0010** | 0.693 (×2.00) |
| pooled | 36 | 568 | 0.13 | **0.0010** | 0.405 (×1.50) |

`perm_p = 0.0010` is the floor `1/(1+B)` — **no** permutation draw reached `W_obs`. β beats generic
split-order-3 in 755/1080 (70%) of comparisons. This is decision-rule **outcome 1**: β/CM-specific,
p≤0.01, R3_med>0 above floor, tie-guard passed, plants fired.

## 3. Mechanism — the CM effect is EXPLAINED (relation-triples)

Per the pre-reg's mandatory §(c) readout (a bound is not a verdict — name the mechanism):

| n_rel (relation-triples in base) | mean quo | n |
|---|---|---|
| 0 | 11.8 | 1071 |
| 1 | 17.4 | 9 |
| 3 | 15.8 | 25 |
| 4 | 36.6 | 11 |

`quo` tracks `n_rel`, and — decisively — the **9 generic φ-orbits that accidentally form
relation-triples** (n_rel>0 among the non-CM maps) also show elevated quo (17.4 vs 11.8). So the
boost is not "β the label" but "β-orbits are **relations**": `{x, βx, β²x} = {x(P), x(λP), x(λ²P)}`
with `P + λP + λ²P = (1+λ+λ²)P = O`, because `λ` is the GLV/CM endomorphism (`λ²+λ+1≡0 mod N`).
Generic split-order-3 Möbius orbits are x-coords of curve points with unrelated discrete logs whose
points do not sum to O. **W_obs significant AND quo tracks n_rel ⇒ CM = the factor base carries k
free relations.** No second mechanism is indicated (the generic-orbit exceptions are exactly the
accidental relation-triples).

## 4. Cryptographic reading (scoped, disciplined)

The relation `P + λP + λ²P = O` is the **known GLV/automorphism relation** — the structure behind the
well-understood `√(#Aut)` index-calculus / Pollard-rho speedup on curves with CM (Gallant–Lambert–
Vanstone; Wiener–Zuccherato). H2 confirms that this structure is **real and CM-specific** at the
factor-base / relation-yield level, and distinguishable from generic order-3 closure. But it is a
**constant-factor** effect (the automorphism group is finite, order 6 at j=0), present at
secp256k1 (which has the GLV endomorphism), and it is **not a keyspace reduction** — a `√6`-class
speedup on a `2^128`-scale problem leaves it at `2^128/√6`. The finding upgrades the *characterization*
(the boost is CM-specific, mechanism named), not the threat model.

## 5. Disposition

- **M26** → the CM x-closure label **SURVIVES**, upgraded to
  `[VERIFIED — matched control; CM-specific vs generic split-order-3; mechanism = GLV relation-triples]`,
  scope {p∈[211,1093], m=3, |V|∈{9,12}}. The audit's over-labeling concern is **resolved in M26's
  favor** — but with the mechanism pinned (GLV relations, a known constant-factor structure), not left
  as a vague "novel CM effect."
- **Do-not-close #4** → **discharged** (β-orbits vs random order-3 orbits: β wins, CM-specific).
- **Contrast with H-5** (this session): the *relation-yield* lever (M25/H1) was an artifact
  (cofactor/sampling, `RESULT_h5_cofactor_artifact_v1.md`); the *x-closure* lever (M26/H2) is **real
  and CM-specific**. Two different levers, two different verdicts — each from its own powered,
  pre-registered, plant-checked test. The x-closure result is a positive that survived; the
  suppression-direction check (was M26 over-labeled?) came back "no, it's real, and here is the
  mechanism."

## 6. Owed / provenance

- Post-run audit vs pre-reg: statistic unchanged, matched permutation null, plants (P-a exact, P-b
  rising) fired, tie-guard enforced, decision taken from the pre-committed cell (outcome 1). Disclosed
  deviation **D-impl-1**: pre-reg |V|∈{6,9} → run |V|∈{9,12}, because m=3 decomposition x-coords require
  ≥3 seed-orbits (|V|≥9); larger |V| is power-favorable (fewer ties) and does not change the contrast.
- Scope hard limit: model primes p∈[211,1093]; no 256-bit, ECDLP, or key claim. The `√(#Aut)`
  cryptographic context (§4) is the standard, published GLV speedup, cited as context, not a new claim.
- Folding this + the H-5 results + N16 + the Move 2 gate into the ledger is the next step (a
  v15/addendum → `compile-diff` gate).
