# RESULT — Side-channel leak of Dirichlet-island / T-membership: construction infeasibility

**Grade: `[CLOSURE — construction-infeasibility, graded]`.** This is NOT an empirical
null and NOT an ECDLP-security claim. It is a decidable feasibility finding about
whether a side-channel *observable* of island/T-membership can be *constructed* at
all, under the project's disjoint-construction and selection/conversion rules.

Pre-registration route: `experiment-designer` (CLAUDE.md §2 mandatory gate), run in
context isolation (no session narrative, no predetermined conclusion handed in).

## The design question (verbatim scope)

Specify a side-channel observable `O` with all three:
1. `O` is a physically/algorithmically justifiable measurement of a real secp256k1
   execution — a scalar mult `d·G` or an ECDSA signing operation.
2. `O` is a genuine function of the long-term scalar's **island / T-membership**
   (A1.5, A2.9) — which reciprocal-floor island / which T-level `d` occupies — **not
   merely** its bit-length or Hamming weight in isolation.
3. `O` and the target are **disjointly constructed** (not the retraction-24 tautology
   of feature and target both `= f(d)`).

## Verdict: no valid `O`. Requirements 2 and 3 are JOINTLY unsatisfiable.

**Object at the point of failure.** The map `φ : {realizable side channel of a real
`d·G` or ECDSA-sign execution} → {island/T-membership of d}`, subject to disjoint
construction.

**Blocker — basis mismatch.** Island/T-membership is a predicate in the **reciprocal-
floor (Dirichlet) basis** `{⌊lo/q⌋}` (A1.5: the `T=1` stratum is exactly
`{base ± ⌊lo/q⌋ : q≥1}`, `lo=2^{N−1}`; A2.9: three T-levels). No standard secp256k1
scalar-mult or signing algorithm operates in that basis — every such execution is a
function of `d`'s **binary / NAF / wNAF / GLV digit sequence** (and, for signing, of
`d·r mod n`). These two bases coincide at exactly one place: full recovery of `d`.

**The dichotomy (the whole argument).** For any admissible observable `O`:

- **Horn A — `O` does not functionally determine `d`** (ladder step-count, add-count =
  Hamming weight, wNAF nonzero count, GLV split-lengths, partial-bit / partial-nonce
  leaks à la LadderLeak/Minerva). Then **requirement 2 fails**: island/T-membership is a
  *global, all-bits* predicate not carried by any proper subset of `d`'s information.
  - Bit-length: constant in-band (islands and randoms both in `[2^{N−1},2^N)`) → 0 info.
  - Hamming/NAF weight: `⌊lo/q⌋` weight ranges over the whole spectrum (weight 1 for
    `q=2^j`, ≈N/2 for generic odd `q`) and **overlaps random band scalars**. Excluded by
    requirement 2 by name; the residual `I(HW;T)` is exactly the excluded quantity.
  - Partial-bit leaks: for `(n,k)=(2,1)`, `base=3·2^{N−2}` has zero low bits, so the
    low-ℓ bits of an island are the periodic tail of `1/q`, sweeping all `2^ℓ` values
    ≈ uniformly = **the same marginal as a random band scalar** → no admissible T-info.
  - GLV split: reduces `d` against the `λ`-lattice, unrelated to the reciprocal-floor
    lattice → scrambles reciprocal-floor structure exactly as for any `d`.

- **Horn B — `O` functionally determines `d`** (a full doubling/addition or wNAF/GLV
  trace = `binary(d)` etc.). Then `T(d)` is a deterministic post-image of `d`, so
  `O ⊇ d ⊇ target` — feature and target share their whole construction through `d`.
  **Requirement 3 fails** (retraction-24 tautology); the only natural matched null
  (shuffle trace↔scalar) destroys the `O↔d` binding exactly as it destroys any real
  signal. Independently, such an `O` already solves ECDLP, so island-membership is moot.

- **The middle is empty.** T-membership is not determined by any proper subset of `d`'s
  information (Horn A) and is trivial once all of `d` is exposed (Horn B). The reciprocal-
  floor global predicate is not aligned with any coarse weight/length statistic a
  non-recovering channel exposes.

## "Reconstruction complexity" — SELECTION vs CONVERSION (required line item)

`T` = minimal number of reciprocal-floor D-terms to reconstruct the integer `d`
(a minimum-description-length of `d` in the reciprocal-floor basis; D-terms computed
from `d`). Placement:
- It is a function of the integer `d` (computable without the PRNG), so not literally
  "how the bits were drawn"; **but** rule (d) names *description length / "reconstruction
  complexity" as a chosen property* as the **SELECTION side (banned)**. Reconstruction
  complexity *is* a description-length → lands on the banned side by the letter of rule (d).
- It is **also not "what the curve did to `d`"**: scalar-mult and signing neither compute
  nor branch on `T`; a `T=1` and a `T=2` scalar of matched binary profile produce
  **identical executions**. Not a conversion-side quantity either.
- **Finding:** reachable from the conversion side only by first recovering `d` in full,
  at which point it is a post-hoc function of the recovered key (the tautology), not an
  independent observable. Not admissible as a disjoint side-channel target on either read.

## The closure, graded (object + class + power + scope + falsification)

- **Object:** the map `φ` above.
- **Class closed:** all timing / cache / power / EM / step-count / NAF-window / GLV-split
  observables of a real `d·G` or ECDSA-sign execution — any function of the algorithm's
  operation sequence and operand-arithmetic patterns (= requirement-1's class).
- **Power:** the obstruction is **structural, not a power limitation** — it holds at every
  `N`, every trace count, every SNR, because the observable's basis (binary/NAF/GLV/
  modular) is invariant to the target's defining basis (reciprocal-floor) except at full
  recovery of `d`. Stated explicitly so this reads as a named construction obstruction,
  not "not found = failed search."
- **Scope — what this does NOT close:**
  1. Real secp256k1 side-channel leakage in general. LadderLeak / Minerva / EUCLEAK /
     HNP+lattice leak **binary-basis nonce bits** and recover keys — a *different target*
     (binary/modular, not reciprocal-floor). This closure says nothing against them; they
     work. The motivating proposal's premise — that these attacks leak a key's
     "reconstruction complexity" / island-membership — is the specific thing shown false.
  2. The already-registered **curve-image joint-set** test
     (`PREREG_islands_curveimage_jointset_v1.md`), which reads the curve *image*
     `x(·),y(·)` — genuinely disjoint from the scalar's reciprocal-floor label — and is
     valid and unaffected.
  3. A hypothetical deployed reciprocal-floor-basis scalar-mult (see falsification).

## Falsification (what would make a valid `O` exist)

A real secp256k1 execution whose **operation sequence is a function of the reciprocal-
floor decomposition depth `T` while not determining `d`** — e.g. an implementation that
natively computes `d·G` by summing reciprocal-floor terms `{⌊lo/q⌋·G}` (a "Dirichlet
ladder"): a `T=1` scalar runs one term-addition, a `T=2` scalar runs two, so `O` =
term-addition count = `T` in the reciprocal-floor basis (req 1 + req 2 hold; req 3 then
needs a fresh disjointness check — plausibly passes, since term-count leaks `T` without
`d`). **No standard library (libsecp256k1, OpenSSL, BoringSSL, …) implements this**; the
reciprocal-floor basis is a d-side *analysis* artifact, not an algorithmic representation.
Its absence is the blocker — named at the object level, decidable.

## Provenance

- Object defs: `PROJECT_SUMMARY_secp256k1_v1.md` §B.7 (A1.5, A2.9; d-side, "no leakage
  or ECDLP claim"), A2.8 (islands live on the scalar side of the `d↦(X,Y)` bijection).
- `T` def: `btc_puzzle_findings_v1.md` §1.2; `nested_recursion_worked_example_v1.py`.
- Rules applied: `btc_puzzle_investigation/CLAUDE.md` — no-float signal path;
  matched-null + firing control; burden-of-proof on closure (c); selection/conversion
  boundary (d). Disjoint-construction template: `PREREG_islands_curveimage_jointset_v1.md`.
- Related retractions: retraction-24 (feature/target tautology).
