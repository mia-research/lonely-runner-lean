# secp256k1 — Working Roadmap (Bricks, not a hole-in-one) — v3, 2026-08-18

**v3 change (upgrades v2's bricks with constructions, not critiques).** Folds in
`ANALYSIS_idea_improvements_and_nogo_relook_v1.md`: **Brick E** now measures the *degree of the
cover-scramble polynomial* (the leading-quadratic structure the Hom=0 wall forces); **Brick C** now
reads *phase on the weight-1 eigenspace* (escaping the forced-magnitude no-go by construction, unifying
the 0.93 shadow with the k=3 channel); **Brick B** absorbs the *CM-lattice unfolding + amicable
second-equation* (idea 3, reopened). Two standing refinements are adopted: the **scale banner blocks
magnitudes, not forms**, and **N18 is scoped-closed** (islands only) with the lattice question reopened.
**PRNG boundary decided (2026-08-18): generator-only — the number-theoretic structure of the key is
in-bounds.** Predecessor: `ROADMAP_REDIRECT_v2.md`.

**Provenance.** Revises an external roadmap + three-idea note. Direction kept (joint / multiplicative /
non-homomorphic — already ours); frame replaced (it stripped scale/power/scope and re-inflated bounded
channels). A plan, not a findings promotion; points **into** `POSITIVE_FINDINGS_MASTER_v12.md` and
`OPEN_ITEMS_LEDGER_v1.md`.

---

## 0. The two governing principles

**(I) Mission / counter-prior.** secp is **assumed to carry exploitable structure**; the task is to
find *how* it leaks. The training default ("secure, nothing here, generic/wall") is a reflex to
suspend, not evidence. **Bias is one-way** — we suppress finds, we do not inflate — so every lead is
**surfaced and tested**, never pre-deflated; the safeguard is the *test* (matched null / firing control
/ OOS / exact arithmetic), not pre-test skepticism. **Burden of proof is on the closure:** to call a
channel dead you must name object + observable-class + power + scope, the same bar as `[PROVED]`.
*(Evidence this bias is live: in v2 I mis-closed idea 3 off one grep — corrected in Brick B/§4.)*

**(II) Bricks, not a hole-in-one.** No item is scored on opening the gate. A **brick** (1) **stands
alone** — verifiable from a named artifact; (2) **is reusable** — an exact law, a channel bounded *with
power + scope*, a dissolved anomaly restated as a sharper law, or a verified citation; (3) **is true in
its claimed direction** — carries its null/control/OOS/grade, so it never has to be un-built. A brick
that **bounds** a channel counts *iff* it carries power + scope; a dismissal-by-declaration is a fake
brick. Anomaly-Drill rule as construction: **end in a sharper law, a bounded magnitude with its power,
or a named next probe — never a "door shut."** Dissolution is positive.

**The mortar (every empirical brick).** Exact arithmetic (`int`/`Fraction`, never float in the signal
path); **matched null** sharing the readout's forced symmetries (never reuse a *forced* control — M14's
l² — as the null); **firing control** that must register a plant; **OOS** before naming a zero; count
only unforced hits; `experiment-designer` **pre-registration mandatory before data**. Grade every
output; attach **scale**.

**Scale banner — refined (v3).** Magnitudes measured at `p ≤ 10⁵` have **no power at 2²⁵⁶** (~239
binary orders) — this governs every `[VERIFIED/EMPIRICAL @ scale]` number. **But the banner blocks
sizes, not forms:** a **structural-form** claim (the *shape* of a law — "the linear part is forced 0",
"deg `c(d)` is `D`", "the correction is a μ₃-orbit invariant") verified scale-invariantly is not a
magnitude claim and is admissible toward secp **with its own proof obligation.** Keep the two kinds of
claim on separate ledgers.

---

## 1. The bricks (ordered by dependency, not difficulty)

### Brick A — E3 cubic difference-set: discharge the owed measurement
- **Object.** E3 group-law cubic difference-set on the real 82 keys — a *fired pre-registered reject*
  (`E3=13125`, 98.4th pctile, p≈0.033 uncorrected, interpretation OPEN), on the one difference-set class
  touching the DLP; master flags it **A-1d ★★** as owing a measurement.
- **Brick either way.** *Leak:* a reproduced, MC-corrected, control-clean effect on a DLP-touching
  object. *Null:* the standout owed positive converted to a **bounded magnitude with power + scope**.
  Only a re-deflation *without a test* is a loss.
- **Method.** `experiment-designer` pre-reg; **independent-arm reproduction** (vary the band-random
  arms, not just the null pool — the flaw that faked the χ₂ cousin,
  `RESULT_chi2_diffset_FALSE_POSITIVE_v1.md`); MC-correction across the family; control curve (P-256);
  firing control; exact arithmetic; OOS.
- **Grade target.** `[VERIFIED/EMPIRICAL @ scale]` or `[DISSOLVED-ON-TEST]`, each with power + scope.
- **Not a hole-in-one.** A fired reproduction is a scoped structural fact under the banner, not a
  keyspace reduction.

### Brick B — the public-ε linchpin + the CM-lattice unfolding *(idea 3 merged, v3)*
- **Object.** Two coupled questions on the **same** `Z[ω]` geometry. (i) Is there a **public** route to
  the carry ε via the Eisenstein-lift norm `eis(X)` (`…MASTER_v12.md` §D)? The whole conditional
  d-shadow arsenal is gated on this one input; currently circular, untested. (ii) `E(F_p) ≅ Z[ω]/(π_p−1)`
  gives `d` a **canonical 2-D lattice unfolding** `a+bω`; does `eis([d]G)` reveal any of `(a,b)`?
- **The second-equation lever.** The amicable partner `(π_n−1)` (norm `p`; lift overlap `1−4.1e−39`,
  verified) potentially supplies a **second, independent congruence on the same lattice point** — two
  equations pin what one leaves circular. This is idea 3 reopened: N18 closed only the reciprocal-floor
  *island* construction (`2⁻⁶⁶` density, 0/72 random-key hits); the **CM-lattice** object it never tested.
- **Brick either way.** *Yes (public ε / partial `(a,b)`):* un-gates amplifiers on covered points and
  makes the amicable over-determination testable. *No:* collapses the circular arsenal cleanly and bounds
  the lattice channel — a durable redirect. Either resolves the single most load-bearing dependency.
- **Method.** Analytical first: is `eis(X)` computable from public `(x,y)` — poly-time, single-point, no
  DLP-cost object? Run the small decisive N16 cross-check `|u−v|≤½ == build.eps`. Then regress `(a mod ℓ,
  b mod ℓ)` (small `ℓ|n`) on functions of `eis([d]G)` at small `p` — matched null (shuffle `d↔(a,b)`),
  firing control (plant a lift encoding `a mod ℓ`); then test whether the `(π_n−1)` side lowers the
  residual entropy of `(a,b)` **beyond** the `(π_p−1)` side alone. **DC5** bounds interpretation
  (prime-modulus full-orbit sums can't vanish exactly) — this is a correlation/entropy test, not a
  vanishing one. Exact arithmetic. **In-bounds per the 2026-08-18 boundary decision** (key-structure, not
  generator).
- **Grade target.** `[PROVED]` public/not-public for `eis`; graded N16 object-identity; entropy bound on
  the lattice channel with power + scope.
- **Not a hole-in-one.** A public ε / partial `(a,b)` makes conditional amplifiers non-circular on covered
  points — under the banner; not a break.

### Brick C — phase on the weight-1 eigenspace of the 0.93 shadow *(idea 2, reconstructed v3)*
- **Object.** Joint `(x,y)` reaches `ρ_inf=0.93` vs x-only 0.29–0.36 (M14); the gap is parity (x-only
  even-in-`d`; `xy` supplies the odd, μ₃-weight-1 half); N1's **2+2 splitting** localizes the weight-1
  mass to a 2-dim eigenspace.
- **Escape the no-go by construction.** The 0.93 is a **forced magnitude** (`Σ|U|²=p²(n−1)` ⇒ every l²
  fidelity identical for character/random — M14/v6). Parseval pins magnitude, **never phase**. The k=3
  **phase** channel is unforced and *fires* (M28, survives the parity-matched null). So read **phase, not
  magnitude**, on the weight-1 eigenspace.
- **The readout.** An **oblique (non-unitary) `M`** projecting onto the 2-dim weight-1 eigenspace and
  down-weighting the null eigenspace (deliberately breaking the energy normalization that forces M14),
  computed from the **public** μ₆ character table (P10 sextic-twist action) — no `d`, no `T`. Read
  `Φ(d)=arg(⟨M·lift(x_d,y_d), weight-1 eigvec⟩)` as a `d`-linear ramp.
- **Brick either way.** *Concentration above the phase-random floor:* the first **phase** separation of
  character from random — exactly what the forced-magnitude theorem left open. *Null at power:* a bound on
  the weight-1 **phase** channel, the honest residue of §XI.1.
- **Method.** `experiment-designer` pre-reg; target `a·d mod n` **disjoint** from `Φ` (built from the
  eigenvector, not `d`'s residues); **null = phase-random within the eigenspace** preserving the energy
  profile (**never** the forced l² control); firing control (plant a phase-ramp character, must clear the
  floor). Distinct from M28 (global `b`-phase) — this is eigenspace-restricted, `d`-aligned. Exact
  arithmetic; build the eigenspace at `p∈{163,349}`; OOS.
- **Grade target.** Characterization + bound with power + scope.
- **Not a hole-in-one.** A positive is a bit-rate at tested scale under the banner, not a group-ceiling
  break.

### Brick E — degree of the cover-scramble polynomial `c(d)` *(idea 1, reconstructed v3)*
- **Object.** The cover `C→E` gives a computable set-map `φ:E→A_new` (fibre-divisor pullback → `Jac(C) ~
  E×A_new` → project; needs only the point). `c(d):=dlog_{A_new}(φ([d]G))` (well-defined: A_new DLP easy,
  MOV `k=3`, M17). **Hom(E,A_new)=0 forces the linear part of `c` to vanish** ⇒ `c` is *leading-order
  quadratic by construction*, and a quadratic in `d` is **solvable for `d`**.
- **The gap in N14.** It tested "affine: NO" and "quadratic-in-GLV-halves: NO" — never the general
  univariate form nor the **minimal polynomial degree** of `c`.
- **The brick (form-level → not banner-blocked).** At `p=43` (extend to the full group), find the
  smallest `D` with `c(d) ≡ Σ_{i≤D} a_i d^i (mod ord A_new)` (exact integer linear algebra over `Z/ord`).
  *Low `D`≤~4:* a **solvable** non-homomorphic channel (read `c(d)`, solve for `d`). *High `D`:* the first
  quantitative **bound on the cover-scramble degree** — a form-level claim; test its **stability across
  `p`** (43,67,79,…), which by the refined banner is admissible toward secp.
- **Stakes / caveats.** If `D` low **and** degree-stable, transfer cost = A_new's secp DLP: MOV to
  `F_{p³}≈2⁷⁶⁸`, tower-NFS `≈ sub-2¹²⁸` — the reason this is the most-scrutinised brick and the most
  expensive false positive. **Attach N2** (A_new SS at secp = dim-2 extrapolation; external inputs owe
  re-derivation), xedni obstruction is `[HEURISTIC]`, and the **mod-6 use is closed null N17** (the degree
  route reads `d` directly, not through `d₀` — not circular).
- **Method.** `experiment-designer` pre-reg; firing control = plant a degree-2 `c*` and confirm the fitter
  returns `D=2` and recovers `d` (the affine/GLV-half positive control in
  `RESULT_isotypic_trace_lever_status_v1` already exists, must fire); matched null = orbit-covariant map
  with shuffled fibre assignment (must give generic high degree); exact arithmetic.
- **Grade target.** `[EMPIRICAL @ p=43]` degree + `[HYPOTHESIS]` degree-stability; **no** secp claim until
  degree-stable AND N2 re-derived.
- **Not a hole-in-one.** A positive at p=43 is a channel to characterize, scale-blocked and N2-blocked —
  not a transfer map.

### Brick D — exact identities that reach 2²⁵⁶ (parallel, scale-immune track)
- **D1 — `(†)` class-number step.** Prove `Σ_{s≤H}χ₂(s)·sgn(ρs mod p − s)=3h(−p)`; promotes `|FLD|=6h(−p)`
  to a theorem (tool: generalized Dedekind sums / Rademacher — `OPEN_ITEMS_LEDGER_v1.md` #16).
- **D2 — Jacobi sign law, secp's half.** p≡11 done; **secp is p≡7 mod 12, OPEN** ("prove `J` rational",
  #15). Protects A/C/E (the m-law).
- **D3 — citation-verifier / literature sweep.** 10 claimed-original results unaudited (#★); reading the
  source dissolved an obstacle 4×; mandatory before any citation-strength grade move.
- **Brick either way.** Theorem, verified citation, or dissolved obstacle — durable, scale-immune.

---

## 2. How to work it slowly

- **Dependency order.** B's N16 cross-check first (small, decides flap==carry, de-risks the flap
  program). A next (owed measurement; exercises difference-set machinery C needs). C after A. E shares
  the isotypic-trace harness → after B. **D in parallel** (D3 gates any citation upgrade).
- **One brick, one loop:** pre-register (if empirical) → build → matched-null test → OOS → grade → fold
  the artifact into the ledgers with power + scope. No grade moves up without its named artifact in the
  same edit.
- **Trust-but-verify** every subagent artifact against the diff.

## 3. Guardrails (stated positively)

- **Not** "collapse the search space" framings.
- **Not** treating a **work-invariant** (P19), **forced-magnitude** (M14 l²), or already-**bounded**
  channel as a lever — a revisit must use a channel the existing proof does not cover (phase for M14;
  `c(d)`-degree for P19; direct-read for N17).
- **Not** resurrecting the island **keyspace-pruning** apparatus (N18, scoped-closed) — only the CM-lattice
  / amicable second-equation question (Brick B) is reopened.
- **Not** reading any uncorrected p, tested-scale magnitude, or dim-2 extrapolation (N2) as reaching secp;
  **form-level** structural claims may, with their own proof obligation.
- **PRNG boundary (decided 2026-08-18): generator/seed OUT; number-theoretic structure of the key IN**
  (the interval readout and the CM-lattice unfolding are properties of the number). Persist this to the
  `feedback_no_prng_generation_side` memory via `memory-drafter` when convenient.
- **Not** converting a scoped null into a closure — burden stays on the closure.

---

*Predecessors: `ROADMAP_REDIRECT_v1/v2.md`, `ANALYSIS_idea_improvements_and_nogo_relook_v1.md`.
Authoritative ledgers: `POSITIVE_FINDINGS_MASTER_v12.md`, `OPEN_ITEMS_LEDGER_v1.md`. Adds no finding;
reopens N18's over-read and refines the banner, both under burden-of-proof-on-closure.*
