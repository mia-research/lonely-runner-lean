# secp256k1 — Revised Working Roadmap (Bricks, not a hole-in-one) — v1, 2026-08-18

**Provenance.** This revises an external model's roadmap
(`~/Downloads/Strategic Research Roadmap_ Unifying Structural Intersections…md`). That roadmap's
*direction* is kept — pivot from single-coordinate readouts toward joint / multiplicative /
non-homomorphic objects — because it is already ours (Part 0 LBE pivot, N15, and the project's own
"a joint property of the SET is the only signal that survives the scramble"). Its *frame* is not
kept: it strips the scale banner, and it re-inflates into break-levers two channels our own proofs
already bound (P19 work-invariance; N16 flap≠carry). See `POSITIVE_FINDINGS_MASTER_v12.md` for the
object-level rebuttal. This document is a plan, not a findings promotion — it points **into** the
authoritative ledgers (`POSITIVE_FINDINGS_MASTER_v12.md`, `OPEN_ITEMS_LEDGER_v1.md`) rather than
re-summarising them, so no open item is degraded by consolidation.

---

## 0. The two governing principles (read first)

**(I) Mission / counter-prior** (`BTC_.../CLAUDE.md`, `feedback_suppression_bias_asymmetric_2026_08_02`).
The working hypothesis is that secp — the j=0/μ₆ curve and the keys/sets it produces — **carries
exploitable structure**, and the task is to find *how* it leaks. The training default ("ECDLP is
secure, nothing here, generic/known/wall") is a reflex to suspend, not evidence. **Bias is one-way:**
we suppress finds, we do not inflate them — so every lead is **surfaced and tested**, never
pre-deflated. The safeguard against a false find is the *test* (matched null / firing control / OOS /
exact arithmetic), not pre-test skepticism. **Burden of proof is on the closure:** to call a channel
dead/generic/bounded-to-nothing you must name the object, the class of observable it closes, and its
power and scope — the same bar as a `[PROVED]`.

**(II) Bricks, not a hole-in-one.** We are not trying to break ECDLP in one move, and no item below is
scored on whether it "opens the gate." The unit of progress is a **brick**: a result that

  1. **stands alone** — independently verifiable from a named artifact;
  2. **is reusable** — an exact law, a channel bounded *with its power and scope*, a dissolved anomaly
     restated as a sharper law, or a verified citation, that later work can build on without redoing;
  3. **is true in the direction it claims** — carries its matched null / control / OOS / grade, so it
     never has to be un-built.

A brick that **bounds** a channel counts — *iff* it carries power + scope (principle I). A
dismissal-by-declaration is a fake brick; it crumbles the first time someone leans on it. This is the
Anomaly-Drill rule stated as a construction principle: **a drill ends in a sharper law, a bounded
magnitude with its power, or a named next probe — never a "door shut."** Dissolution is a positive
result.

**The mortar (non-negotiable on every empirical brick).** Exact arithmetic (`int`/`Fraction`, never
float in the signal path); a **matched null** sharing the readout's forced symmetries (a
value-permutation null against an even-in-`d` readout is a *guaranteed* false positive — it has fired
twice); a **firing control** that must register a planted effect; **out-of-sample** retest before any
zero is named; **count only unforced hits**; and `experiment-designer` **pre-registration is mandatory
before data** for any test/sweep/drill. Every output carries a **grade**
(`[PROVED]`/`[VERIFIED]`/`[CITED]`/`[EMPIRICAL]`/`[HEURISTIC]`/`[OPEN]`/`[GAP]`/`[DISSOLVED-ON-TEST]`)
and, if empirical, its **scale** — the banner (p ≤ 10⁵ measured vs secp's 2²⁵⁶, ~239 binary orders)
governs every measured claim.

---

## 1. The bricks (ordered by dependency, not by difficulty)

Each brick lists the **object**, the **brick laid in *either* outcome** (this is the point — both a
leak and a bounded null are bricks), the **method/mortar**, the **grade target**, and the **not-a-
hole-in-one** clause (what it explicitly does not claim).

### Brick A — E3 cubic difference-set: discharge the owed measurement
- **Object.** E3 group-law cubic difference-set energy on the real 82 keys — a *fired pre-registered
  reject* (`E3=13125`, 98.4th percentile, p≈0.033 **uncorrected**, interpretation OPEN), on the one
  difference-set class that touches the DLP. Master v12 flags it **A-1d ★★** as the standout suppressed
  positive that "owes a MEASUREMENT," having been deflated to a null at a consolidation seam.
- **Brick either way.** *Leak:* a reproduced, MC-corrected, control-clean effect on a DLP-touching
  object at tested scale = the most consequential structural brick in the corpus. *Null:* a
  properly-powered characterization that converts the standout owed positive into a **bounded magnitude
  with power + scope**, retiring a hanging seam honestly (principle I burden met). Both are bricks; only
  a *re-deflation without a test* would be a loss.
- **Method / mortar.** Pre-register with `experiment-designer`. **Independent-arm reproduction** — vary
  the band-random arms, *not* just the null pool (the exact flaw that faked the χ₂ cousin,
  `RESULT_chi2_diffset_FALSE_POSITIVE_v1.md`). MC-correction across the pre-registered family. Control
  curve (P-256). Firing control (plant an E2/E3 effect, confirm it registers). Exact arithmetic; OOS
  arms. The χ₂ death is the template for *both* the valid method and the honest null.
- **Grade target.** `[VERIFIED/EMPIRICAL @ tested scale]` characterization **or** `[DISSOLVED-ON-TEST]`,
  each with power + scope. Not a security claim.
- **Not a hole-in-one.** Even a fired reproduction is a scoped structural fact at p ≤ 10⁵ under the
  banner — a brick, not a keyspace reduction.

### Brick B — the public-ε linchpin (resolve the arsenal's single dependency)
- **Object.** Is there a **public** route to the lift carry ε via the Eisenstein-lift norm `eis(X)`
  (`POSITIVE_FINDINGS_MASTER_v12.md` §D / doc 19 §4A)? The whole conditional d-shadow arsenal is gated
  on this one input; it is currently **circular** and **untested**. Sub-item N16 owes the declared-not-
  tested cross-check `|u−v|≤½ == build.eps` on the project script.
- **Brick either way.** *Yes (public):* un-gates the amplifiers on covered points — a genuine step, and
  it makes N16's flap==carry question concrete. *No:* collapses a whole circular arsenal cleanly and
  confirms the flap≠carry gap (N16) is real at the object level — a durable brick that redirects the
  entire flap program instead of leaving it hanging. Either outcome resolves the **single most
  load-bearing dependency** in the map.
- **Method / mortar.** This is first an **analytical** brick: is `eis(X)` computable from public
  `(x,y)` with no DLP-cost object in its definition, poly-time, single-point? Build the construction;
  then run the small, decisive N16 owed cross-check (`|u−v|≤½ == build.eps`) to settle whether the
  coordinate flap equals the scalar carry ε_LBE. Exact arithmetic throughout.
- **Grade target.** `[PROVED]` that `eis` is / is not public, and a graded object-identity result for
  N16 (`eps(x) == ε_LBE` or a counterexample bank).
- **Not a hole-in-one.** A public ε is not a break; it is the input that makes the *conditional*
  amplifiers non-circular on covered points — still under the banner.

### Brick C — N15 joint readout, beyond orbit geometry
- **Object.** Do `e([d]G) ⊕ s-class ⊕ y-parity ⊕ interval` **jointly** constrain `d`? OPEN, untested
  (N15). The single readout carries full determined info (MI=1.585 bits) but is not a cheap arithmetic
  function of `d` (max 0.033 bits over 8 cheap fns). This is the honest residue of the "no keyspace
  reduction" dismissal — *argued, never tested* (A-1b/A-1e).
- **The constraint the external roadmap missed.** P19 (carry-ceiling work-invariance, `[PROVED —
  identity]`) shows the **orbit-geometry** channel is measure-preserving: compression × oracle-cost =
  1.000. So the brick is specifically a joint channel that adds **something beyond orbit geometry** — or
  it re-tests a proven no-op.
- **Brick either way.** *Leak:* first evidence a joint readout beats the single-readout 0.033-bit cheap
  ceiling. *Null:* a matched-null bound on the joint channel at stated power — converts A-1b/A-1e from
  "argued" to "bounded, tested," discharging a hanging contradiction the right way.
- **Method / mortar.** `experiment-designer` pre-reg. Target **disjoint** from the readout (no
  residue-vs-component tautology, §XII.24). Null **symmetry-matched** (even-in-`d` guard). Firing
  control. Readout must include a channel beyond the μ₆-orbit label — interval position × s-class
  residue, and the non-μ₆-covariant raw bits (`x mod 2`, high bits of `x`) that live outside the μ₆
  decomposition. Exact arithmetic; OOS.
- **Grade target.** Characterization + bound, with power + scope.
- **Not a hole-in-one.** A positive joint MI is a bit-rate at tested scale under the banner, not a
  search-space collapse.

### Brick D — exact identities that reach 2²⁵⁶ (parallel, scale-immune track)
These are the purest bricks: theorems / citations that **do not decay with scale** and are reusable
independent of any leakage question. This track always yields something and needs no leakage pre-reg.
- **D1 — `(†)` class-number step.** Prove
  `(†) C′−C = Σ_{s≤H} χ₂(s)·sgn(ρs mod p − s) = 3·h(−p)`; promotes `|FLD| = 6h(−p)` from
  `[VERIFIED 134 primes]` to a theorem. Elementary manipulation is *provably* circular — the tool is
  generalized Dedekind sums / Rademacher (`OPEN_ITEMS_LEDGER_v1.md` #16).
- **D2 — Jacobi sign law, secp's half.** The proved half is p≡11 mod 12; **secp is p≡7 mod 12, OPEN**,
  re-typed to "prove `J` is rational" (`OPEN_ITEMS_LEDGER_v1.md` #15). Closing it is a theorem; it also
  protects Bricks A–C, which lean on the m-law.
- **D3 — citation-verifier / literature sweep.** The 10 claimed-original results (Cap Law, H1,
  `|FLD|=6h(−p)`, Claims S/F, `A_new` supersingularity, secp amicability, the `m` quantum number, three
  `U` conservations, bilinear closure, `k_den` Farey comb) are **unaudited against the literature**
  (`OPEN_ITEMS_LEDGER_v1.md` ★). Reading the source dissolved an obstacle **four** times on this
  project. Mandatory before any grade moves up on a citation's strength, and it guards D2 (the external
  roadmap cited Jacobi on the wrong side of exactly this gap).
- **Brick either way.** Each item is a theorem, a verified citation, or a dissolved obstacle — all
  durable, all reusable, none dependent on scale or on the leakage question.
- **Not a hole-in-one.** These sharpen the map and protect the other bricks; none is itself a leakage
  result.

---

## 2. How to work it slowly (steady cadence, one brick at a time)

- **Dependency order, not difficulty order.** B's N16 cross-check is small and decisive for whether
  flap==carry, so it comes first and de-risks the flap program. A is the standout owed measurement and
  exercises the difference-set machinery that C also needs, so A precedes C. **D runs in parallel
  throughout** as the scale-immune track that always returns a brick and needs no leakage pre-reg.
- **One brick, one loop:** pre-register (if empirical) → build the object → matched-null test → OOS →
  grade → fold the artifact into `POSITIVE_FINDINGS_MASTER` / `OPEN_ITEMS_LEDGER` with its power and
  scope. No brick promotes a grade without its named artifact in the same edit.
- **Trust-but-verify** every subagent artifact against the diff before it becomes a brick.

## 3. What we are explicitly NOT doing (guardrails, stated positively)

- **Not** chasing "collapse the search space" / "decidable isolation of `d`" framings — no item is
  scored on opening the gate.
- **Not** treating a **work-invariant** (P19) or already-**bounded** channel as a lever; if we revisit
  one, the brick must add a channel beyond what the existing proof covers.
- **Not** reading any uncorrected p-value, or any tested-scale (`p ≤ 10⁵`) result, as reaching secp —
  only algebraic bricks with no measured input (Track D, plus P1/P2/P8/P9–10/P15) do.
- **Not** the PRNG / generation side — a research-interest boundary, restated (`CLAUDE.md` scope).
- **Not** converting a scoped null into a closure — burden of proof stays on the closure (principle I).

---

*Predecessor ledgers (authoritative, not superseded): `POSITIVE_FINDINGS_MASTER_v12.md`,
`OPEN_ITEMS_LEDGER_v1.md`. This roadmap adds no finding and closes no avenue; it orders the owed and
open work into bricks under the two governing principles.*
