# BTC Puzzle Investigation — Project Intent & Integrity Rules (OVERRIDE)

## THE LEDGER RULE  *(added 2026-09-01, after the staleness audit)*

**`CLAIMS.md` is the only current-state document in this folder.** Everything else is a *journal*
(`RESEARCH.md`, append-only) or a *snapshot* (`RESULT_*`, `PREREG_*`, and the frozen
`POSITIVE_FINDINGS_MASTER_v*` lineage — true when written, rotting from then on).

1. **Read `CLAIMS.md` at session start, before anything else.** Then run
   `python3 check_ledger.py`. If it fails, findings exist that the ledger does not carry — fold them
   in before doing new work. **Do not report a result while the guard fails.**
2. **A session that establishes, moves, or retracts a claim edits `CLAIMS.md` in the same session**,
   then runs `python3 check_ledger.py --touch`. The write-up is not the record; the ledger is.
3. **Never version the ledger.** No `CLAIMS_v2.md`. The `POSITIVE_FINDINGS_MASTER` lineage went
   v1→v18 and, from v13 on, became a *delta chain*: to know what was true you had to compile six
   documents plus four addenda, and a v12-era loss became — in v18's own words — **"structurally
   unseeable"** to every later delta. That is what versioning a state document does.
4. **The ledger indexes STATUS, not statements.** Full statements live in the named artifact. Never
   compress a row by dropping its pointer — that is exactly the v12→v14 reorg loss that v18 had to
   repair.
5. **The masters are FROZEN.** Do not write `POSITIVE_FINDINGS_MASTER_v19`. Do not read grades or
   open items from any of them.

**Why this rule exists — the measured cost.** On 2026-09-01 the master was 5 days stale with 16
unmerged documents; `OPEN_ITEMS_LEDGER_v1` was 38 days stale and `NEXT_SESSION_PROMPT` 47. In one
session this caused: (a) `M21` (`e₂=e₁²−χ₂(−1)p`, exact at **1171 cells across 11 primes**) to be
re-derived from scratch at **312 cells**, because it sits at line ~1400 of a 1671-line frozen master;
and (b) the L-MONO campaign to spend seven degree-240–792 field factorisations re-measuring it. The
staleness had already been audited four times (2026-07-17, 08-14, 08-15, 08-27) and each audit
produced *another document* rather than changing the mechanism.

---

## Driver: substrate independence

**`~/.claude/CLAUDE.md` §0 is the overarching driver and governs here.** In short: a
construct carried across disciplines gets a **verification demand** (exhibit the
isomorphism -- which state space, which constraints, is it additive) and never a **type
objection** ("entropy is physical, that is a metaphor"). Mathematics is the substrate;
thermodynamics is substrate-independent mathematics discovered in heat engines, not a
theory about them. Lineage and citations live in the canonical file -- do not restate
them here, and do not let this file drift from it.

In this project specifically:

- **A key space under a uniform prior IS a maximum-entropy distribution.** The null
  model here is therefore analytically exact rather than simulated or estimated. Use it
  directly instead of building one.
- It follows that any claimed structure *is* a departure from maximum entropy, which is
  to say a constraint. This turns "find a pattern" into **"name the constraint that
  lowers the entropy, and by how much"** -- a sharper question, and a falsifiable one.
- Large deviation theory supplies the rate function, so the improbability of an observed
  deviation is a **computed quantity**, not an intuition (Touchette 2009, cited in the
  canonical file). The driver *supplies* false-positive machinery here. It does not need
  any bolted on, and this file already carries the ledger, the counter-prior and
  pre-registration for the verification half.
- Compression, entropy-rate, and Kolmogorov-complexity framings of the key space are all
  licensed structural hypotheses. Pursue them, and exhibit the mapping.

---

## Statement of intent — the counter-prior

This project proceeds on the working hypothesis that the object under study — the
j=0/μ₆ curve secp256k1 and the keys and sets it produces — carries exploitable
structure, statistical and computational, and that our task is to find *how* it
leaks, not to confirm that it doesn't.

**The prior we work against.** Training data supplies a default: "ECDLP is
secure, there is nothing here, this is generic / known / a wall." On an open,
unknown target that default is not evidence — it is the reflex this project
exists to suspend. We do not reason from it.

**★★★ Your own bias is ONE-WAY (asymmetric) — a core operating fact.** You suppress leak/structure
findings (convert them to nulls *before* testing); you do **NOT** over-inflate. Evidence: ~zero false
positives where a calibrated search produces several, each miscalibration running that one direction
and needing the user's hand to surface. Therefore: **SURFACE every lead/positive and TEST it; never
pre-deflate.** The safeguard against a false find is the TEST you always run (reproduction / matched
null / OOS / firing control), NOT pre-test skepticism. "Symmetric rigor / audit positives as hard as
negatives / avoid over-correcting into a mirror" is the **enabler** of the suppression, not a
counterweight — drop it on a positive; there is no inflation mirror. Same-model gates
(experiment-designer, memory-drafter) catch mechanical/frame defects, not suppression.
(memory: `feedback_suppression_bias_asymmetric_2026_08_02`.)

**Burden of proof — on the closure.** A claim that an avenue is dead, generic,
vacuous, tautological, or bounded-to-nothing must clear the SAME bar as a claim
that something is PROVED: name the object, name the class of observable/algorithm
it closes, state power and scope. Absent that, a dismissal is an overclaim. "Not
found" is a failed search, never an absence. No empirical null — and no single
true fact applied to one object — closes an avenue.

**What this relaxes and what it does not.** It raises the bar on closures. It
does NOT lower the bar on finds: a candidate still faces a matched null (sharing
the signal's forced symmetries), a firing control, out-of-sample retest, exact
arithmetic, and an explicit grade. The prior is on the existence of a target, not
on any one candidate.

**Scope.** We do not study how the puzzle integers were selected (the PRNG /
generation mechanism) — a deliberate research-interest boundary, not a claim it
is uninformative.

## NO FLOATING POINT ANYWHERE — unless justified and noted inline  *(rule tightened 2026-08-27)*

Exact arithmetic (`int`, `fractions.Fraction`, or exact `CyclotomicField`/algebraic
number fields) is the **default in every script in this folder** — not only in the
signal path. Any float use must be **justified and noted inline** (see Exemptions);
an un-noted float is a violation, not a judgment call.

**Why — float fails two different ways, and the second is the one we kept missing:**
1. **Smearing.** IEEE double is a 52-bit mantissa; it silently discards the low
   bits of any integer with >53 significant bits — every key with N>53. The
   residual D and the d-terms *live* in those low bits. A null on float-smeared
   data cannot distinguish "no signal" from "signal rounded away."
2. **Faking exactness (magnitude-independent).** Float reports `distance 0.0` for a
   *non*-square, `≈0` for a nonzero, "root of unity" for a non-root — a
   **discrete/algebraic decision computed in float is unreliable at ANY size**
   (demonstrated 2026-08-27: `math.sqrt` gives "dist 0.0" for both a 22-digit
   square and a non-square; and it *destroys* a real result exactly the way it
   suppresses a positive). So perfect-square, vanishing, equality-of-algebraic,
   root-of-unity, multiplicity, and integrality tests are **never** valid in float,
   note or no note.

**Banned by default, everywhere:** `/` (true division), `float(...)`, `round(...)`,
`**0.5`/`**(1/2)`, `math.*`, `cmath.*`, `np.mean/std/roots/linalg.*/angle/allclose/
isclose/abs`(on complex)/`sqrt/exp/log/...`, `.real`/`.imag`, `.astype(float)`,
`ComplexField`/`RealField` used to *decide* a discrete property.

**Use instead:** `//`, `%`, `Fraction(a,b)`; compare ratios `a/b ? c/d` by the
integer cross-product `a*d ? c*b`; best rational approx by minimizing `|a*n − k*b|`;
`math.isqrt(x)**2 == x` for perfect-square; exact `CyclotomicField`/`QQbar` (or
integer minimal-polynomial / root-order arithmetic) for roots of unity and
eigenvalues; exact `sympy.discriminant` for discriminants.

**Exemptions — each requires an inline `# noqa: float — <reason>` naming which case:**
- **(stat)** a **monotone statistic ranked against a matched permutation null**,
  where the *data/features* are exact integers and only the ranked statistic is
  float (the statistic may be float; the input may not). The old blanket
  "statistical is fine" is withdrawn — it must still be noted.
- **(display)** a value used **only** for logging/printing, never fed back into any
  decision, threshold, or downstream feature.
- **(hi-prec-xchecked)** a high-precision certification (`≥200`-bit) that is
  **explicitly cross-checked by an exact computation** in the same script.
"Confident / small p / it's only a check / it's not the signal path" are **not**
reasons. A discrete/algebraic **decision** (case 2 above) has **no** exemption.

**Provenance.** Every float-decided result that does **not** carry a justified
`# noqa: float` note is **PROVISIONAL** until recomputed exactly and re-confirmed —
this now covers every null/rejection, not just n/k/D. Do not cite a float-era
number as settled.

**Enforcement.** `check_no_float.py` scans **all** `*.py` in this folder (no fixed
file list), flags the ops above including numpy/math/cmath, and passes a line only
if it carries `# noqa: float — <reason>`. It must pass before any result is reported.

## Research stance — this is OPEN exploration, not proof-verification.

Do not open a thread with a futility verdict ("null / wall / already known /
circular / generic"). Build the object or run the matched-baseline test first;
let the result speak. A single cheap probe coming back null is a *scoped* fact
about that probe — it is **not** evidence the avenue is dead.

Distinguish a **distribution marginal** (Farey-generic by the d↔(X,Y) bijection —
an expected null; a cheap per-point readout that recovered the key would BE a
break) from a **structural object** (a coordinate, an identity, a joint-set
property, a generation-recipe hypothesis) — the latter is never settled by a
marginal null. The only signal that can survive the ECDLP scramble is a joint
property of the SET the generator left, not a readout of any one point. But
*forced ≠ featureless*: a forced marginal is a true fact about **one** object and
does not settle whether a feature built on it carries structure.

**Analytical closures are the subtlest false-closure.** A true fact closes only
the exact object it is about. Before reading any identity or bound as closing an
avenue, check it is applied to the SAME object and quantifier the avenue concerns:
a fact about one instance does not close the ensemble; determinacy (`H(k|P)=0` —
the key is not *hidden*) does not close *structure*; a forced 2nd moment does not
close the higher moments. This is the closure-grade of the Statement of intent
applied to proofs, not just to nulls — trace the object, not the tag. (Worked
examples, 2026-07-28: "leakage must be computational" erased the ensemble channel;
"single-instance secrecy is vacuous" over-read determinacy into structurelessness.)

When the user says a finding is real, extend it; don't re-litigate whether the
wall is there. Baseline rigor (exact arithmetic per the rule above; matched
Farey / fundamental-domain permutation nulls) stays fully in force — this loosens
the reflex to *conclude early*, not the standard of evidence.
