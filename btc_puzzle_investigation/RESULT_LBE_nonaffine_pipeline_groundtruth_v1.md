# RESULT — LBE / non-affine inversion pipeline, tested against ground truth

Serious attempt at the "isotypic-trace-carry" Localized Bit Extraction pipeline
(orbit readout → Semaev carry → reciprocal-floor congruence → CVP/LLL ⇒ 1–3 keys).
Built a small **GLV curve where every discrete log is known** and ran each named step
against ground truth. Harness: `lbe_setup.sage`, `lbe_pipeline.sage`, `lbe_t3hard.sage`.

**Curve:** `y²=x³+2 / F_100003`, prime order `n=99667`, `β=7120` (ord 3 in F_p),
`λ=30642` (`λ³=1 mod n`), `φ(x,y)=(βx,y)=λ·P` verified. `n≡1 mod 3` like secp.

Grades: T1/T3/T4 = **PROVED-at-scale** (mechanical, ground-truth, with controls).
T2 = **PARTIAL** (natural reading null; exact statistic underspecified — left OPEN).

## T1 — the congruence law is false
`d ≡ d₀·(−1)^j − ⌊d₀λ^j/n⌋ (mod 3)`, tested on 2000 random known `(d,d₀)`:
holds **652/2000 = 32.6% ≈ 1/3 (chance).** Not a law. (It is also internally
malformed: `(−1)^j` depends on `j mod 2` while `j` is an orbit index mod 3.)

## T2 — the ±0.58 orbit-conditioned correlation did NOT reproduce [OPEN]
Conditioning a sign readout on the GLV branch `j` and correlating with `d mod 3`:
`corr = −0.008, +0.004, +0.013` for `j=0,1,2` — **≈ 0**, not `±0.577`.
Caveat, stated not buried: the report does not pin down "isotypic projection trace"
and "reciprocal-floor lattice carry `c`" precisely, so this is one natural reading, not
their exact statistic. Flag: **`0.58 ≈ 1/√3` is exactly the value a forced 3-way
conditioning manufactures** ([[feedback_prereg_abstention_is_the_finding_2026_07_19]],
[[residue_vs_component_tautology]]) — the prime suspect is a forced statistic, but that
is not yet demonstrated. Owed: their exact definitions, then reproduce-or-refute.

## T3 — the Semaev "carry" is NOT observable from group elements [the structural kill]
Carry `ε(d)=[d+d₀≥n]` has `H=0.994 bit`. Mutual information recovered from point
readouts of `P_d`, `P_{d₀}`, and their sum (hi/lo bits of x,y; residues; joint):

| feature | MI (bit) | its shuffle baseline |
|---|---|---|
| hi/lo(x_sum), hi(y_sum) | ≤ 0.0013 | ≥ same | 
| hi/lo(x_tgt), hi(y_tgt) | ≤ 0.0013 | ≥ same |
| x%97 readouts | 0.0001 | 0.0005 |
| **POSITIVE CONTROL `[d≥n−d₀]`** | **0.994** | 0.00001 |

Every real readout is **at or below its finite-sample MI floor** → zero signal; the
positive control recovers the whole bit → the estimator works. **Mechanism (provable,
not just measured):** the group is `ℤ/n`; addition reduces mod `n` and the result
`P_{(d+d₀) mod n}` is one more point whose coordinates are a pseudorandom function of the
reduced scalar. Nothing in it records whether a wrap occurred. To "measure the carry"
you must already know `d+d₀` as an integer — i.e. already have the DLP. **A cyclic group
exposes no carry channel.** Step 2 is vacuous.

## T4 — no collapse to 1–3 keys
Readout vector `(j, s, carries vs K anchors)`, candidates sharing a target's readout:

| K anchors | #classes | candidates for target | claim |
|---|---|---|---|
| 1 | 12 | 9422 | 1–3 |
| 8 | 54 | 2385 | 1–3 |
| 32 | 198 | 1518 | 1–3 |
| 64 | 390 | **177** | 1–3 |

And this is the **generous** run — I fed the pipeline the *ground-truth* carries it
cannot actually observe (T3). Even so, 64 anchors reach 177, not 1–3. Once T3 removes the
carries, only the `(j,s)` readout survives = **12 classes = n/12 ≈ 8300 candidates,
flat, for all K.** At 256-bit scale: `2²⁵⁶/12 ≈ 2²⁵²`. No collapse; CVP/LLL has no small
BDD window to work in.

## Verdict (scoped)
The pipeline **as specified** does not localize the key: its localizing step (the carry)
reads a bit the group does not expose (T3), its congruence law is chance (T1), and its
collapse does not occur even when handed unobservable data for free (T4). This refutes
**this mechanism**, on **this GLV family**, at **ground-truth scale** — it does not (and
cannot) prove secp secure in general; ECDLP remains assumed-not-proven.

## BANKABLE (real, reusable — this is not a dead end, it's a map)
1. **GLV orbit readout is real but reads the *presentation*, not the secret.**
   `χ₃(x_{dG})` genuinely distinguishes the three orbit members `{d, λd, λ²d}` (since
   `φ` multiplies `x` by `β`, `χ₃(βx)=ω·χ₃(x)`). It tells you *which representative you
   hold* — `log₂3` bits about the presentation, **0 bits about `d`**, because being handed
   `dG` already fixes the member. Same shape as the "count distinct configurations" lesson.
   Bank as a **named trap**: orbit-index readouts feel informative and are not.
2. **NAMED NO-GO — the mod-n no-carry obstruction.** Any scheme needing to observe a
   wrap / carry / half-plane / Markov-transition bit from a group operation is dead a
   priori: `ℤ/n` addition has no observable carry. Prunes the whole Markov-carry /
   reciprocal-floor-carry / Semaev-carry family in one stroke. **Positive deliverable.**
3. **The ground-truth GLV harness** (`lbe_setup`+`lbe_pipeline`) — reusable rig for any
   future "readout ⇒ key" claim: build small GLV curve, enumerate dlogs, measure MI vs
   ground truth with shuffle baseline + positive control. Apply it to every such claim
   before believing a collapse number.

## IDEA-LEVEL TEST (not just the method) — `idea_test.sage`
The *idea* stripped of the broken pipeline: "the curve's algebraic structure / orbit
stratification leaks the secret scalar `d` on a fixed curve." Tested directly — MI between
a battery of tractable algebraic readouts of the public point `P_d` (χ₃(x), χ₂(x), χ₂(y),
x,y mod small primes, `F=χ₃(x)y`, anchor sums `χ₃(x_{P_d+P_a})`) and the secret bits
(`d mod 2,3,5,7`, half-plane `[d<n/2]`, top bits).

- **Positive control fires:** feature `d mod 3` vs target `d mod 3` → **1.585 bit = log₂3**
  (full). The estimator detects real dependence.
- **All real readouts vs all secret bits: MAX MI = 0.00051 bit**, shuffle-baseline floor
  = 0.00020 bit. Signal ≈ noise. Half-plane bit (the BDD-relevant one) ≤ 0.00012 across
  every feature.
- **Orbit stratification does NOT appear.** Their claim: flat globally, spikes to ±0.58
  within a GLV orbit. Measured: global MI ≈ 0.00002 **and** per-orbit-branch MI ≈ 0.00005
  — flat at both levels. The signature phenomenon of the idea is absent.

Nuance (stated, not hidden): the full coordinate pair `(x_d,y_d)` trivially determines `d`
(it's a bijection) — "having the point" is not a leak. The meaningful question is whether a
*tractable low-degree algebraic* readout predicts `d`'s bits; measured null. So the idea,
like the method, is a scoped null at `n≈10^5`: no tractable algebraic-structure leakage of
the fixed-curve scalar, globally or orbit-conditioned. This is the fixed-curve object prior
turns flagged as untested — now tested (this scale).

## Owed
- T2 exact-statistic reproduction (their "isotypic trace" / "lattice carry `c`" defs).
- Scaling sweep of the idea-test (max-MI/baseline vs `n`) to show the null holds as `n`
  grows — the MI floor is `~bins/N`, so per-readout MI → 0, but a multi-`n` confirmation
  would match the calibrated-detector standard used earlier.
- experiment-designer pre-registration audit (gate not run this turn) — [PROVISIONAL] on
  the graded slots; the T1/T3/T4 kills stand on their controls independent of the gate.
