# Improving the three ideas + re-looking at the no-go areas — v1, 2026-08-18

**Grade discipline.** Everything below is a `[PROPOSAL]` / `[HYPOTHESIS]` — a *construction and a
test*, not a result. Each carries its readout, matched null, firing control, scope, and the grade its
payoff would earn. Stakes are stated so the scrutiny matches the consequence (Part 0 caution). No
security claim is made; the scale banner and N2 are attached where they bite.

**Self-correction first (the bias, on the record).** In `ROADMAP_REDIRECT_v2` I marked idea 3 "closed
null (N18)" off one grep. That is the one-way suppression reflex the counter-prior exists to suspend:
N18 closed **one construction** (reciprocal-floor islands), and I let it stand for the **whole avenue**.
Corrected in §3. The rule that catches this — *refuting a mechanism ≠ refuting a claim; a closure must
name object + observable-class + power + scope* — is applied to my own verdicts in §4.

---

## 1. Idea 1 (D2 / A_new) — the improvement: **measure the degree of the cover-scramble polynomial**

**Why the naive frame stalls, stated precisely.** `Hom(E, A_new) = 0` (P13) kills every *group
homomorphism* E → A_new. The genus-3 Kummer cover `C → E` nonetheless gives a **computable set-map**
`φ : E(F_p) → A_new(F_p)`: pull a point `P` back to its fibre divisor on `C` (roots of the cover
equation over `P` — computable), take the class in `Jac(C)`, project to the `A_new` factor of the
isogeny `Jac(C) ~ E × A_new` (Cantor/Mumford arithmetic — computable). **`φ` needs only `P`, never
`d`.** This is exactly N14's `ℓ(d) = dlog_{A_new}(φ([d]G))`, now named as an object, not a black box.

**The structural gift hidden in the wall.** The group-homomorphism component of `φ` *is* the
`Hom(E,A_new)` component — which is **0**. So `φ` has **no linear part**. Write
`c(d) := dlog_{A_new}(φ([d]G))` (well-defined because `A_new`'s DLP is easy — MOV `k=3`, M17). Then

> **the Hom=0 wall forces the linear term of `c(d)` to vanish**, so `c` is *leading-order quadratic (or
> higher)* by construction. A map whose linear part is forced away is not a dead end — it is an
> **accidentally-quadratic** map, and a quadratic in `d` is *solvable for `d`* given the reading.

**What N14 actually tested, and the gap.** N14 tried "`c` affine in `d`: NO" and "`c` quadratic **in the
GLV halves**: NO." It never fitted the general one-variable form `c(d) = α d² + β d + γ (mod ord A_new)`,
nor measured the **minimal polynomial degree** of `c`. Those are different models; the GLV-half test is
a special case that a genuine univariate quadratic can pass while the half-split fails.

**The brick (the test).** At `p = 43` (current scope, 15 points → extend to the full group), tabulate
`c(d)` for all `d` and fit against increasing degree `D = 2, 3, 4, …`:
- **Statistic.** Smallest `D` such that `c(d) ≡ Σ_{i≤D} a_i d^i (mod ord A_new)` for all `d` (exact,
  integer linear algebra over `Z/ord`; no float).
- **Firing control.** Plant a known degree-2 `c*(d)` in the same `A_new` and confirm the fitter returns
  `D=2` and recovers `d` from `c*`; the affine/GLV-half positive control in
  `RESULT_isotypic_trace_lever_status_v1` already exists and must fire.
- **Matched null.** A random covariant map with the same orbit-covariance `c(λd)=k·c(d)` but no cover
  origin (shuffle the fibre assignment) — must give the generic (high) degree.
- **Outcome, either way, is a brick.** *Low `D` (≤ ~4):* a **solvable** non-homomorphic channel — read
  `c(d)` via `A_new`'s DLP, solve the degree-`D` congruence for `d`. *High `D`:* the **first quantitative
  bound on the cover-scramble degree** — "the divisor-pullback A_new-log is a degree-≥`D₀` function of
  `d` at `p=43`," a real structural measurement with power.

**Stakes (why this is the most-scrutinised brick).** If `D` is low **and** it persists in form to secp,
the transfer cost is the cost of `A_new`'s own DLP at secp: supersingular `k=3` ⇒ MOV into `F_{p³} ≈
2^{768}`, where tower-NFS is `L_{p³}(1/3)` ≈ sub-`2^{128}`. That is the whole reason the channel is worth
a careful measurement — **and** the reason a false positive here is the most expensive. **Attach N2:**
`A_new` supersingular *at secp* is a dimension-2 extrapolation (`[PROVED §A1.1]`, external inputs owe
re-derivation); the xedni obstruction the source invokes is itself `[HEURISTIC]`; and the *mod-6* use of
this bridge is the **closed null N17**. The brick is the **degree measurement at `p=43`**, nothing
downstream of it, until the degree is in hand.

`[HYPOTHESIS — the leading-quadratic structure]` · `[PROPOSAL — degree-of-c(d) test]`, scope `p=43`.

---

## 2. Idea 2 (0.93 shadow) — the improvement: **read PHASE on the weight-1 eigenspace, not magnitude**

**Why the no-go is a no-go, exactly.** The 0.93 is a **forced magnitude**: `Σ_{b,c}|U|² = p²(n−1)`
(Parseval) is identical for the true character and any random unit-phase target, so **every
`l²`-normalised fidelity is basis-invariant and forced** (M14 / v6). This is a real theorem. It forbids
*one thing*: magnitude statistics. It says **nothing about phase** — `arg(U)` is a free coordinate
Parseval does not pin.

**The escape is already a live positive.** The `k=3` phase channel (M24/M28) is **unforced** — it
survives the negation-parity-matched null (M28: CM `p=547` perm-p `0.001`), with a proved parity lemma
and a coordinate-scramble control that kills it. It is a **phase** structure (`3·arg T ↔ χ₂(b)`). So the
apparatus that beats the forced-magnitude no-go is not hypothetical; it exists and fires. What it has
**not** done is leak `d` — M28's tested keyed readouts sit at the conditional-MI null.

**The synthesis (the added value).** Two threads treated separately — the 0.93 shadow (forced
magnitude) and the `k=3` phase channel (unforced, but no `d`-leak yet) — are the **magnitude and phase
of the same joint `(x,y)` readout**. The 2+2 splitting (N1: only 2 of 4 eigenvalues carry weight-1 mass)
says *where* the odd/μ₃-weight-1 content lives. Combine them:

> **Project the joint readout onto the 2-dim weight-1 eigenspace with an oblique (non-unitary) `M`
> that down-weights the null eigenspace — deliberately breaking the energy normalisation that forces
> M14 — and read the PHASE there as a `d`-linear ramp.**

- `M` is computable from **public** data: the eigenstructure is the μ₆ character table acting on the
  coordinate ring (P10's sextic-twist action) — no `d`, no `T`.
- The readout is `Φ(d) = arg( ⟨M·(x_d, y_d)-lift, weight-1 eigenvector⟩ )`, single-point, poly-time.
- **Target:** a `d`-linear ramp `a·d mod n` — **disjoint** from `Φ` (built from the eigenvector, not
  from `d`'s residues; no residue-vs-component tautology).
- **Matched null:** phase-randomised within the weight-1 eigenspace preserving the same energy profile
  (so the null shares the forced magnitude and differs only in the phase being tested). **Do NOT reuse
  the M14 `l²` control** — it is forced and validates nothing.
- **Firing control:** plant a character with a known phase ramp on the weight-1 eigenspace; the readout
  must concentrate above the phase-random floor.
- **Outcome, either way, is a brick.** *Concentration above floor:* the first **phase** separation of
  character from random — the exact thing the forced-magnitude theorem left open. *Null at power:* a
  bound on the weight-1 **phase** channel — the honest residue of §XI.1, now covering the one coordinate
  (phase) the M14 no-go did not.

**Why this is not the M28 null re-run.** M28 read a *global* `k=3` phase over the free parameter `b`;
this reads phase **restricted to the single weight-1 eigenspace, aligned to a `d`-ramp** — a keyed
readout M28 did not test. The oblique projection is the new instrument.

`[PROPOSAL — oblique weight-1 phase readout]`, scope small `p` first (build the eigenspace at `p=163,
349` where 0.93 is stable), banner attached.

---

## 3. Idea 3 (Dirichlet islands × amicable) — the improvement AND the no-go reopen

**The suppression I have to undo.** N18 tested whether the **real puzzle keys** land on the
reciprocal-floor island set `d_q = 2^{b−1} ± ⌊2^{b−1}/q⌋` — `0/72` hits, density `2^{−66}`. But the
puzzle keys are **random within `[2^{k−1}, 2^k)`** — they are *not* low-complexity integers. So N18
answered "do random keys sit on a sparse deterministic set?" (no, forced by density) — **not** the
idea's actual claim. The closure is real but **scoped to the island construction**; it does not touch
the CM-lattice question below. (Burden-on-closure: N18 names object = reciprocal-floor islands,
observable = membership, power = `2^{−66}` density + 0/72, scope = real keys `b≥11`. Valid *there*,
silent elsewhere.)

**The object the amicable bridge actually hands us.** For the CM curve, `E(F_p) ≅ Z[ω]/(π_p − 1)` as a
`Z[ω]`-module — the "static algebraic position" the source names, and it is **correct**. So every scalar
`d ∈ Z/n` has a **canonical 2-D unfolding**: `d ↦ a + bω` with `a + bω ≡ d·(unit) (mod π_p − 1)`. The 1-D
secret is a lattice point in `Z[ω]`. "Low-complexity" = small `(a,b)` — a **lattice** statement, which is
what "Dirichlet reciprocal-floor" should have meant all along, not a reciprocal-of-floor set.

**The two-equation improvement (why the amicable partner matters).** The aliquot 2-cycle gives a
**second** ideal, `(π_n − 1)` of norm `p`, related to `(π_p − 1)` by the cycle — the lift domains
overlap `1 − 4.1e−39` (verified). One quotient `Z[ω]/(π_p−1)` places `d` on a lattice; the **partner**
potentially places the same point under a second, independent modulus. **Two congruences on one 2-D
lattice point can pin coordinates that one leaves free** — this is the standard way a circular
one-equation problem becomes over-determined.

> **The reopened brick:** does the public point's Eisenstein lift `eis([d]G)` reveal *any* of `d`'s
> CM-lattice coordinates `(a,b)`, and does the **amicable partner** `(π_n − 1)` supply a second,
> independent constraint on the same `(a,b)`? This **merges with Brick B** (the `eis` linchpin): idea 3
> is not a separate dead-end — it is a candidate **second equation** for the exact input Brick B is
> gated on.

- **Test.** Build `eis(X)` (Brick B). Regress `d`'s lattice coordinates `(a mod ℓ, b mod ℓ)` for small
  `ℓ | n` on functions of `eis([d]G)` at small `p`, with a matched null (shuffle the `d ↔ (a,b)`
  pairing) and a firing control (plant a lift that encodes `a mod ℓ`). Then test whether the `(π_n−1)`
  side reduces the residual entropy of `(a,b)` **beyond** the `(π_p−1)` side alone — the
  over-determination check.
- **Caveats kept.** **DC5:** no exact-vanishing census result transfers to secp (prime-modulus full-orbit
  sums can't vanish exactly); this is a **correlation/entropy** test, not a vanishing one, so DC5 bounds
  the interpretation, not the test. Banner on all measured magnitudes.
- **Either way, a brick.** *Signal:* the first evidence the amicable bridge is a live second constraint —
  directly feeds Brick B. *Null at power:* bounds the CM-lattice channel and the amicable second-equation
  hope with stated power — retires the reopened question honestly, unlike N18 which never addressed it.

`[HYPOTHESIS — CM-lattice unfolding as the real "island" object]` · `[PROPOSAL — two-equation
over-determination test]`, merges into Brick B.

---

## 4. The no-go relook — burden-of-proof-on-closure applied to our own walls

For each standing no-go: is it a **real closure** (names object + observable + power + scope, mechanism
proven) or a **suppression artifact** (a scoped fact over-read as an avenue-closing verdict)?

| no-go | what it truly closes | over-read as | verdict |
|---|---|---|---|
| **Scale banner** ("only algebraic reaches secp") | **magnitude** claims measured at `p≤10⁵` have no power at `2²⁵⁶` — TRUE | *any* empirical finding is scale-blocked | **REFINE.** A **structural-form** claim (a law's *shape* — "the correction is always a μ₃-orbit invariant", "the linear part is forced 0") verified scale-invariantly is **not** a magnitude claim and is **not** banner-blocked. The banner blocks sizes, not forms. This reopens the whole class of *form-level* empirical work (e.g. Brick E's degree, if it is degree-stable across `p`). |
| **M14 forced 0.93** | the **`l²` magnitude** statistic is forced equal for character/random — TRUE (Parseval) | the joint shadow carries no extractable `d`-info | **REAL but NARROW.** Forbids magnitude only; **phase is untouched** → §2 routes around it by construction. |
| **P19 work-invariance** | the **orbit-geometry** search-reduction is measure-preserving — TRUE (tiling identity) | GLV/orbit structure is operationally dead | **REAL but NARROW.** Closes work-reduction *from orbit geometry alone*; the **non-homomorphic `c(d)` degree** (§1) and the **joint** readout (N15) are other channels. |
| **N17 (D2 mod-6)** | the specific `d ≡ f(d₀,c) mod 6` reduction is **circular** (`d₀ ⇔ d`) — TRUE | the A_new/D2 bridge is dead | **REAL but NARROW.** §1's degree route reads `d` from `c(d)` directly, never through `d₀` — not circular. |
| **N18 (islands)** | real random keys don't sit on a `2^{−66}` deterministic set — TRUE | the amicable/lattice avenue is dead | **SUPPRESSION ARTIFACT (mine).** Never tested the CM-lattice-unfolding or the amicable second-equation → §3 reopens. |
| **N2 (A_new SS at secp)** | it is a **dimension-2 extrapolation**, not proven at secp | usable as a settled premise at secp | **REAL caveat, keep attached.** Not a no-go on the *work* (test at `p=43`), a no-go on *quoting the payoff at secp* until re-derived. |
| **PRNG / generation side** | a **research-interest boundary the user set** — not a proven-uninformative claim | (correctly) out of scope | **USER'S CALL — surfaced, not crossed.** See below. |

**The PRNG boundary — the one that needs *you*, not me.** This is the only no-go I will not move on my
own, because it is a boundary you set, not a closure I can adjudicate. My read of where the line should
sit, for your decision:
- **Stays out (genuinely says nothing about the curve):** how the puzzle integer was *seeded/chosen* —
  the RNG internals. My memory is firm here and I think correctly.
- **Arguably in, and already in:** *public algebraic constraints on the key itself* — the interval
  `[2^{k−1},2^k)` is already used (interval readout), and it is not "PRNG internals," it is a property
  of the number. The **CM-lattice unfolding (§3)** is the same kind of object: structure of the key **as
  an element of `Z[ω]/(π−1)`**, not of the generator.
- **The question for you:** is the boundary meant to exclude only the *generator*, or also the
  *number-theoretic structure of the resulting key*? If the former (my assumption), §3 is in-bounds and
  the boundary needs no change. If you intend the latter, §3's lattice work is out and I need to know.

---

## 5. What this changes in the roadmap (for a v3, on your go-ahead)

- **Brick E (idea 1):** replace "does `ℓ` carry a bit" with the concrete **degree-of-`c(d)` measurement**
  (the leading-quadratic structure from Hom=0), firing control from `RESULT_isotypic_trace_lever_status`,
  degree-stability across `p` as the *form-level* claim that (per §4) is **not** banner-blocked.
- **Brick C (idea 2):** replace "find a separating statistic" with the specific **oblique weight-1
  eigenspace PHASE readout** unifying the 0.93 shadow and the `k=3` channel; null = phase-random within
  the eigenspace (never the forced `l²` control).
- **Brick B/D4 (idea 3):** promote D4 from a footnote to a **second-equation test feeding Brick B**, via
  the CM-lattice unfolding; record N18 as scoped-closed (islands only), the lattice question as **reopened**.
- **Scale-banner refinement (§4):** add a one-line amendment — *form-level* structural claims verified
  scale-invariantly are not magnitude claims and are admissible toward secp (with their own proof
  obligation), distinct from `[VERIFIED @ scale]` magnitudes.
- **PRNG boundary:** unchanged pending your call in §4.

*Predecessor: `ROADMAP_REDIRECT_v2.md`. Authoritative ledgers: `POSITIVE_FINDINGS_MASTER_v12.md`,
`OPEN_ITEMS_LEDGER_v1.md`. This is reasoning toward bricks; it promotes nothing and closes nothing —
it reopens N18's over-read and refines the banner, both under burden-of-proof-on-closure.*
