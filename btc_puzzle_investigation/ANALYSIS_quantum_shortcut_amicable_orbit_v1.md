# ANALYSIS — Do secp256k1's amicable-pair / p→n→p geometry give a Shor short-cut? (v1)

**Date 2026-08-06.** Prompted by a "quantum resource compression + geometric short-cut"
hypothesis: that recent qubit-count reductions for Shor-on-secp, combined with secp's status as
a Silverman–Stange amicable pair and its Rhombus-Theorem lattice geometry, might let quantum
period-finding exploit "structural symmetry between `F_p` and `F_n`" via the length-2 prime
orbit `p → n → p`.

**Bottom line up front.** The prompt fuses three separate objects. One (qubit compression) is
real and generic; one (CM/GLV) is real and bounded; the specific proposed mechanism (the
amicable / p→n→p orbit shortening period-finding) meets **three proved obstructions** and is
**not** supported by any known effective map. A pre-registered empirical test of the one
non-vacuous sub-question — statistical dependence across the two fields — comes back **null at
demonstrated power**. Grades are attached per claim; nothing here is asserted at the PROVED bar
without a proof, and nothing is called *closed*.

---

## 0. Three objects, disentangled

| object | what it is | status toward a Shor short-cut |
|---|---|---|
| **A. Qubit compression** (835–1193 logical qubits) | RNS + space-efficient modular inversion for 256-bit field arithmetic | `[ASSERTED — figures unverified]` real, **bit-length-driven**, generic to any 256-bit prime field; the only secp-specific lever is the **prime form** `p=2²⁵⁶−2³²−977` (fast reduction), unrelated to amicability/CM/rhombus |
| **B. CM / GLV** (`j=0`, `μ₆`, endomorphism `[λ]`) | an efficiently computable **self-map of `E(F_p)`** | `[PROVED effective map]` real; classical `√6` rho + half-scalar GLV; quantum benefit is a **circuit constant**, already polynomial — **distinct object** from the amicable claim |
| **C. Amicable pair / p→n→p orbit / trace duality / Rhombus** | relations *between two different fields* / a static lift marginal | `[PROVED]` provides **no effective map**; three obstructions below |

The prompt's mechanism is **C**. A and B are not it.

---

## 1. Why the p→n→p orbit gives no period-finding short-cut — three proved obstructions

**(1) Category error: the orbit is a period of the wrong map.** `[PROVED]`
Shor's ECDLP period is the order **n** of the point `P` — the hidden subgroup
`L = {(a,b) : a ≡ b·d mod n}` lives at scale `n` (~256 bits). The "length-2 prime orbit" is a
fixed structure of the **size map** `q ↦ #E(F_q)`: `#E(F_p)=n`, `#Ẽ(F_n)=p`. Different
quantity, different type. The orbit being length 2 does not make `n` smaller; the period the
QFT must resolve is still ~`n`. No 2-cycle on *field sizes* reduces the *group-order* period.

**(2) `Hom = 0`: the two fields carry no group morphism.** `[PROVED — project §XII.4]`
`|E(F_p)|=n`, `|Ẽ(F_n)|=p`, `gcd(n,p)=1` ⇒ every group homomorphism between the two curves is
trivial. A "structural symmetry between `F_p` and `F_n`" therefore cannot be a group map that
transports the DLP.

**(3) The only candidate bridge map *is* the ECDLP.** `[PROVED — project T1]`
The CM coordinate map `φ : E(F_p) → Z[ω]/(π_p−1) ≅ F_n` that would realize the p↔n "log
bridge" **is the discrete logarithm itself**. Any evaluable point→partner map contains ECDLP in
its own construction; it is legal only on the *measurement* side. The trace duality
`t_n = 2 − t_p` that would be the "matching boundary condition" is **forced** by `π_n = π_p − 1`
and is **public** (both `n` and `p` are published) — it hands an attacker nothing beyond
knowing `n`, which Shor already uses as its modulus.

**Consequence.** To "exploit the p↔n symmetry" to speed period-finding, one must first
instantiate the symmetry as a computable map, and doing so already requires solving the very
ECDLP the period-finding is trying to solve. Scope: this rules out the **effective-map** route
via the amicable / trace-duality / orbit mechanism. It does **not** assert ECDLP is secure and
does **not** touch the statistical-dependence question (§3).

---

## 2. The Rhombus Theorem is a static marginal — out of scope for Shor `[PROVED, out of scope]`

`lift_sextant_rhombus_law_v2.md`: the CM lift's `p` lattice points distribute over the six
sectors of a `√p`-edge 60° rhombus as a one-parameter closed form in `θ = arg(π_p) mod 60°`
(secp: `θ ≈ 50.55°`, pinned pair `{0,3}=1/8`). This is a **single-point marginal**, explicitly
*scalar-independent*, and its own scope section states it says nothing about joint / group-law
statistics. It is a fact about where lattice points sit — no coupling to a period-finding
circuit or its complexity. It neither helps nor is invoked by Shor.

---

## 3. The one non-vacuous sub-question — tested, null at power

The homomorphic route is dead a priori (§1.2). The **decidable non-homomorphic** rendering is
statistical: *does a d-free `F_p` feature see a partner-side `F_n` function after μ₆-averaging,
beyond matched non-amicable curves?* This was pre-registered (`PREREG_amicable_log_bridge_v1.md`,
2026-07-23) and **executed this session** — full result in `RESULT_amicable_log_bridge_v1.md`.

- **Feature** `F(P)=χ₃^{(p)}(y(P))`; **target** `g(d)=χ₃^{(n)}(d³+7)`; **statistic** the exactly
  double-centred `Z[ω]` pairing `T`, `R=N(T)/((n−1)²n)`; **primary** the amicable-vs-matched-
  control Mann–Whitney of per-unit permutation p-values.
- **Result `[EMPIRICAL, scoped]`:** discovery `p=0.83`, replication `p=0.35`, **signs disagree**;
  per-unit `π` ≈ Uniform[0,1]; `T` argument-sector uniform (no hidden symmetry-type effect);
  aggregate `(F,g)` contingency flat. **Outcome §9-3: falsified at the measured power.**
- **Power is demonstrated, not assumed:** the injected-signal plant reproduces the exact
  magnitude `R≈ε²n/4` (1–3%), and the **contrast rejects an injected amicability effect down to
  ε ≈ 1/50** — yet none is present in the real data. Scope: `E_7`, `907 ≤ p < 200000`, `n`
  prime; **236 binary orders below secp**; OOS `p<2×10⁶` owed.

**Crucially, even a positive here would not be a Shor short-cut.** By the pre-reg's own §0b/§10,
the statistic requires `d` on the measurement side, so a positive is *a dependence, not a map and
not a bit*. The statistical avenue characterizes structure; it cannot, by construction, become a
period-finding short-cut. Its null is one more absent lever, not the load-bearing argument —
§1's obstructions are.

---

## 4. Where a real, non-zero lever sits (and its ceiling)

Not everything is inert. **CM/GLV (object B)** is the genuine structure and, unlike the amicable
cross-field relation, lives *on the field side*: `[λ]P = φ(P)` is an efficiently computable
endomorphism of `E(F_p)`. It could shave **circuit constants** in a Shor implementation
(half-width scalar registers; the order-6 automorphism inside the hidden-subgroup structure)
`[plausible, bounded]`. But (i) Shor is already polynomial — an order-6 automorphism changes
constants, not asymptotics; and (ii) this is the CM/GLV feature, **not** the amicable/orbit
mechanism the prompt proposes. The compression figures of object A are likewise real but
generic to the 256-bit field and the special prime form — they do not draw on amicability, CM,
or the rhombus.

---

## 5. What would have to be true — and the grade banner

For the posed short-cut to exist you would need an **effective, d-free, polynomial-time map**
relating `E(F_p)`'s group structure to something cheaper on the `F_n` side. Obstructions
(1)–(3) rule out the amicable / trace-duality / orbit route as its source, and the one
statistical rendering of a weaker (non-map) dependence is null at power over `p<200000`.

**Grades.** §1(1)–(3) and §2 are **PROVED** algebraic facts, scoped to the amicable/orbit/
rhombus mechanism (they do not claim ECDLP security). §3 is **EMPIRICAL**, scoped to `p<200000`
with power `ε_min^W=1/50` and OOS owed. Object-A figures are **ASSERTED** (relayed, unverified).
Object-B's quantum benefit is **plausible and bounded** (circuit constant, already polynomial).
No line here is written as *closed / no leakage / generic*; the empirical leg is a scoped
magnitude bound, and a result at `10³–10⁵` says nothing automatic at `2²⁵⁶`.

**Provenance:** `RESULT_amicable_log_bridge_v1.md`, `amicable_log_bridge_v2.py`,
`amicable_log_bridge_v2_results_200000.json`; algebra from
`PREREG_amicable_log_bridge_v1.md` (§0, T1, `Hom=0`), `lift_sextant_rhombus_law_v2.md`,
`secp256k1_arithmetic/` (amicable = S–S Conj 40, `13/50`; GLV=CM). External audit:
experiment-designer (spec-vs-code, this session).
