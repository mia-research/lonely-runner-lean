# PREREG — Deterministic `s<3/16 ⇒ ε_scalar=0` implication as a search-space cut: RULING = REDUCIBLE / PRE-REFUTED, with the minimal non-circular repair

**Status: FROZEN pre-registration / adjudication. No NEW data generated. This document RULES on
well-posedness before any run; it does not run the test.**
Date frozen: 2026-08-13. Author role: experiment-designer (pre-registration gate, CLAUDE.md §2).
Scope curve: secp256k1 (j=0, CM by `Z[ω]`, p≡7 mod 12, n prime, GLV
`LAM=0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72`, λ³≡1 mod n, β³≡1 mod p).
Public coordinate predicate: `s(x)=N(eis(x))/p ∈ [0,3/4]`, exact integer function of x alone
(`int1_frame_operator_v1.build_secp` + `enorm`; `RESULT_linchpin_s_gate_v2.md`).

**Grounding artifacts read (all prior, none regenerated):** `RESULT_linchpin_s_gate_v2.md`,
`RESULT_eps_to_d_constraint_v1.md` (+`_v2`), `RESULT_joint_fiber_carry_mi_v1.md`,
`RESULT_joint_carry_twokey_mi_v1.md`, `ARSENAL_d_shadow_and_range_tools_v1.md`,
`ANALYSIS_public_gate_glv_carry_circularity_v1.md`, `OPEN_d2_congruence_law_v1.md`.

---

## TOP-LINE VERDICT (frozen before any new run)

**The proposed deterministic implication `[s(x_P)<3/16] ⇒ [ε_scalar(d)=0]`, counted as violations, is
NOT a genuinely new test for any of the registered scalar-carry objects. It is REDUCIBLE, in three
non-overlapping regimes, to facts already in hand or to an exact algebraic impossibility:**

| scalar-carry target | Pr[ε=1] regime | ruling | why (frozen, exact) |
|---|---|---|---|
| single-key upper-half `ε_u=[dλ mod n ≥ ⌈n/2⌉]` (j=1) | balanced ≈0.49 | **PRE-REFUTED by a marginal (Fréchet) bound** | `Pr[s<3/16]+Pr[ε_u=1]−1 ≈ 0.68+0.49−1 = 0.17 > 0` forces ≥17% violations with ZERO data. Also MI-null already (`joint_fiber`, Îhat=0.001, p=0.79). |
| two-key tool-7 `ε_7=[(d₁+d₂)λ mod n < r₁]` (j=1) | balanced ≈0.50 | **ALREADY RUN and EMPIRICALLY REFUTED** | `RESULT_eps_to_d_constraint_v1.md` gate row: **21–93 violations** per cell (p∈{43,547,907,1303}). Same marginal bound applies. |
| orbit-carry parity / low bit of `c=⌊d₀λ^j/n⌋` | balanced ≈0.50 | **PRE-REFUTED by the same marginal bound** | balanced low bit ⇒ 0.17 forced-violation floor; DEGENERATE on real-82 (c≡0, `OPEN_d2`). |
| orbit-carry rare bit `ε=[c=0]` (j=1) | rare ≈2⁻²⁵⁴ | **FIRING-CONTROL DEAD (power-zero)** | on constructed full-range, `Pr[c=0]=Pr[d₀<n/λ]≈4/n≈2⁻²⁵⁴` ⇒ ε=1 never occurs in any feasible N ⇒ the consequent's negation cannot co-occur with the antecedent ⇒ vacuous "0-violation" pass; DEGENERATE on real-82 (c≡0 ⇒ ε≡1 ⇒ ~68% trivial violations). |

**There is no regime in which the deterministic-implication test is simultaneously (i) marginally
possible, (ii) firing-control-live, and (iii) not already run.** The intended edge — "MI at MI_min
power can miss a deterministic law a 0-violation test would catch" — does not survive the numbers here
(§HAZARD-2). The correct next object is a SEARCH-SPACE / lattice question, not this implication
(§REPAIR).

**This is NOT a closure of the CM/GLV avenue.** It is a scoped ruling on ONE implication over the
registered carry objects, resting on (a) an exact Fréchet inequality, (b) an already-executed run, and
(c) a computed degeneracy — never on a pre-test deflation of an untested positive
(`feedback_suppression_bias_asymmetric`). The rare-carry-on-constructed and geometric-lattice objects
are left explicitly OPEN with the exact conditions that would make them new (§REPAIR, §SCOPE).

---

## HAZARD 1 — CIRCULARITY: does "public fn of P is redundant with P" kill a 1-bit deterministic PIN?

**RULING: NO — the circularity argument (`ANALYSIS_...circularity_v1.md §4`) does not disqualify a
hypothetical 1-bit deterministic pin. The test is WELL-POSED and non-circular in principle; it is
killed by HAZARD 2 (marginal feasibility), not by circularity.**

- The §4 argument ("a public function of `P` is redundant with `P`; it cannot carry information about
  `d` beyond the DLP") correctly kills a public **readout** of the full ~256-bit carry `c` — because
  `c` contains `d₀`, and reading `c` from public `x` would require the DLP (ANALYSIS §2).
- The proposed test has a **different logical shape**: it does not READ `ε` from public data. It asks
  whether a public predicate `A=[s<3/16]` is a **sufficient condition** that PINS `ε` to a known
  constant (0). An implication `A(public) ⇒ ε(scalar)=const` is **not** "a public function equal to a
  d-value"; it is a logical constraint. IF it held, it WOULD be a genuine non-circular amplifier:
  compute `s` from public `x` (no `d`), and for the core fraction KNOW `ε=0` — a constraint on `d`
  obtained without ever evaluating the d-containing `ε`.
- So circularity is the WRONG disqualifier here. Note the connection, though: a true deterministic pin
  of a *balanced* d-bit would itself be a genuine sub-DLP partial break (it extracts ≈H(A)≈0.9 bits of
  mutual constraint, §HAZARD-2) — precisely the leak the project tests for. That it does not exist is
  established by the marginal bound, not by "it would be circular."

**Consequence:** do not file this under "circular." File it under "marginally pre-refuted /
already-run / power-vacuous" per the top-line table. Mislabeling it circular would wrongly imply a
public-antecedent⇒scalar-consequent implication is inadmissible in general; it is not.

---

## HAZARD 2 — ALREADY-NULL-MI + the marginal impossibility (THE CRUX)

**RULING: for every MI-tested (balanced) scalar carry the deterministic test is STRICTLY WEAKER than
what is already known — pre-refuted by an exact marginal bound AND already excluded by the MI null.
The "MI might miss a deterministic law" motivation is quantitatively void here.**

### (2a) The exact marginal (Fréchet) bound — no data needed

Let `A=[s(x_P)<3/16]` with `p_A := Pr[A=1]` and `ε` the scalar carry with `q := Pr[ε=1]`. The
implication `A=1 ⇒ ε=0` is the statement `Pr[A=1 ∧ ε=1]=0`. But for ANY joint distribution,
```
Pr[A=1 ∧ ε=1]  ≥  max(0, p_A + q − 1)     (Fréchet lower bound).
```
Measured marginals (scope-tagged): `p_A ≈ 0.68` (`s_gate_v2`: 0.6786–0.6893 small p, 0.6831 secp);
`q ≈ 0.49` for `ε_u` (`joint_fiber`: 0.4878 real-82, 0.4987/0.5043 constructed). Hence
```
Pr[A=1 ∧ ε=1] ≥ 0.68 + 0.49 − 1 = 0.17  >  0.
```
**The deterministic pin is IMPOSSIBLE for any scalar carry with `q ≥ 1 − p_A ≈ 0.32`.** The FORCED
violation rate is `≥ q − (1 − p_A) = q − 0.32`. On real-82: `≥ 0.17·82 ≈ 14` forced violations; on
constructed-full N=10⁴: `≥ 1700`. This is consistent with the executed `ε_7` run (21–93 violations,
`eps_to_d_constraint_v1`) and needs no run to establish for `ε_u`.

### (2b) A deterministic pin ⇒ MI far above the MI-null already reported (cross-check)

If `A=1 ⇒ ε=0` held with `p_A=0.68` at the feasibility boundary `q=0.32`, the 2×2 table is
deterministic both ways (`A=1 ⟺ ε=0`) and `I(A;ε)=H(0.68)≈0.90` bits. Even a rare feasible pin
(`q=0.01`) gives `I(A;ε)≈0.02` bits. Compare the reported MI-null power:
- real-82 `MI_min(80%,df=1)=0.103` bits, observed `Îhat(ε_u;b_eps)=0.001`, exact perm-p=0.79;
- constructed `MI_min=8.4×10⁻⁴` bits, observed `Îhat≈2×10⁻⁵`.

So a *balanced* pin (0.9 bits) is excluded by the real-82 MI null itself (0.9 ≫ 0.103). A *rare*
feasible pin (0.02 bits) is BELOW real-82 `MI_min` but ABOVE the constructed `MI_min` (8.4×10⁻⁴) — i.e.
the constructed-set MI test ALREADY has the power to see any firing-control-live deterministic pin.
**The only regime where a deterministic law could hide under MI is {small N (real-82, MI_min=0.10) AND
rare target}; but a rare carry on real-82 is degenerate/firing-dead (§HAZARD-3), so that window is
empty.** The deterministic-implication test buys nothing the existing MI machinery on the constructed
set does not already deliver.

### (2c) Verdict of HAZARD 2

For `ε_u` and `ε_7`: **REDUCES TO (and is strictly weaker than) the MI null** — additionally
pre-refuted by the marginal bound, and for `ε_7` already empirically refuted. Not new.

---

## HAZARD 3 — DEGENERACY: scope each target to the arm where it is non-degenerate

**RULING (computed, `OPEN_d2` + `ARSENAL` bookkeeping):**

- **Real-82 solved keys** are all `≪ n` (~2⁷⁰ vs 2²⁵⁶) ⇒ each is its own orbit-min rep ⇒
  `j_formula=0`, orbit carry `c=⌊d₀/n⌋=0` for ALL 82 (`OPEN_d2`: "all 82 carries ≡ 0 mod 3", sampling
  artifact). **Orbit-carry targets (parity, `[c=0]`, low bits) are DEGENERATE on real-82** (constant
  ⇒ zero variance ⇒ any test vacuous). Scope them to the **constructed full-range set only**.
- **Single-key `ε_u=[dλ mod n ≥ ⌈n/2⌉]` (j=1) is NON-degenerate on real-82** (`joint_fiber`:
  Pr[ε_u=1]=0.4878, balanced) ⇒ testable on real-82 — but marginally pre-refuted there (§HAZARD-2).
- Consequence: there is no arm on which an orbit-carry target is BOTH non-degenerate AND
  firing-control-live for this implication (constructed: `[c=0]` firing-dead at 2⁻²⁵⁴, parity
  marginal-pre-refuted; real-82: constant).

---

## THE FROZEN SPEC (the nine sections — filled so a genuinely-new variant inherits an exact spec)

### 1. OBJECT
Whether the public core-membership predicate `A=[s(x_P)<3/16]` (exact integer fn of `x` alone) is a
DETERMINISTIC sufficient condition pinning a scalar-side carry bit `ε_scalar(d)` (a fn of `d` in
`Z/n` via λ) to 0 — i.e. a search-space cut on `d`, NOT a mutual-information question. Feature (public
`s`) and target (`ε_scalar`, contains `d`) are disjoint-construction (no `d` in the `s`-path), so this
is not the `r=v−w` tautology family. **Tautology/circularity check: PASSES** (§HAZARD-1); the object
is well-posed. It is disqualified downstream by feasibility/power, not by construction.

### 2. STATISTIC
Exactly one: **`V = #{ samples with s<3/16 AND ε_scalar=1 }`** (integer count of violations of the
implication). Distribution under the "no-pin" null (independence of `A` and `ε` given the marginals):
`E[V] = N·p_A·q`, hypergeometric/binomial spread. **Pre-committed decision rule:** `V=0` ⇒ pin
consistent (over the sampled N only); `V>0` ⇒ deterministic refutation. NOTE (frozen): by §2a,
`V ≥ N·max(0,p_A+q−1)` is FORCED for any `q≥1−p_A`, so `V=0` is unreachable for balanced targets
regardless of data — the statistic is degenerate against balanced carries.

### 3. MATCHED CONTROL
Shuffle the `ε_scalar` labels against a FIXED `s<3/16` mask, on μ₆-canonicalized / orbit-deduped
records (as in `joint_fiber`/`twokey`). Preserves both marginals `p_A, q` and the μ₃/j forcing;
destroys only the alleged `A→ε` pin. Shuffle `V` centers on `N·p_A·q`. A real `V` BELOW the shuffle
band would indicate a pin — but the Fréchet floor forbids `V` from dropping below `N(p_A+q−1)`, so for
balanced `ε` the real `V` sits INSIDE the shuffle band by construction (no separability). The shuffle
control is therefore VALID but shows the "clean pass" cannot occur for balanced `ε`.

### 4. PLANTED CONTROL (firing) — the decisive gate
The implication is non-trivial only if `ε_scalar=1` CAN co-occur with `s<3/16` (the consequent's
negation is reachable). **Firing check = "does `ε_scalar=1` occur AND co-occur with `s<3/16` in the
matched null?"**
- Balanced `ε_u/ε_7/c-parity`: firing control **ALIVE** (ε=1 common; ≥17% forced co-occurrence) ⇒ the
  test FIRES ⇒ returns a refutation (this is exactly the 21–93 violations already seen). A live firing
  control here means a *refutation*, not a pass.
- Rare `ε=[c=0]`: firing control **DEAD** (ε=1 occurs with prob ≈2⁻²⁵⁴; never in feasible N) ⇒ the
  null is uninformative ⇒ **any "0-violation" pass is VACUOUS, full stop** (agent rule: a control that
  cannot fire invalidates the null).

### 5. POWER
Exact/one-sided: the deterministic test either finds a violation in N samples or does not; absence in N
bounds but does not prove the universal implication. Frozen power facts:
- Balanced targets: `V` is bounded BELOW by `N(p_A+q−1)>0` ⇒ the test cannot return 0 ⇒ it is
  *pre-determined to refute*, not powered to confirm.
- Rare `[c=0]` target: expected violations under the null `= N·p_A·q ≈ N·0.68·2⁻²⁵⁴ ≈ 0` at
  N≤10⁶ ⇒ **zero power** (no ε=1 point to violate on), and MI would see it anyway if it fired (§2b).

### 6. SCOPE
Every number inherits: secp256k1; `s`/`eps` per `s_gate_v2`; `λ`=canonical LAM, threshold `⌈n/2⌉`
(ε_u) or `r₁=⌊n/2⌋`, j=1 (ε_7); orbit carry `c=⌊d₀λ^j/n⌋`. Arms × targets (non-degeneracy enforced):
`ε_u`: real-82 + constructed. `ε_7`: constructed (and the enumerable p∈{43,547,907,1303} where it was
run). orbit-carry: constructed-full only (degenerate real-82). Enumerable-p results do NOT transfer to
secp scale (a null does not inherit scale; an exact identity/bound does — and §2a IS an exact bound,
so IT transfers).

### 7. FALSIFICATION
This RULING is falsified if someone exhibits a scalar-carry object that is simultaneously (i)
marginally feasible (`Pr[ε=1] ≤ 1−Pr[s<3/16] ≈ 0.32`), (ii) firing-control-live on some arm (ε=1
occurs AND co-occurs with s<3/16 with nonzero expected count), (iii) NOT defined by a threshold chosen
after observing s's rate (no post-hoc rarity tuning), and (iv) not already MI-tested — and then shows
`V=0` over N with the shuffle control non-vacuous. Absent such an object, the reducibility stands.

### 8. EXACTNESS
Signal path exact: `s<3/16` by integer cross-product `N(eis(x))·16 < 3·p`; `ε_scalar` by integer
comparison in `Z/n`; `c=⌊d₀λ^j/n⌋` integer floor. Marginal bound §2a is exact rational arithmetic.
Only float carve-out permitted: the reported densities `p_A,q` and any MI log₂ (analytic size, ranked
against an integer-count permutation null; no key in the path). `check_no_float.sh` must exit 0 before
any run.

### 9. PRE-COMMITMENT (grade slots, all filled before any run)
- **`ε_u` / `ε_7` / `c-parity` (balanced):** `[REDUCES TO THE MI NULL — pre-refuted by the marginal
  bound; ε_7 additionally empirically refuted, 21–93 violations, `eps_to_d_constraint_v1`]`. No grade
  moves. **← THIS SLOT FIRES.**
- **`ε=[c=0]` (rare, constructed):** `[UNINFORMATIVE — firing control dead, power ≈ 0; a 0-violation
  pass is vacuous]`. Not a null of record.
- **Any post-hoc-rarity target (threshold on c chosen to match 3/16):** `[INADMISSIBLE — statistic /
  threshold chosen after looking; the ordering failure this gate exists to prevent]`.
- **Hypothetical genuine pin (does not occur here):** would grade `[EMPIRICAL — search-space cut, bits
  + scope]` per §(d) below, pending independent reproduction; contradicts the marginal bound so would
  be treated as an instrumentation defect until reproduced.

---

## (d) SEARCH-SPACE-CUT QUANTIFICATION — IF the pin held (it cannot, for balanced ε; recorded for completeness)

Were `s<3/16 ⇒ ε=0` true for the ~68% core:
- `ε_u` is 1 bit ⇒ `ε_u=0` means `dλ mod n < ⌈n/2⌉` ⇒ a factor-2 (1-bit) cut on `d` (via λ⁻¹) for
  those keys; **0 bits for the other ~32%**. Net over a random key: ≤1 bit, on 68% of keys.
- **Ceiling of the whole class ≈ 3 bits** (ARSENAL tool 7: all 6 (s,j) branches remove ~1.4 bits,
  ~3 independent bits; tool 6: μ₆ saturation caps automorphism extraction at mod 6 ≈ 2.58 bits). So
  even a perfect pin is a constant-factor, not a break.
- **Babai/GLV lattice does NOT compound it.** `ANALYSIS_...circularity_v1.md §4`: Babai/GLV
  "decomposes a KNOWN scalar; it does not recover an unknown one." A partial carry bit does not feed a
  lattice step that yields more than the carry itself. No amplification.

**So the dreamed payoff is ≤3 bits with no lattice compounding — and it is marginally unreachable for
balanced carries. The `s<3/16` core-membership predicate does NOT deterministically pin a balanced
scalar-carry bit.**

---

## REPAIR — the minimal non-circular object that is actually new (register separately, do not run here)

The motivating hope ("public core-membership → a cut on d") is not dead as a PROGRAM; only this
implication over these carry objects is reducible. The two non-reducible directions, with the exact
conditions that make each new:

1. **Geometric (lattice), not carry-bit.** `RESULT_joint_carry_twokey_mi_v1.md` named it: does public
   `s<3/16` core-membership, composed with a Babai/GLV-lattice step, cut the `d`-search space via a
   GEOMETRIC constraint (a region in the λ-decomposition lattice), independent of pinning any balanced
   carry bit? This escapes §2a because it is not a single-bit implication. **Caveat inherited:** it
   still needs a REAL scalar constraint to feed Babai; §2a shows `s<3/16` supplies none via `ε`, so a
   new run must FIRST exhibit a non-trivial scalar constraint from `s` before the lattice step is
   meaningful. Register with a firing control that a nonempty, strictly-smaller lattice region results.
2. **A RARE, firing-control-live, pre-defined scalar carry on the constructed set.** If (and only if) a
   scalar object exists with `Pr[ε=1]∈(0, 0.32]`, defined without reference to s's rate, whose `ε=1`
   event co-occurs with `s<3/16` with nonzero expected count at feasible N — register the deterministic
   test AND the matched MI test (which, per §2b, already has the power). No such natural object is in
   the registered arsenal (`[c=0]` is firing-dead; low bits are balanced).

Neither repair is this test; both are new pre-registrations. The `μ₆` solving-degree lever for the j=0
Semaev system (`ANALYSIS_semaev_cm_yield_mechanism_v1.md P2`) lives outside this frame entirely and is
untouched by this ruling.

---

## Owed gates
`citation-verifier` on the Cap-Law `¾:⅛:⅛` / `eps=0⟺core` and the `s∈[0,¾]` inputs before any grade
moves up on them. `compile-diff` if folded into a master. This document moves NO grade up and closes NO
avenue; it rules one implication reducible on an exact bound + an already-executed run + a computed
degeneracy.
