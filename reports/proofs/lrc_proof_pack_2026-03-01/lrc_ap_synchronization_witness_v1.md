# AP Synchronization Witness Program (Route 1) v2
Date: 2026-03-04
Status: Floor Identity (PROVED), Dead Zone (PROVED), Coverage Equivalence (PROVED),
        Prime-a transition witness (PROVED), General Lemma B (PROVED via Sole Cover route —
        see lrc_dropped_runner_witness_v1.md §11; R1.D route is no longer load-bearing)
Scope: Case-2, Case-iiib locked scope from `lrc_dropped_runner_witness_v1.md`

---

## 0) Purpose and Status Update

**Lemma B is now PROVED** via the Sole Cover Witness (see `lrc_dropped_runner_witness_v1.md` §11).
The proof does not require Route-1 (AP synchronization) at all.

**Sole Cover Witness (summary):** For each d ∈ {a,b}, the residue r_d = −d⁻¹ mod n is
covered SOLELY by runner d on the interval (1/n, 1/(n−1)) ⊂ I_div. At state t=0, which holds
throughout this interval, bad_set(e,0,n) for any e ≠ d cannot contain r_d (unit-solo argument).
Since d is dropped, Miss_{E_fix}(r_d) ⊇ (1/n,1/(n−1)). This is a 4-step arithmetic proof with
no empirical steps.

This note is retained as a record of the AP synchronization approach and the proved sub-theorems
(Floor Identity, Dead Zone, Coverage Equivalence) which remain valid and may have independent use.
The R1.D claim (open below) is no longer a critical blocker.

---

Original purpose (archived): This note formalizes the Route-1 strategy for the single remaining blocker:

**Lemma B (was open; now proved by alternate route):** there exists a dropped-runner transition
`t*/e*` whose entering residue `r_enter(t*)` is not pre-covered by `E_fix`.

This note rewrote Lemma B as an AP-rigidity contrapositive (archived for reference):

> If `E_fix` pre-covers every entering residue at every transition of `e*`, then the speed
> structure is AP-synchronized; therefore non-AP Case-iiib must fail this universal pre-coverage
> at least once.

---

## 1) Locked Scope and Definitions

Setting (same as `lrc_dropped_runner_witness_v1.md`):
- `n >= 10`, one-divisible branch.
- `E_fix = {1,...,n-1} \\ {a,b}` (Case-iiib near-complete).
- `gcd(a,n)=gcd(b,n)=1` (unit dropped runners in this branch).
- choose `e* in {a,b}` and let `b*` be the other dropped runner.
- `I_div = [1/n, (n-1)/n]`.

Objects:
- `bad_set(e,t,n) = Sol(e,-t,n) U Sol(e,-(t+1),n)`.
- transition of `e*`: `alpha_t = t/e*` with `alpha_t in I_div`.
- entering residue at `alpha_t`:
  `r_enter(t) = (e*)^{-1} (-(t+1)) mod n`.
- pre-transition fixed coverage:
  `U_fix^-(t) = U_{e in E_fix} bad_set(e, floor(e*alpha_t)-1_if_boundary, n)`.

Define the universal pre-coverage property:

`UPP(e*)`: for every admissible transition `t/e* in I_div`,
`r_enter(t) in U_fix^-(t)`.

Lemma B is exactly `NOT UPP(e*)` for some choice of `e* in {a,b}`.

---

## 2) Route-1 Target Theorem (Contrapositive Form)

### Theorem R1 (target)
Under locked Case-iiib scope:

`UPP(e*)  =>  AP-synchronization constraint S(e*)`.

Then, if `S(e*)` is incompatible with non-AP Case-iiib templates, we get:

`non-AP Case-iiib  =>  NOT UPP(e*)  => Lemma B`.

So the only load-bearing analytic step is proving that universal pre-coverage forces the AP-type synchronization constraint.

---

## 3) Three Proved Theorems from Explicit Floor Arithmetic

These are new results proved this session. All verified computationally.

### Theorem FD (Floor Decomposition Identity) — PROVED
For gcd(a,n)=1 and T_e = floor(e·t*/a):
```
T_e  ≡  c_e·t*  −  a⁻¹·(e·t* mod a)   (mod n)
```
where c_e = e·a⁻¹ mod n.
Proof: write e·t* = a·T_e + (e·t* mod a), multiply through by a⁻¹ (mod n). ∎

### Theorem CE (Coverage Equivalence) — PROVED
r_enter(t*) ∈ bad_set(e, T_e, n) iff T_e ≡ c_e·(t*+1) or c_e·(t*+1)−1 (mod n).
Combining with FD: coverage holds iff
```
(e·t* mod a)  =  (n−e) mod a    [Condition A: applies when e > n−a]
               or (a−e) mod a    [Condition B: applies when e < a]
```
Proof: substitute FD into CE and simplify mod n, then reduce to mod a since remainders < a. ∎

### Theorem DZ (Dead Zone) — PROVED
For e with a < e ≤ n−a: r_enter(t*) ∉ bad_set(e, T_e, n) for EVERY t*.
Proof: Condition A requires n−e < a (fails since n−e ≥ a). Condition B requires e < a (fails).
For condition B with e > a: required value = (n+a−e) mod a ≥ 2a−a = a > a−1. Impossible. ∎

### Corollary GCD (GCD Exclusion) — PROVED
For e > n−a: Condition A requires gcd(e,a) | (n−e). If gcd(e,a) ∤ (n−e), runner e also
cannot cover r_enter(t*) for any t* (no solution exists to the congruence). ∎

### R1.A (bijection in transition index) — Status unchanged
As t ranges over T_int(e*), r_enter(t) runs through a structured residue set.
Status: PROVED (unit inverse + affine map in t).

### R1.B (residue-to-floor congruence form) — PROVED (was PROVED-LOCAL)
Theorem CE above provides the clean global statement.
Status: PROVED via CE + FD.

### R1.C (coverage incidence matrix)
Define binary incidence:
`M_e(t)=1` iff runner `e` pre-covers `r_enter(t)` at transition `t`.
Then `UPP(e*)` is:
`sum_{e in E_fix} M_e(t) >= 1` for all transition indices `t`.

Status: PROVED (definition).

### R1.D (AP rigidity claim; load-bearing)
If `sum_e M_e(t) >= 1` for all `t` in the full transition index set of `e*`,
then floor-phase constraints force a global linear synchronization relation equivalent
to AP coverage relay.

Status: OPEN (this is the core theorem target).

### R1.E (non-AP incompatibility)
Case-iiib non-AP templates violate `R1.D` synchronization relation.

Status: OPEN (depends on R1.D statement form).

---

## 4) Candidate Mathematical Frameworks for R1.D

1. Beatty covering rigidity:
   treat `floor(e t/e*)` families as coupled Beatty-type sequences on the transition index.

2. Covering systems / exact cover of cyclic residues:
   interpret `M_e(t)` as periodic hit sets on `t mod e*`, then classify exact union conditions.

3. Farey incidence rigidity:
   transition graph on fractions `t/e*` with runner-hit labels; universal hit implies relay regularity.

Each route must produce a theorem with explicit hypotheses and no empirical step in the final implication.

---

## 5) Known Non-Implications (to prevent false shortcuts)

The following do **not** prove Lemma B by themselves:

1. Farey freezing (`NR`): gives constant supports on an interval, not non-coverage.
2. global measure lower bounds from naive summation: become vacuous for larger `n`.
3. per-residue pigeonhole on cardinalities: enough slots exist to cover a fixed residue pointwise.

These are support lemmas only; they are not the missing synchronization break.

---

## 6) Diagnosed Failure of the Transition-at-Dropped-Runner Approach

### Prime a — WORKS

For prime a: each small runner e < a blocks exactly gcd(e,a)=1 transition t* value
(specifically t* = a−1 for all e < a simultaneously). Transitions t* ∈ {1,...,a−2} are
unblocked by all small runners. If the GCD Exclusion knocks out all large runners above
n−a (as in n=7, a=3: gcd(6,3)=3, 3∤1), then t*=1 is a witness. **PROVED for this case.**

### Composite a — FAILS for n≥11

For composite a, low-order runners e < a with gcd(e,a) > 1 block gcd(e,a) > 1 transition
values each. Example showing failure:

**n=11, a=4, b=7, E_fix={1,2,3,5,6,8,9,10}:**

Active blockers (non-dead-zone):
- e=1: gcd(1,4)=1 → blocks t*=3
- e=2: gcd(2,4)=2 → blocks t* ∈ {1,3} (both)
- e=3: gcd(3,4)=1 → blocks t*=3
- e=9: gcd(9,4)=1, n−e=2, 1|2 → blocks t*=2 (Condition A: 9·t*≡2 mod 4 → t*≡2 mod 4 → t*=2)

Union: {1,2,3} = all valid transitions for a=4. No witness. **The transition-at-dropped-runner
approach fails completely for n=11, a=4, b=7.**

The case b=7 also fails: checked all t* ∈ {1,...,6} for e*=b=7; all covered by E_fix. ✗

### Interpretation

The empirical data (1719 templates, 0 Miss failures) confirms that Miss_{E_fix}(r*) ≠ ∅
exists for these configurations — but the Miss interval is at a TRANSITION OF A FIXED
RUNNER in E_fix, not of a dropped runner. The dropped-runner transition approach is
sufficient for small n / prime a but not necessary or sufficient in general.

**Implication for Route-1:**
R1.D-Strict must be proved not as "∃ entering-residue failure at dropped-runner transition"
but as "∃ coverage gap anywhere in I_div" — a global coverage statement on the Farey
arrangement of E_fix.

---

## 7) Integration into Existing Chain

If R1 closes (`UPP => AP-synchronization`, non-AP contradiction), then:

1. Lemma B is PROVED.
2. `lrc_dropped_runner_witness_v1.md` chain yields M2 (`Miss(r*) != empty`).
3. M3 (already proved) gives positive discrete mass slope.
4. Cascades:
   - Y.3/Y.4/Y.5
   - Z.2/Z.4/Z.5
   - W.3/W.4
   - V.3/V.4/V.5

This closes the single remaining Case-2 blocker under the current architecture.

---

## 8) Concrete Next Proof Task

Write `R1.D` as a standalone lemma with explicit arithmetic statement on the transition index set:

- Domain: `t` such that `t/e* in I_div`.
- Predicates: `M_e(t)` in closed modular form (no set-language ambiguity).
- Claim: `forall t, exists e: M_e(t)=1` implies a constrained linear phase relation across `e`.
- Final step: show that relation is incompatible with non-AP Case-iiib templates.

This is the pen-and-paper target. Everything else is already scaffolding.

---

## 9) R1.D Strict Modular Statement (Ready-to-Prove Form)

This section provides the exact `t`-domain and closed form for `M_e(t)`.

### 9.1 Transition index domain
Fix dropped unit runner `e* in {a,b}`.
Use interior transition indices:

`T_int(e*) := { t in Z : 0 <= t <= e*-1 and 1/n < t/e* < (n-1)/n }`.

Boundary transitions are intentionally excluded here and handled by the existing boundary lemmas.

### 9.2 Left-state floor at transition `t/e*`
For each `e in E_fix`, define the left-limit floor state at `alpha=t/e*`:

`tau_e^-(t) := floor(e*t/e*) - chi(e* | e*t)`,

where `chi(P)=1` if predicate `P` is true, else `0`.

This is exact for `floor(e*alpha)` evaluated at `alpha = t/e* - 0`.

### 9.3 Entering residue
Since `gcd(e*,n)=1`, define:

`r_enter(t) := (e*)^{-1} (-(t+1)) mod n`.

### 9.4 Closed form of pre-coverage indicator
For each `e in E_fix`, define

`M_e(t) := 1_{ r_enter(t) in bad_set(e, tau_e^-(t), n) }`.

Then `M_e(t)=1` is equivalent to the pair of congruences:

`e*r_enter(t) == -tau_e^-(t) mod n`  OR
`e*r_enter(t) == -(tau_e^-(t)+1) mod n`.

Substitute `r_enter(t)` and define `lambda_e := e*(e*)^{-1} mod n`:

`M_e(t)=1  <=>  lambda_e*(t+1) == tau_e^-(t) mod n`
`              OR lambda_e*(t+1) == tau_e^-(t)+1 mod n`.

This form is valid for both unit and non-unit fixed runners `e`.

### 9.5 Universal pre-coverage in matrix form
Define the incidence family:

`M(t) := (M_e(t))_{e in E_fix}`.

Then universal pre-coverage for direction `e*` is exactly:

`UPP(e*)  <=>  for all t in T_int(e*):  sum_{e in E_fix} M_e(t) >= 1`.

Lemma B in this direction is:

`exists t in T_int(e*) such that sum_{e in E_fix} M_e(t) = 0`.

### 9.6 R1.D (strict target statement)
`R1.D-Strict (OPEN):` If `sum_{e in E_fix} M_e(t) >= 1` for all `t in T_int(e*)`,
then the family `{tau_e^-(t), lambda_e}` satisfies a global phase-lock relation
`S(e*)` equivalent to AP relay synchronization on transition indices.

`R1.E-Strict (OPEN):` In non-AP Case-iiib templates, `S(e*)` fails for at least one
choice of dropped direction `e* in {a,b}`.

Combining `R1.D-Strict + R1.E-Strict` gives Lemma B.

---

## 10) Immediate Proof Tasks for R1.D-Strict

1. Derive periodicity of `M_e(t)` as a function on `t mod l_e`, where
   `l_e` is induced by `e*` and `n` through `tau_e^-(t)` and `lambda_e`.
2. Characterize `H_e := {t in T_int(e*): M_e(t)=1}` as a union of arithmetic slices.
3. Show `T_int(e*) = union_{e in E_fix} H_e` forces the AP phase-lock relation `S(e*)`.
4. Prove non-AP incompatibility of `S(e*)`.
