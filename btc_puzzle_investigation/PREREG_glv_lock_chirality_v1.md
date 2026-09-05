# PREREG — GLV chirality lock `χ(a)=sign(Im α₂/α₁)`: RETIRED BEFORE RUN

*Frozen 2026-07-28 by `experiment-designer`. Nothing run. No grade moves. No leakage / key-recovery /
ECDLP claim. This is a **retired-before-run** pre-registration: the test is disposed of by an
established fact, not by data.*

---

## 0. Disposition (one line)

**RETIRED — the proposed statistic's feature and target share construction.** `η(a)=α₂/α₁` at `a` and
at `λa` are read from the **same** Frobenius eigenvalue multiset, because `L*(a)=L*(λa)` is an exact
family identity; hence `χ(λa)=χ(a)` is **forced**, and the only branch the test can return is the
tautological one. The informative branch requires an **internal** `ω`-action on `H¹(F_a)` that is
**explicitly retracted**. Forcing structure:
`RESULT_anew_twisted_eigenvalues_nonabelian_v1.md` §4b (and §3). Zero information; not runnable as posed.

---

## 1. The test that was to be pre-registered

- **Chirality:** `χ(a) := sign(Im(α₂/α₁)) ∈ {±1}`, reading the four eigenvalues `α_i=√p·z_i`
  (`z⁴+m z²+1=0`) from the `n1_twisted_eigenvalues_v1.sage` output.
- **GLV `ℤ/2` dichotomy under `a↦λa` (`λ³=1 mod n`):**
  - Cell **S** `{ φ acts as one scalar on all of H¹(A_new) ⇒ χ fixed ⇒ FORCED / tautological / 0 bits }`
  - Cell **I** `{ φ distinguishes / swaps the two Frobenius pairs ⇒ χ(λa) = −χ(a) ⇒ informative }`
  - `η→1` cases excluded (they break the proven `120°` law).

Task instruction: *verify or refute the dichotomy from the eigenvalue algebra before building on it.*
Result of that verification is §2.

---

## 2. Why it is retired: the forcing structure (the tautology, verified two ways)

### 2a. Established fact (cited, object-level)
`RESULT_anew_twisted_eigenvalues_nonabelian_v1.md` (2026-07-27, `[VERIFIED — p=43,67; plant-validated]`):

- **§4b** — `ω:(x,y)↦(ζ₃x,y)` "puts a genuine `μ₃` into the arithmetic of the **family**
  (`L*(a)=L*(λa)`; `L*` over the index-3 subfield). **It does not act *internally* on `H¹(F_a)`
  (still retracted)**; it constrains the monodromy group to contain/commute with this `μ₃`."
- **§3** — the `a≠0` eigenvalues are **GL(2) / big-monodromy, non-abelian over `ℚ`** (splitting field
  not even Galois; FAIL at `σ₃₁₃` for `p=43`, `σ₇₉₃` for `p=67`). The `120°` ratio `α₂/α₁=ζ₃` "is **NOT
  an arithmetic fact about the eigenvalues — it is a relation *within* the GL(2) structure, i.e. a
  MONODROMY / geometric fact.**"

`L*(a)=L*(λa)` ⇒ the Frobenius characteristic polynomial (hence the eigenvalue **multiset**, hence any
representative pairing `η=α₂/α₁`, hence `χ`) is **identical** at `a` and `λa`. `χ(λa)=χ(a)` is forced —
Cell **S** — **not** because `φ` is a scalar on `H¹`, but because the family symmetry hands back the
same eigenvalues. Cell **I** (`χ` flips ⟺ `φ` distinguishes the pairs *internally*) is exactly the
internal action §4b retracts.

### 2b. Independent trace-level witness (the eigenvalue algebra, derived here)
`V_k(a)=Σ_{P∈E(F_{p^k})} χ₂(y_P)·χ_a(Tr_{k/1}P)`, power sums `p_k(a)=−V_k(a)`. `φ` is `F_p`-rational,
`φ³=id`, commutes with `Tr`; `φ(x,y)=(βx,y)` fixes `y` (so `χ₂(y_{φP})=χ₂(y_P)`) and sends
`Tr(φP)=φ(Tr P)=[λ·d]G` (so `χ_a(Tr φP)=χ_{λa}(Tr P)`). Reindex the sum by the bijection `P↦φP`:

> `V_k(a) = Σ_P χ₂(y_{φP})·χ_a(Tr φP) = Σ_P χ₂(y_P)·χ_{λa}(Tr P) = V_k(λa)`,  **exactly, every `k`.**

Equivalently, the exact integer histogram `h_k` is `λ`-invariant (`h_k[λd]=h_k[d]`). So `p_k(a)=p_k(λa)`
⇒ identical char poly ⇒ identical eigenvalue multiset — the trace-level form of the cited `L*(a)=L*(λa)`.
The `phase_structure_T_v1.py` identity `T(a,b)=T(λa,βb)` (D2a, exact) is the same fact on the full 2-D
transform.

**Verdict on the dichotomy:** the biconditional `"χ fixed ⟺ φ scalar"` is **REFUTED as a test** — `χ`
fixed is implied by the reindexing identity alone, independent of how (or whether) `φ` acts on `H¹`.
Cell **S** is reachable with probability 1 and carries no information; Cell **I** is unreachable.

### 2c. Concrete convention-ambiguity (why `χ` is not even a multiset invariant)
For `m=1` the multiset is `√p·{ω,ω²,−ω,−ω²}` (angles `{±π/3,±2π/3}`). The `α↦−ᾱ` pairing gives two
`±`-pairs `{ω,−ω²}` and `{ω²,−ω}`; the representative choice that keeps `η` a primitive cube root
admits **both** `(α₁,α₂)=(ω,ω²) ⇒ χ=+1` **and** `(−ω²,−ω) ⇒ χ=−1` from the *same* multiset. So `χ` is a
function of `(multiset + representative choice)`, and the only arithmetic rule that fixes the
representative is the **internal `φ`-eigenspace label** — the retracted object. The `.sage` output prints
`phs = sorted([...])`, which discards the pairing entirely.

---

## 3. The nine-item spec, each collapsed to its retirement reason

1. **OBJECT.** Intended: whether `φ` splits `H¹(A_new)` into two `μ₃`-eigenspaces aligned with the two
   Frobenius pairs (Cell I) or not (Cell S). For `a≠0` this internal object **does not exist** (§4b
   retraction); `φ` acts only on the family `{H¹(F_a)}` by `a↦λa`. The chirality `χ` read from the
   `.sage` eigenvalue output measures a **proxy** (the GLV-invariant multiset), not the object.
2. **STATISTIC.** `χ(a)=sign(Im α₂/α₁)`, aggregated as the count over `μ₃`-orbits `{a,λa,λ²a}` of
   `#{orbits all-equal}` vs `#{orbits with a flip}`. **Pre-run value is forced:** `(n−1)/3 : 0`. A
   deterministic all-equal count is not a statistic under any null.
3. **MATCHED CONTROL.** Requested: shuffle the `a↔λa` pairing. **Invalid null** — see §4b(control).
4. **PLANTED CONTROL.** No planted swap can fire: Cell I is unreachable on this instrument (`V_k(a)=
   V_k(λa)`). By the standing rule *a positive control that cannot fire ⇒ the null is uninformative* —
   this is the terminal condition, and it is why the test is retired rather than run.
5. **POWER.** **Zero, at every `n` and every number of primes.** `χ(a)−χ(λa)≡0` is an exact identity,
   not a small-sample effect; no quantity of data changes it. (Same class as the "N=82, needs `f=1.0`"
   zero-power null in the charter — here the power is identically 0, not merely low.)
6. **SCOPE.** The eigenvalue instrument enumerates all of `F_{p^k}` (`k≤4`) plus a full `n`-point
   discrete-log table and an `O(n²)` transform — feasible only for small `p` (default `p=13`; law
   measured `p≤547`). Non-abelian verdict established `p=43,67`; `p=13` (`n=7`) is the exception.
   **No transfer to `p=2²⁵⁶−2³²−977`:** `RESULT_mu4_eigenvalue_individual_v1.md` §4 states the `m`-value
   (hence the eigenvalue angles, hence `χ`) is undetermined at that prime and the scale-free `μ₄`
   argument leaves it open; the `p^k` enumeration is infeasible there regardless. Any claim is scoped to
   the small-prime window only.
7. **FALSIFICATION (of Cell I).** Already met **pre-run**: §4b retracts the internal `ω`-action, and §3
   proves the `a≠0` eigenvalues non-abelian ⇒ the `ζ₃` ratio is monodromy, not eigenvalue-arithmetic —
   so nothing internal to `H¹(F_a)` can carry a `φ`-driven sign flip.
8. **EXACTNESS.** Signal path `h_k` is exact integer (project no-float rule satisfied). The eigenvalues
   and `arg(α_i)/π` are `CC` (float). The `χ` sign would be a float readout of a quantity the **exact**
   invariants provably cannot carry a sign for: `m` (integer) and `s₁²+s₁s₂+s₂²=3/4` are both symmetric
   under `ω↔ω²`. So the sign is not an exactness carve-out of "analytic size only" — it is reading a
   labeling artifact below the exact invariants. Additional retirement ground.
9. **PRE-COMMITMENT.** The forced `(n−1)/3 : 0` count is recorded as **tautological / uninformative**,
   never as "`χ` fixed ⇒ `φ` scalar ⇒ interesting." No follow-up statistic is run on the frozen window.

---

## 4. Instrument determinations the task requested

### 4a. Control `C2` — identity and scope
`C2` = **Newton / root-solver recovery unit-test** (`.sage` lines 109–127): plant
`√p·{z₆¹,z₆²,z₆⁴,z₆⁵}` at `p=43`, synthesize `p_1..p_4`, confirm the `Newton→charpoly→CC-roots` solver
returns the planted tuple within `1e-6` (`ANALYSIS_..._v1 §7`: fires at `4.4e-16`).
**Scope:** validates only the *numerical solver*, at one prime, on one planted (`m=1`-shaped) tuple. It
does **not** validate `V_k↔Frobenius` (that is `C1` weight `+ C3` dimension `+` the `a=0` trace-zero `L1`
consistency), and it involves **no** `φ`, no `a`, no chirality. For this pre-registration `C2` fires but
is **orthogonal** — it cannot serve as the planted control for a swap.

### 4b. `phase_structure_T_v1.py` — does it fix how `φ` acts on the index `a`, and force Cell S?
**Yes to both, at the multiset level.** D2a establishes the **exact** frequency-plane symmetry
`T(a,b)=T(λa,βb)` (`max|diff|≈1e-14`) — the reindexing identity on the full 2-D transform. It fixes that
`φ` acts on the index `a` by `a↦λa` **uniformly, on the family** (moving `b↦βb` jointly), which is the
`L*(a)=L*(λa)` action; this forces Cell **S** at the eigenvalue-multiset level. It computes **no**
internal `φ`-eigenspace split (there is none for `a≠0`, §4b), so it neither opens nor informs Cell **I**.

**Matched control (requested shuffle `a↔λa`) — invalid null.** Preserves: the per-`a` eigenvalue
multiset, the `μ₆` orbit structure. Destroys: the `a↔λa` pairing — but that pairing's agreement is the
**by-definition** symmetry `L*(a)=L*(λa)`. A shuffle therefore breaks a *real* swap and the *spurious*
tautology in exactly the same way, so a "significant" true-vs-shuffled gap would be produced by the
identity alone. This is the documented invalid-null pattern (residue `r=v−w` vs `w`; the `μ₆`-mismatch
shadow): *a shuffle that destroys a symmetry the readout has by definition is an invalid null.* It
cannot distinguish "`χ` fixed because tautological" from "`χ` fixed because `φ` scalar," and cannot be
run to detect a swap because no swap is reachable.

---

## 5. Decidable outcome table (as outcomes, not verdicts)

| cell | structural condition (decidable) | reachable on the `.sage` / phase instruments? | reading |
|---|---|---|---|
| **S** `φ` scalar / pairs not separated | two Frobenius pairs share the `μ₃`-label ⇒ `χ(λa)=χ(a)` | **YES — forced, prob 1** by `V_k(a)=V_k(λa)` / `L*(a)=L*(λa)` | **tautological, 0 bits** |
| **I** `φ` splits / swaps the pairs | pairs sit in different internal `μ₃`-eigenspaces ⇒ `χ(λa)=−χ(a)` | **NO — unreachable**; the internal action is **retracted** (§4b), eigenvalues are non-abelian (§3) | informative branch **does not exist** for `a≠0` |

Both cells resolve without a run: **S** is the only reachable cell and it is tautological; **I** is
excluded by an established fact. No data would move this table.

---

## 6. The live object (redirect — where the `ζ₃` actually lives)

Per `RESULT_anew_twisted_eigenvalues_nonabelian_v1.md` §4 (L-mono), the between-pair `ζ₃` is a
**geometric / arithmetic monodromy** fact, not eigenvalue-arithmetic. The live target:

> **Identify the `μ₃` in the geometric / arithmetic monodromy group of `L_{χ₂(y)}⊗L_{χ_a}` on `H¹_c`
> that forces the between-pair ratio `α₂/α₁` to be a primitive cube root, uniformly in `a`.**

The `§4b` `ω`-descent (`ω:(x,y)↦(ζ₃x,y)`, `L*(a)=L*(λa)`, `L*` over the index-3 subfield) is an
**ingredient** of that route — it constrains the monodromy group to contain / commute with this `μ₃` —
**not** the internal order-pinning lever (that reading is retracted). A monodromy-route pre-registration
is a **separate** object from this one and would need its own spec; it is *not* a chirality-of-eigenvalue
statistic and must not be reformulated as one.

---

## 7. Scope banner

Everything above inherits: `E: y²=x³+7`; small primes with prime `#E(F_p)` (`p=13` exception, non-abelian
verified `p=43,67`, law measured `p≤547`); exact integer `h_k`, float `CC` eigenvalue extraction; **no
transfer to `p=2²⁵⁶−2³²−977`**. No leakage, key-recovery, or ECDLP statement is made or implied.
