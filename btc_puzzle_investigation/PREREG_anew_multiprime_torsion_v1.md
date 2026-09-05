# PRE-REGISTRATION — Multi-prime small-torsion labels of Q_d = S([d]G) ∈ A_new(F_p): beyond the ℓ=3 channel

**Status:** FROZEN pre-registration. Written BEFORE any Q_d datum for any ell>3 is computed.
**Frozen date:** 2026-08-22
**Author:** kellytmunroe@gmail.com (via experiment-designer, context-isolated spec)
**Extends (same methodology, NEW invariant class):**
`PREREG_anew_direct_invariant_partialinfo_v1.md` (parent, FROZEN 2026-08-22) and its powered result
`RESULT_anew_f5f6_powered_outcomeB_v1.md`. The parent tested ONLY ell=3 (its "f5") and returned
Outcome B at powered scale (p∈{5827,5839}, N_test≈490): no first-order d mod m leak of strength ≥ π=1/8
in the ℓ₀=3 torsion label. **ell=3 is therefore COVERED GROUND and is NOT re-tested as a primary here.**

**Grade contract (inherited verbatim):** every number produced under this spec inherits its SCOPE (the
prime it came from) and may never be stated without it. No grade promotion while any owed SELF-AUDIT slot
is open. This spec reuses the parent's statistic, decoder, null, controls, power model, exactness rule,
and realization engine (R1); it changes EXACTLY ONE thing — the invariant menu — and one consequence of
that change (the powered-prime ladder must be selected PER ELL, because the |A_new| factorization differs
across primes). Everything else is inherited, not reinvented.

---

## 0. Decision-integrity preamble (why ordering is the mechanism)

Everything choosable after seeing data is frozen in THIS file: the single verdict statistic `T` (inherited),
the decoder, the null (`K=9999`, integer exceedance `E`), the NEW invariant menu (below), the modulus set
`M(n)`, the per-ell prime ladder selection rule, the sample sizes, and the three controls with their
required behaviour. A positive cannot be manufactured by picking a lucky (ell, m) post hoc (menu frozen;
significance additionally requires SURVIVING collapse AND replicating on ≥2 powered primes that BOTH carry
that ell AND being out-of-sample). A null cannot be laundered into a find by adding an ell or m after the
fact (both sets frozen; L_MAX frozen). Neither verdict is reachable by reframing.

---

## 1. OBJECT (unchanged from parent)

- Curve `E : y² = x³ + B` over `F_p`, `p ≡ 7 (mod 12)`, `j(E)=0`, `n=#E(F_p)` PRIME, `G` a fixed generator.
- `d ∈ (Z/n)*` the discrete log of a public point `[d]G`.
- Cover `C : w⁴ = x³ + B`, genus 3; `Jac(C) ~ E × A_new`, `dim A_new=2`, `A_new` supersingular with CM by
  `Q(ζ₁₂)`, embedding degree 3, `|A_new(F_p)| = p²+p+1`.
- Map `S : E(F_p) → A_new(F_p)`: one (non-Galois-closed) 4th-root preimage, projected to the `A_new`
  isotypic component. `Hom(E,A_new)=0` ⇒ `S` is NON-homomorphic. `Q_d := S([d]G)`; `anew_part(X)=[nE]·X`
  isolates the `A_new` component. ORBIT LABEL: `ℓ(λd)=p²·ℓ(d)`, partitioning `(Z/n)*` into λ-orbits
  `{d,λd,λ²d}` (≈1.585 bits) — a KNOWN structural fact, quotiented out, NOT what we test.
- **Object under test:** whether a small-torsion label of `Q_d` at a prime `ell | |A_new|` with `3 < ell ≤
  L_MAX` carries first-order information about `d` (its residue `d mod m`) beyond the orbit label.

**Tautology check (disjoint construction, inherited).** The feature is a function of the POINT `Q_d`
(its `ell`-torsion image); the target is a function of the SCALAR `d` (its residue `d mod m`). They meet
ONLY through the pipeline `d → [d]G → S → Q_d → f_ell` whose leakage is the hypothesis. `f_ell` is never
computed from `d mod m`. The torsion prime `ell` and the target modulus `m` are DISTINCT and independently
sourced (`ell` from the factorization of `|A_new|`; `m` from `M(nE)`), so no forced coincidence links
feature and target. This is NOT the forbidden `r=v−w` vs `w` tautology.

---

## 2. THE NEW INVARIANT MENU (the ONLY thing that changes)

Freeze **`L_MAX = 100`.** For a prime `p`, factor `|A_new| = p²+p+1 = ∏ ell_i^{a_i}`. A prime `ell` can
divide `p²+p+1` only if `ell = 3` or `ell ≡ 1 (mod 3)` (the order-3 cyclotomic factor splits mod `ell` iff
`ell ≡ 1 mod 3`); the candidate NEW primes are therefore exactly

`ELL(L_MAX) = { ell prime : 3 < ell ≤ 100, ell ≡ 1 (mod 3) } = {7, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97}`,

and for a given `p` the ACTIVE set is `ELL(p) = { ell ∈ ELL(L_MAX) : ell | p²+p+1 }` (a subset that varies
by prime). Each `ell | |A_new|` divides `p²+p+1` to first power at these primes (verified: at p=5827
`|A_new|=3·13·433·2011`, at p=5839 `|A_new|=3·11366587`), so `A_new[ell] ≅ (Z/ell)²`.

**Feature `f_ell(Q_d)` (DLP-free, cost `O(ell²)`):**
`f_ell(Q_d) := canonical_id( [ |A_new| / ell ] · anew_part(Q_d)  ∈  A_new[ell] )`,
where `canonical_id` is a fixed lookup: pre-enumerate the realized `A_new[ell]` set (`ell²` points) under a
frozen basis and return the index of the matched point in `{0, …, ell²−1}` (or a frozen canonical
2-coordinate `(a,b) ∈ (Z/ell)²`). The internal `ell`-torsion match is `O(ell²) ≤ 9409` — cheap, and is NOT
the full-group `A_new` dlog (which is the forbidden/dead MOV step, Corollary C).

**Joint CRT tuple `f_CRT(Q_d)`:** the tuple `( f_ell(Q_d) )_{ell ∈ ELL(p)}` — the combined small-torsion
coordinate at that prime, taken over the NEW-menu ells only (`3 < ell ≤ L_MAX`). By CRT this is the label
of `[ |A_new| / ∏ELL(p) ] · anew_part(Q_d)` in `A_new[∏ELL(p)]`. **ell=3 is EXCLUDED** from `f_CRT`
(covered ground; including it would re-credit the closed channel). A secondary diagnostic tuple that
prepends `f_3` is REPORTED non-verdict only.

**Frozen menu `F_new` = { f_ell : ell ∈ ELL(L_MAX) } ∪ { f_CRT }.** ell=3 is NOT in `F_new`.

**Modulus set `M(n)` (inherited verbatim):**
`M(n) = { m ∈ {2,5,7,11,13} : (λ mod m) ∉ {0,1} } ∪ { smallest 2 primes >3 dividing n−1 }`.
`n = nE` is a public curve parameter; deriving `M(n)` is not post-hoc. Guard keeps the λ-orbit acting
non-trivially on `Z/m` so orbit-label alone cannot fix `d mod m`.

---

## 3. STATISTIC (inherited verbatim from parent §2)

**`T(p, f, m)` = out-of-sample MAP-recovery count of `d mod m` from `f(Q_d)`,** an integer, the SOLE
verdict statistic. Protocol per powered prime `p`:
1. Fix `E` (smallest `B>0` with `nE=#E(F_p)` prime, `j=0`), `G`, `nE`.
2. Draw `N_p` DISTINCT λ-orbits; take canonical rep `d* = min{d, λd, λ²d} (mod n)`. One rep per orbit.
3. Compute `Q_{d*}=S([d*]G)` via R1, then `f(Q_{d*})` for each `f ∈ F_new`. No `A_new` dlog.
4. TRAIN/TEST split by a fixed permutation seeded by `p` (seed = `p`), equal halves.
5. TRAIN: MAP decoder `g_{f,m}(a)=argmax_b #{train: f=a, d* mod m=b}` (ties → smallest `b`). Frozen.
6. TEST: `T = #{test: g_{f,m}(f(Q_{d*})) = d* mod m}`.
7. Null: EXACT PERMUTATION of TEST-set `d* mod m` labels, `K=9999`, frozen decoder;
   `E = #{perm: T_perm ≥ T_obs}`; p-value `=(1+E)/(1+K)` as an integer ratio. **Verdict by integer `E`.**

Under H0 `T` sits at the permutation null centred on the `1/m` floor (permutation uses the OBSERVED
marginal, absorbing any canonical-rep skew). Under H1 `T` exceeds it.

**Secondary diagnostic (NON-verdict, inherited):** marginal-bias readout of `f_ell(Q_d)` vs uniform-point
expectation — reported for interpretation, CANNOT trigger a verdict (a marginal in `f` independent of `d`
is a property of `S`'s image, not a `d`-leak).

---

## 4. CONTROLS (inherited, WITH the mandated matched-control correction)

### (i) COLLAPSE NULL — full-pipeline shuffle (THE load-bearing false-positive control)
Permute `Q_d ↔ d` across the sample BEFORE computing the target, run the ENTIRE
train/test/decoder/permutation pipeline. Required: recovery at floor (no significant `E`) for all `f∈F_new`,
`m`. Spurious significance here ⇒ pipeline miscalibrated → fix before trusting any positive.

### (ii) FIRING PLANT — positive control calibrating power (inherited)
`f_plant(Q_d) := (d mod m)` with each label independently corrupted (frozen-PRNG uniform) with probability
`(1−π)`; corruption threshold precomputed as an integer (`u<⌊(1−π)·D⌋`, `π` a design constant). Sweep
`π ∈ {1, 1/2, 1/4, 1/8, 1/16, 0}`. MUST fire (`E=0`) for all `π` above the floor and MUST NOT fire at
`π=0`. Smallest reliably-detected `π` = achieved detection floor. **Plant not firing at achievable `N` ⇒
null uninformative — full stop.**

### (iii) MATCHED CONTROL — `S_closed` — **PREMISE CHECK ONLY** (parent-over-credit CORRECTED)
Same `p,E,G,d*`, replace `S` by the Galois-averaged preimage `S_closed` (sum the four preimages
`{w,−w,iw,−iw}` as a divisor, project to `A_new`); `Hom(E,A_new)=0` forces the `A_new`-projection trivial,
so `Q^closed_d` is `d`-independent. **CORRECTION (mandated):** for EVERY `ell`, `f_ell(S_closed)` is a
CONSTANT (d-independent) label — `S_closed` zeroes the whole `A_new` part, so `[|A_new|/ell]·anew_part(Q^closed_d)`
is one fixed torsion point for all `d`. A constant feature CANNOT leak. Therefore `S_closed` at floor is a
**PREMISE VERIFICATION** (confirms `S_closed` really is `d`-independent, as `Hom(E,A_new)=0` predicts) and
is **NOT an independent FP control** for these torsion invariants. It does not gate the verdict. (The
parent over-credited it as a matched FP control; it is corrected to a premise check here.)

**OWED — a stronger, d-DEPENDENT, A_new-structure-free matched control.** The proper matched null would
reproduce every structure of `Q_d` EXCEPT the `A_new`-torsion structure under test, while remaining
`d`-dependent. Two candidates and their status:
- The homomorphic sibling `R_d = [d]·H`, `H` a fixed full-order point of `A_new(F_p)`: this is `d`-dependent
  and `A_new`-structured, but `[|A_new|/ell]·R_d = (d mod ell)·(ell-generator)` reads `d mod ell` EXACTLY
  (Pohlig-Hellman). It is therefore a TAUTOLOGICAL leak that MUST fire — it belongs to the PLANT family,
  not the matched-null family. (It is a useful *second plant*: a channel that must fire because the map is
  homomorphic; `S`'s non-homomorphy is exactly the property whose leak we test.)
- A non-homomorphic "non-closed 4th-root" map into a DIFFERENT supersingular abelian surface with CM by a
  different field (a sibling cover) — same construction, different torsion arithmetic — so that a leak there
  would indicate a construction artifact rather than `A_new`-specific structure. **No such sibling model is
  on disk; marked OWED (frame; a self-audit cannot discharge it per CLAUDE.md §2a).**
- **If no such control can be constructed, Outcome A for these torsion invariants rests on COLLAPSE +
  replication (≥2 powered primes) + out-of-sample** — because `S_closed` cannot discriminate them either
  (it zeroes the whole `A_new` part). This is stated up front so the reduced control set cannot be reframed
  after the numbers land.

---

## 5. POWER (inherited model; NEW per-ell aggregation and an alphabet-size caveat)

Inherited: R1 reaches `N ≈ nE/6` orbit reps; at powered scale `N_test ≈ 490` and the PLANT fires to
`π = 1/8` (not reliably 1/16) — this is the achieved detection floor. Detection floor for `d mod m`
recovery depends on `m` and `N_test`, NOT on `ell` (the null is the permutation of `d mod m` labels):

| m | floor 1/m | N_test=490 → δ_min (p<0.01) | ≈ bits floor (N_test=490) |
|---|-----------|-----------------------------|---------------------------|
| 2 | 0.500     | 0.058                       | ~0.010 bit                |
| 5 | 0.200     | 0.046                       | ~0.0076 bit               |
| 7 | 0.143     | 0.041                       | ~0.0066 bit               |
| 11| 0.091     | 0.033                       | ~0.0055 bit               |
| 13| 0.077     | 0.031                       | ~0.0051 bit               |

**Powered verdict defined only on `N_test ≥ ~490` at ≥2 primes** — inherited bar.

**NEW alphabet-size power caveat (must be stated).** `f_ell` has alphabet size up to `ell²` (or `ell` if the
canonical id is taken mod the torsion-order line); the MAP decoder must estimate `d mod m` per feature-value.
At `N_train ≈ 490`, an alphabet near or above `N_train` (large `ell`, e.g. `ell=97 → ell²≈9409` cells)
leaves ≪1 sample per cell, so the decoder cannot generalize and power DEGRADES toward the floor regardless
of any true leak. To keep every `f_ell` powered, the canonical id is read as the **2-coordinate `(a,b)∈(Z/ell)²`
and the verdict statistic is run on EACH coordinate separately (alphabet `ell ≤ 97`) AND on the paired label**;
for `ell ≥ 23` the single-coordinate alphabet (`≤97`) still gives ≥5 samples/cell at `N_train≈490`, workable;
the full `ell²` paired label is REPORTED but flagged low-power for `ell ≥ 23`. The plant (alphabet = `m ≤ 13`)
calibrates the true achievable floor per prime and is the gate. `f_CRT` inherits the same caveat and is
run coordinate-wise as well.

**Per-ell ladder (populated; confirmed).** Because `ELL(p)` varies by prime, a like-for-like replication of a
specific `f_ell` requires ≥2 powered primes that BOTH carry that `ell`. The candidate ladder (primes
`p ≡ 7 mod 12`, `p ≥ 5000`, `ell | p²+p+1`; nE-prime / j=0-curve existence checked at run) is non-empty for
every candidate `ell`:

| ell | smallest powered-scale primes p (p≡7 mod12, p≥5000, ell\|p²+p+1) |
|-----|------------------------------------------------------------------|
| 7   | 5023, 5107, 5119 |
| 13  | 5443, 5827, 6067 |
| 19  | 5023, 5179, 5407 |
| 31  | 5419, 5647, 5791 |
| 37  | 5227, 6427, 6871 |
| 43  | 6271, 8563, 9883 |
| 61  | 5503, 5659, 6967 |
| 67  | 5791, 6067, 6871 |
| 73  | 6067, 8167, 9043 |
| 79  | 5743, 6343, 6691 |
| 97  | 11119, 11287, 12451 |

**Frozen per-ell selection rule:** for each `ell ∈ ELL(L_MAX)`, the two powered primes are the two SMALLEST
`p ≡ 7 mod 12` with `ell | p²+p+1`, a prime-order `j=0` curve, and `N_test ≥ 490`; extend the search upward
until two qualify. **The parent's own powered primes do NOT suffice for the new menu:** at p=5827 only
`ell=13` is active (unreplicated there); at p=5839 `ELL(p)=∅` (|A_new|=3·11366587) — the new menu is EMPTY.
So the new menu mandates its own ladder above.

---

## 6. SCOPE (banner — governs every number this run emits; inherited)

SMALL/MID-`p` STRUCTURAL test of whether the covariant `S` carries `d`-information beyond the orbit label,
over the NEW multi-prime torsion menu `F_new` and moduli `M(n)`, on the per-ell ladder. **NO claim at
`p ≈ 2²⁵⁶`.** For secp, `ord_n(p) = (n−1)/6 ≈ 254 bits`; the pairing/MOV second hop is PROVED dead as an
attack (Corollary C). This spec reads cheap `O(ell²)` torsion coordinates directly and never proposes an
MOV/pairing dlog recovery. A find here is a LEVER CANDIDATE, not an attack, needing a separate dlog-free
exploitation argument this spec does not supply.

---

## 7. FALSIFICATION / DECISION RULE (pre-committed both ways; neither reachable by reframing)

**Preconditions for ANY verdict at a prime** (else UNINFORMATIVE at that scope; owed larger `N`/better
realization; NOT a closure and NOT a find):
- FIRING PLANT fired at `π ≥ π_floor` on ≥2 powered primes (power confirmed), AND
- COLLAPSE NULL at floor on all powered primes (FP rate calibrated).
- MATCHED `S_closed` at floor is a PREMISE CHECK (confirms `S_closed` d-independence); it is **NOT gating**
  for these invariants (correction, §4(iii)).

**OUTCOME A — LEVER LIVES.** On ≥2 distinct POWERED primes that BOTH carry the same `ell` (`N_test ≥ 490`),
∃ `f ∈ {f_ell, f_CRT}`, `m ∈ M(n)` with out-of-sample recovery `E=0` at `K=9999` (`p<1e-4`) AND collapse at
floor at that `(p,f,m)`.
→ CONCLUSION: "A cheap DLP-free multi-prime torsion label `f_ell` (or the CRT tuple) of `Q_d` carries
first-order partial `d`-information (`d mod m`) beyond the orbit label, at scope [ladder reached]. Lever
lives." Report `(f_ell or f_CRT, m, recovery rate, bits, prime, N_test)` — each WITH its prime (SCOPE) and
`N_test` floor (POWER). NEXT PROBE (named now): does recovery compose across `m` via CRT toward a
search-space reduction; which coordinate `(a,b)` of `A_new[ell]` the leak lives in; push `ell` and the
ladder higher; build the OWED d-dependent A_new-structure-free control to certify A_new-specificity.

**OUTCOME B — NO INFORMATION (bounded closure at the counter-prior's bar).** Preconditions met AND across
all qualifying powered primes, ALL `f ∈ F_new` (every `f_ell`, `3 < ell ≤ L_MAX`, coordinate-wise; and
`f_CRT`), ALL `m ∈ M(n)`, every out-of-sample recovery sits within the null band (no `E=0`).
→ CLOSURE, graded at the PROVED bar per the counter-prior:
  - **OBJECT** = { multi-prime small-torsion labels `f_ell`, `3 < ell ≤ L_MAX=100`, and the joint CRT tuple
    `f_CRT`, of `Q_d=S([d]G) ∈ A_new(F_p)` }. (ell=3 is separately closed by the parent; the F_{p³} PAIRING
    invariants f1–f4 are NOT this object — separate probe.)
  - **CLASS closed** = first-order out-of-sample MAP recovery of `d mod m`, `m ∈ M(n)`, from these labels.
  - **POWER** = achieved plant floor `≈ π = 1/8` at `N_test ≈ 490` per prime (leaks below `π=1/8` NOT
    excluded; large-`ell` paired labels low-power per §5).
  - **SCOPE** = the per-ell powered ladder reached, `p ≡ 7 mod 12`, prime-order `j=0` curves.
  - **EXPLICITLY NOT CLOSED** (a bound is a size, not "no structure"): the **F_{p³} PAIRING invariants
    f1–f4** (the joint-structure channel — the named next probe); higher-order / joint distinguishers
    beyond `f_CRT`; leaks below the `π=1/8` plant floor; the LARGE prime factor(s) of `|A_new|` with
    `ell > L_MAX` (left unprobed by cost — §8(b)); anything at `p ≈ 2²⁵⁶`. If `d`-information lives in a
    subspace/joint statistic this design does not project onto (a pairing coordinate, or the large-`ell`
    torsion), Outcome B returns "no information" while structure persists there — the null is bounded to
    `F_new` and first-order, and the pairing invariants f1–f4 are the pre-committed NEXT PROBE even under B.

**Frame the negative as banked progress that NARROWS the target** (the multi-prime cheap-torsion channels
are then bounded, sharpening the live A_new question onto the pairing invariants f1–f4) — NOT a declared
null on A_new, which stays OPEN.

**Anti-reframe.** Outcome B cannot be upgraded to A by adding an `ell`/`m` post hoc (both frozen; L_MAX
frozen). Outcome A cannot be manufactured by a lucky `(ell,m)`: significance requires surviving collapse
AND replicating on ≥2 primes that both carry that `ell` AND being out-of-sample under a frozen decoder.

---

## 8. EXACTNESS / FLOAT RULE (inherited verbatim)

All signal-path arithmetic exact: `A_new(F_p)` group law and `[·]`-scalar-mult on integer tuples mod `p`;
`ell`-torsion enumeration and `canonical_id` lookup are integer; MAP decoder, counts, and permutation
exceedance `E` are integer; p-values are the integer ratio `(1+E)/(1+K)`. **No float decides any verdict.**
Any effect size printed as a float is DISPLAY-ONLY, ranked against the integer permutation null (the
CLAUDE.md analytic-size carve-out: no key in the path). `check_no_float.sh` MUST pass on the run script
before execution.

---

## SELF-AUDIT — sections I could NOT fully cover (absence from this list is NOT clearance)

**(a) ell VARIES ACROSS PRIMES — the "same invariant" is not literally identical across the ladder
(FRAME + MECHANICAL). ADDRESSED, with a residual frame gap.** Because `|A_new|=p²+p+1` factors differently
per prime, `ELL(p)` differs, so `f_ell` at prime `p₁` and `f_ell` at prime `p₂` are the "same invariant"
ONLY when both primes carry that `ell`. The verdict AGGREGATES PER ELL: an `f_ell` verdict (A or B) uses the
two frozen powered primes that BOTH carry that specific `ell` (§5 ladder), so replication is genuinely
like-for-like at the level of a single `ell`. Consequence made explicit: the parent's own powered primes
p=5827 (only `ell=13` active) and p=5839 (`ELL=∅`) CANNOT replicate any new `f_ell` between them — the new
menu needs its own ladder, frozen in §5. RESIDUAL FRAME GAP: `f_CRT` is NOT the same alphabet across primes
(its ell-set `ELL(p)` differs), so `f_CRT` "replication" means only "the joint small-torsion coordinate
recovers `d mod m` on ≥2 primes," not identical-alphabet replication — a LOOSER claim, flagged; a `f_CRT`
Outcome A must additionally report the differing ell-sets of the two primes. Isolation-owed per §2a.

**(b) L_MAX=100 LEAVES A LARGE PRIME FACTOR UNPROBED (MECHANICAL, disclosed).** By cost, `L_MAX=100` caps
the probe at `O(ell²) ≤ 9409`. The bulk of `|A_new|` is a large prime (or large-prime product) with
`ell > L_MAX`, and it is UNPROBED: e.g. at p=5827 the factors 433 and 2011 (`|A_new|=3·13·433·2011`), at
p=5839 the whole non-3 part 11366587 (`|A_new|=3·11366587`). Reading the large-`ell` torsion label costs
`O(ell)`–`O(ell²)` and for `ell ~ 10⁶⁺` that IS the `A_new`/`F_{p³}` dlog — forbidden and dead at scale
(Corollary C). The Outcome-B closure is therefore EXPLICITLY bounded away from the large-factor torsion; it
is named as NOT CLOSED in §7. A leak living in the large-`ell` torsion would return Outcome B here while
persisting there.

**(c) MATCHED-CONTROL GAP (FRAME; self-audit CANNOT discharge, per §2a).** `S_closed` is a PREMISE CHECK
only for these invariants (constant feature; §4(iii)), correcting the parent's over-credit. No d-dependent,
A_new-structure-free matched control is on disk (the homomorphic sibling is a tautological plant, not a
null). Outcome A therefore rests on COLLAPSE + replication + out-of-sample, and its `A_new`-SPECIFICITY (vs
a generic construction artifact of the non-closed-4th-root map) is NOT certified by a matched null — the
owed sibling-cover control is the mechanism, and it is isolation-owed. Stated up front so the reduced
control set cannot be reframed post hoc.

**(d) REALIZABILITY OF `f_ell` AT SCALE (MECHANICAL, owed with artifact).** R1 (the parent's engine) is
shown to run the group law and `ell₀=3` label to `p≈6000`. The `A_new[ell]` enumeration + `canonical_id`
lookup for `ell up to 97` (`ell²≈9409` points, built once per prime) is asserted `O(ell²)` and cheap but is
not yet demonstrated; smoke-check at one ladder prime (e.g. p=5443, ell=13) before counting a prime as
powered. Discharge with the run artifact.

**(e) nE-PRIME / j=0-CURVE EXISTENCE PER LADDER PRIME (MECHANICAL, owed).** The §5 ladder lists primes `p`
with `ell | p²+p+1`; each still needs the smallest-`B>0` `j=0` curve to have PRIME order `nE` and
`N_test ≥ 490`. Generic (~1/ln nE of twists prime) but must be verified per prime at run; if a listed `p`
fails, take the next carrying that `ell`. Mechanical.

**(f) INVARIANT-MENU COMPLETENESS / SUBSPACE GUARD (FRAME, disclosed).** `F_new` is finite, first-order,
cheap-torsion. If `d`-information lives in the pairing coordinates (f1–f4), in a higher-order/joint
statistic beyond `f_CRT`, or in the large-`ell` torsion (b), Outcome B returns "no information" while the
structure persists unprojected. The Outcome-B null is bounded to `F_new` and first-order; f1–f4 are the
named next probe even under B.

**Layer tags per CLAUDE.md §2a:** (b),(d),(e) are MECHANICAL (a run/smoke-check discharges them, with the
artifact). (a residual), (c), (f) are FRAME — isolation is the mechanism; a self-audit cannot clear them;
disclosed as owed/open.
