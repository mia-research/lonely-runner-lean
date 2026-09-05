# ANALYSIS — the `A_new` bridge, gated at its target: `n`-visibility and the `k`-tradeoff (v2)

*2026-08-06. Supersedes `ANALYSIS_anew_bridge_n_visibility_v1.md`, which stays on disk. v2 folds in the
`experiment-designer` audit of the v1 runs and the `citation-verifier` pass on §7 — both gates were
recorded as **owed** in v1 §9 and have now been run. **Every correction below was recomputed from
scratch before being accepted** (`anew_n_visibility_v2.py` / `.log`); the audit is a subagent's report,
not a verdict. Artifacts: `anew_n_visibility_v1.py`/`v2.py` + logs, `anew_d1_forced_check_v1.py` + log.
Exact integers throughout, no float in any path. No leakage claim, no ECDLP claim, no security claim.*

> **What changed from v1.** (1) The bound was **not minimal and is stronger than v1 reported** — at the
> secp branch the bridge gives **no gain at all**, where v1 claimed a factor of 3. (2) The closure class
> in v1 §5 was **over-scoped**: the phrase "including non-homomorphic constructions" inverts the one
> hypothesis the argument needs. Restated in §5, with two channels v1 did not carve out. (3) v1's firing
> controls were weak (one was **forced**) and never called the headline function; replaced. (4) `n` and
> the factors of `n−1` are now **proved** prime by recursive Pocklington certificate, not sampled by
> BPSW. (5) §7's two references are now `[CITED — verified]` with primary sources.

---

## §0 Where the proposal already sits in the record

Unchanged from v1. `A_new` supersingular at secp is `[PROVED, scale-free, curve-independent]`
(`RESULT_mu6_cohomology_supersingular_v2.md` §4); `k=3` was `[VERIFIED, 7 primes]` (M17);
`Hom(E,A_new)=0` is P13 `[PROVED]`; D1 and D2 are the open doors
(`RESULT_supersingular_cover_lever_v1.md` §4). Nothing here re-litigates them.

What this file adds is the gate the record never applied: **the MOV embedding-degree condition, applied
to the bridge's *target* rather than to `E`.**

---

## §1 The gate

Every transfer attack has two independent requirements; the record has only ever checked the first.

1. **A map exists.** Where `Hom(E,A_new)=0` bites, and what D1/D2 propose to get around.
2. **The target group can hold the answer** — it must contain an element of order `n`. For MOV this is
   the familiar `n | p^k − 1`.

Requirement 2 is a statement about **group order**, so Tate is not its mechanism. `n` is prime, so:

- a nonzero group homomorphism `ℤ/n → A_new(F_{p^j})` exists **iff** `n | #A_new(F_{p^j})`;
- if `n ∤ #A_new(F_{p^j})` then for any `Q` of order `M` we have `gcd(n,M)=1`, so any assignment
  `d ↦ [αd+β]Q` **that is well defined on `d ∈ ℤ/n`** forces `M | α`, killing the `d`-dependence.

**The italicised hypothesis is load-bearing and v1 stated it in §1 but then dropped it in §5.** See §5.

---

## §2 The theorem

**Inputs**, both `[PROVED]` on the record: `A_new/F_p` supersingular at secp; `b₁ = 0`.

So `P(T) = T⁴ + b₂T² + p²`. With `u = α/√p`, supersingularity makes every `u` a root of unity and
`u⁴ + mu² + 1 = 0`, `m = b₂/p`. Then `m` is rational and an elementary symmetric function of algebraic
integers, so `m ∈ ℤ`; the roots pair as `{v,−v,w,−w}` with `|v|=|w|=1`, so `m = −(v²+w²)` gives
`|m| ≤ 2`. **`m ∈ {−2,−1,0,1,2}` is derived, complete, and independent of which branch holds at secp.**
*(The audit notes `b₁=0` is itself forced for a supersingular surface over `F_p`, `p>16`: `Σαᵢ = √p·Σζᵢ
∈ ℤ` with `|Σζᵢ| ≤ 4` forces `Σζᵢ = 0`. Not relied on here — the record's `μ₄` derivation is used.)*

| `m` | `−2` | `−1` | `0` | `1` | `2` |
|---|---|---|---|---|---|
| `#A_new(F_p) = 1+mp+p²` | `(p−1)²` | `p²−p+1` | `p²+1` | `p²+p+1` | `(p+1)²` |
| minimal even `e` with `α^e = p^{e/2}` | 2 | 12 | 8 | 6 | 4 |
| `k := e/2` | 1 | 6 | 4 | 3 | 2 |

`e` verified exactly by squarefree-part polynomial division at the secp `p`; the audit re-checked
minimality over **all** even `e ≤ 200`, confirming the search list contains the true minimum for every
admissible `m`.

> **Theorem.** If `n | #A_new(F_{p^j})` then `ord_n(p) | k·j`.
>
> *Proof.* `N_j := #A_new(F_{p^j}) = ∏_i(1−α_i^j) ∈ ℤ`. Let `𝔫` be a prime of the splitting field above
> `n`. From `n | N_j`, some factor lies in `𝔫`, so `α_i^j ≡ 1 (mod 𝔫)` for some `i`. Raise to the `e`-th
> power and use `α_i^e = p^{e/2}`: `p^{kj} ≡ 1 (mod 𝔫)`. Since `p^{kj}−1 ∈ ℤ ∩ 𝔫 = nℤ` (using `n`
> prime), `n | p^{kj}−1`, i.e. `ord_n(p) | k·j`. ∎

**Corollary A (`j=1`, applied to `ℓ | #A_new(F_p)`): `ord_ℓ(p) | k`** — the `k` in the table *is*
`A_new`'s internal MOV embedding degree. At `m=1` this gives `k=3`, so **M17's `k=3` at 7/7 primes is
forced and carries no independent weight.**

**Corollary B (at secp) — corrected, and stronger than v1.** `ord_n(p) = (n−1)/6`, 254 bits, with `n`
and every prime factor of `n−1` **proved** prime by recursive Pocklington certificate (v1 used sympy's
BPSW, a probable-prime test — and the error direction matters: a composite "prime" factor lets the
order-peeling return a *multiple* of the true order, overstating the bound). `2⁵ ‖ ord_n(p)` and
`3 ∤ ord_n(p)`.

v1 reported `j ≥ ⌈ord/k⌉`. The exact solution set of `ord | k·j` is `j ∈ (ord/gcd(ord,k))·ℤ`:

| `m` | `k` | `gcd(ord,k)` | v1 said | **sharp** | gain vs `E`'s own MOV |
|---|---|---|---|---|---|
| `−2` | 1 | 1 | 254 b | 254 b | **factor 1** |
| `−1` | 6 | 2 | 251 b | **253 b** | factor 2 |
| `0` | 4 | 4 | 252 b | 252 b | factor 4 |
| **`1`** (secp branch) | 3 | 1 | 252 b | **254 b** | **factor 1** |
| `2` | 2 | 2 | 253 b | 253 b | factor 2 |

**Best branch for an attacker is `m=0` at 252 bits (factor 4), not 251 (factor 6). At the secp branch
`m=1` the gain is factor 1 — the bridge buys nothing whatsoever over `E`'s own MOV degree.** And `j`
must be a **multiple** of the step, not merely exceed it: permitted `j` have density `≤ 2^{−251}`.
v1's numbers were all valid lower bounds; v1 understated its own result.

---

## §3 What the theorem says, in one sentence

**The same `k` appears twice with opposite signs.** `A_new`'s DLP is easy *because* `k` is small (its
order divides `p^k−1`); the bridge is unusable *because* `k` is small (`ord_n(p) | k·j`). A
supersingular surface with `k` large enough to reach would have an internal DLP as hard as `E`'s. No
choice of cover, cubic, or branch escapes it — the theorem quantifies over all five admissible `m`.

---

## §4 The exact runs

**Run 1 — `anew_n_visibility_v1.py`/`.log`.** Pre-registration (statistic, outcome map, controls,
instrument checks) sits in the module docstring, written before the run. `gcd(n, #A_new(F_{p^j})) = 1`
for all five `m`, all `j = 1..64`, at the true secp `p`, `n`.

> **This 320-cell sweep is entailed by the theorem and is an instrument check on the code, with zero
> independent evidential weight.** The script and v1 §4 both say so; the audit's finding is that the
> qualifier must travel with the claim wherever it is quoted. It does so here.

- **Instrument checks:** `I1` `N₁ = P(1)` ✅. `I2` closed forms ✅ — *after failing on first execution,
  on my expected value rather than the computation (for `m=±2` the roots are repeated, so even `j` gives
  `(p^{j/2}−1)⁴`). The same repeated-root fact then invalidated a matrix-level version of the §2 step
  (`M^e = p^{e/2}I` is false for `m=±2`); redone on `rad(P)`, where it holds for all five `m`.*
  The audit found `I2` covers `j>1` **only for `m=−2`** and closed the gap externally by recomputing
  every cell through an independent algorithm (`Res_T(P(T), 1−T^j)` over `ℚ`): 305 cells, all match.
  It also validated the Bareiss determinant against `sympy` on 400 random zero-pivot-heavy matrices.
- **Firing controls — v1's were weak; replaced in v2.** v1's `C2` planted the divisor `3`, which is
  **forced**: `p ≡ 1 mod 3` makes `3 | 1+p+p²` identically, so it could not fail. And neither v1 control
  called `sweep()`, the function that produced the headline. **v2's replacement plants a genuine large
  prime — `#E(F_p)` itself — and runs the headline function:**

| `p` | `ℓ = #E(F_p)` | `m` | hits at `j` | `ord_ℓ(p)` | min permitted `j` | |
|---|---|---|---|---|---|---|
| 43 | 31 | −1 | 5, 10, 15, 20 | 30 | 5 | attained |
| 43 | 31 | 1 | 20 | 30 | 10 | permitted, not attained |
| 43 | 31 | 2 | 15, 30 | 30 | 15 | attained |
| 67 | 79 | −2 | 13, 26 | 13 | 13 | attained |
| 79 | 67 | −1 | 11, 22 | 66 | 11 | attained |

  The detector fires (5 cells), **every hit is a multiple of the theorem's bound** (asserted in code),
  and the bound is attained in 4 of 5 cells. The 5th shows the condition is **necessary, not
  sufficient** — `j=10` is permitted at `p=43, m=1` but the first actual hit is `j=20`. v2 states this;
  a stronger reading ("the first hit lands exactly on the bound") would be wrong.

**Run 2 — `anew_d1_forced_check_v1.py`/`.log`.** Exact brute force at M18's own primes:

| `p` | `#E(F_p)` | `m` | `#A_new(F_p)` | `gcd` |
|---|---|---|---|---|
| 43 | 31 (prime) | 1 | 1893 | **1** |
| 67 | 79 (prime) | 1 | 4557 | **1** |
| 79 | 67 (prime) | 1 | 6321 | **1** |

The record's own T1 (`#C(F_p)=p+1−a_p`) reproduces 3/3, and `assert S % p == 0` is a real `b₂ = m·p`
check that would fail on a ~1-in-`p` coincidence if the supersingular model were wrong. The audit
extended the result: `gcd(#E(F_p), #A_new(F_{p^j})) = 1` for **all `j ≤ 12`** at all three primes.

> **Consequence for M18 — corrected scope.** No nonzero **additive** map `⟨G⟩ → A_new(F_{p^j})`,
> `j ≤ 12`, exists at those primes. So M18's `0/666` **additive** measurement is forced and carries zero
> information about other constructions. **v1 also imported M18's "`0/339` affine" into the same
> sentence; that half is forced only under the reading affine = additive + translation**, and is not
> established by this run otherwise. Three premises about what M18 measured are inherited and
> uncheckable here: that its target was `A_new` rather than `Jac(C) = E × A_new` (whose `E` factor
> trivially carries `ℓ`), that its domain was the full `E(F_p)`, and that the 666 candidates were
> nonzero (the zero map is additive).

---

## §5 Closure grade — corrected, and narrower than v1

Per `feedback_closure_grade_2026_07_28`. **v1's CLASS row said "including non-homomorphic
constructions". That is wrong as written and is corrected here** — the point-map may be
non-homomorphic; the *log-map* may not.

| | |
|---|---|
| **OBJECT** | `A_new(F_{p^j})` as the target group of a transfer from `⟨G⟩ ⊂ E(F_p)`, at the true secp `p`, `n`. |
| **CLASS closed** | Any transfer whose `A_new`-log-value is an affine function of `d` **that is well defined modulo `n`** — equivalently, where recovery of `d mod n` runs through a single cyclic channel carrying a `ℤ/n`-action. The map on *points* may be non-homomorphic; the map on *logs* may not. Covers Route 2 and D1's additive arm. |
| **POWER** | Deterministic, so power is exact and two-sided: **power 1** against the class above; **power 0** against both classes in §6.1–6.2 — the statistic is a `gcd` with `n`, so by construction it sees only the `n`-part. |
| **SCOPE** | `j` must be a multiple of `ord_n(p)/gcd(ord_n(p),k) ≥ 2^{251}`; the useful range is empty. Rests on: `A_new` supersingular **at secp** with `b₁=0` — a **cited premise, not verified in either run** (in-run support exists only at `p ∈ {43,67,79}`). If `A_new` at secp were ordinary or mixed, the gate is void. |

---

## §6 What this does **NOT** close

1. **A set-injective encoding that does not factor through `ℤ/n`.** `d` is a specific integer in
   `[1,n)`; a non-homomorphic construction need not factor through `ℤ/n` at all. An injective
   `d ↦ Q(d)` inside a cyclic `⟨R⟩` with `M = ord(R) ≥ n` recovers `d` and needs only
   `#A_new(F_{p^j}) ≥ n` — already true at `j=1`, where `#A_new ≈ p² ≈ n²`. **Against this class the
   gate has power 0.** This is D1's non-affine arm, and it is the sharpest statement of it yet.
2. **Partial recovery + CRT.** `L(d) = d mod M` with `gcd(M,n)=1` leaks `d mod M` and is invisible to a
   `gcd` with `n`. Collecting `d mod M_j` across many `j` with `∏M_j ≳ n` is **untested, power 0**.
   Neither run bounds the multiplicative structure of `#A_new(F_{p^j})`. *(New in v2 — v1 had no such
   carve-out.)*
3. **D2, the Lang-torsor twist bridge.** A statement about the **values** of `V(a)` under the twist, not
   a transfer of a point into a group. The gate does not apply. `[OPEN]`, unchanged, and the stronger
   of the two doors.
4. **Route 3 / N4, the cover-family index calculus.** Does not need `n` visible in `A_new`. `[OPEN]`.

---

## §7 The two proposed "glues" — `citation-verifier` result

Both were `[ASSERTED — citation-verifier owed]` in v1. The gate has run; **neither contains a
fabricated landmark**, and both descriptions hold, with one nomenclature caveat.

- **"Fake GLV" — `[CITED — verified]`.** Primary source: **Eagen, El Housni, Masson, Piellard, *Fast
  elliptic curve scalar multiplications in SN(T)ARK circuits*, IACR ePrint 2025/933 = LATINCRYPT 2025**
  (`10.1007/978-3-032-06754-8_4`). It replaces the in-circuit check `[k]P = Q` by `[x]P − [z]Q = 0_E`
  with `x,z ≈ 1.16√r` from lattice reduction — or, per the abstract, a half-extended Euclidean
  algorithm in a ring of integers — on `x + λy − k(z+λt) ≡ 0 mod r`. Its own Note 2: *"In 2-dimensional
  GLV, we need an efficient endomorphism. In our case, we don't."* The hinted output `Q` plays the role
  `φ(P)` plays in GLV. Effect: 22–53% proving-time speedup. **All points lie on one curve `E`; where
  `ψ` appears it is `E`'s own GLV endomorphism. No second abelian variety occurs anywhere in the
  paper.** ⚠ **Nomenclature caveat:** the string "fake" does not appear in that paper; the name lives
  only in an Ethereum Research post (El Housni, 2024-09-09) and in gnark's `scalarMulFakeGLV`. Cite
  2025/933, not the name.
- **Endomorphism simulation inside SNARKs — split grade.** The descriptive half is `[CITED —
  verified]`: in Masson–Sanso–Zhang (ePrint 2021/1152) `ψ = √−2 ∈ O₋₈` is a genuine algebraic
  endomorphism built by Vélu, and the circuit spends **6 R1CS constraints** expressing it; in Curve
  Trees (USENIX Security '23 §2.1.3) and Guillevic–Masson (ePrint 2024/1737) the "crossing" between two
  curves is a **field-cardinality match** plus reinterpreting a point's coordinates as a pair of
  scalars, which those sources state as such — not a morphism of varieties. The negative half —
  *cannot manufacture an element of `Hom(E, A_new)`* — is **`[ASSERTED, scope = P13]`**: no source
  states it, and it rests on P13 plus a failed literature search, not on a quoted theorem. Curve Trees
  records only the scoped null *"No known attacks make use of this additional structure"* (2023).
- **No primary source found** for: any peer-reviewed occurrence of "fake GLV"; any published
  construction transporting a DLP instance between abelian varieties via a fake-GLV or in-circuit
  endomorphism technique; any SNARK/circuit technique used as an attack on a curve's group. Recorded
  as failed searches, not as absences.

**Provenance note retained from v1:** the proposal's phrasing tracks the four user-supplied survey
reports, and the placement map already quarantines fabricated landmarks from that batch. The `A_new`
mathematics is ours; these two references were the survey-sourced parts, and they have now been
verified.

---

## §8 Next probes (find, not verdict)

1. **D1's non-affine arm, properly instrumented** — §6.1 is now its precise statement. The forced-null
   finding means the arm needs a prime where the null *can* fail: pick `p` with
   `ℓ | gcd(#E(F_p), #A_new(F_{p^j}))`. **§4's replacement control exhibits five such cells** (e.g.
   `p=67, ℓ=79, m=−2, j=13`). Only there does a measured `0/N` carry information. This is the firing
   control the D1 measurement never had.
2. **§6.2, the CRT channel** — a genuinely untested direction that neither run touches: does
   `#A_new(F_{p^j})` carry recoverable `d mod M` for `gcd(M,n)=1`, and do the `M_j` accumulate?
3. **D2 unchanged**, and the higher-value door.
4. **Regrade M17 and M18** in the master as forced (Corollary A; §4), with M18's correction restricted
   to its additive half. Promotion into a consolidated document requires `compile-diff` first — not run
   here, and this file is not a promotion.

---

## §9 Gates

- **`experiment-designer`: RUN** (audit of the completed v1 runs against their spec). Findings above.
  Load-bearing corrections — sharp bound, replacement control, Pocklington certificates — were each
  **recomputed from scratch** (`anew_n_visibility_v2.py`/`.log`) before acceptance; two of the agent's
  own framings were themselves corrected in doing so (its Pocklington claim was reproduced only after
  replacing trial-division factoring; its "each first hit lands exactly on the bound" is false in 1 of
  5 cells, so the condition is necessary, not sufficient).
- **`citation-verifier`: RUN.** §7. Two grades moved up on verified primary sources; one negative clause
  stays `[ASSERTED, scope = P13]`.
- **`compile-diff`:** still not applicable — nothing promoted into a consolidated document here.
- **Latent defect logged** (`anew_d1_forced_check_v1.py:118-120`): the verdict keys on
  `max(prime factors of #E)`. Harmless here — `#E(F_p)` is prime at all three primes — but incomplete
  if reused where `#E` is composite, since forcing requires *every* relevant `ℓ` to miss `#A_new`.
