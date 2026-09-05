# ANALYSIS — the `A_new` bridge, gated at its target: `n`-visibility and the `k`-tradeoff

*2026-08-06. Object: the proposed transfer `E → A_new` (record routes **D1**, **D2**, §VII.3 Route 2).
New content: one theorem plus two exact runs, `anew_n_visibility_v1.py` / `.log` and
`anew_d1_forced_check_v1.py` / `.log`. Exact integers throughout; no float in any path. No leakage
claim, no ECDLP claim, no security claim.*

---

## §0 Where the proposal already sits in the record

The four components of the proposal are each already on the ledger, at these grades. Nothing below
re-litigates them.

| component | record status |
|---|---|
| `A_new` (the `χ₄`-isotypic / "new" part of `Jac(C)`, `C : w⁴ = f(x)`, `dim 2`) is **supersingular at secp** | `[PROVED, scale-free, curve-independent]` — `RESULT_mu6_cohomology_supersingular_v2.md` §4. Stronger than "suggests": it holds for **every** `p ≡ 3 mod 4` and every separable cubic. Independent adversarial pass still pending there. |
| `A_new`'s **internal** DLP is easy, MOV embedding degree `k = 3` | `[VERIFIED, 7 primes]` — M17. §3 below shows this is **forced**, not evidence. |
| `Hom(E, A_new) = 0` at secp | `[PROVED]` — P13, via Tate + disjoint Newton slopes `{0,1}` vs `{½,½}`. |
| the bottleneck is therefore the **transfer map**; **D1** (non-homomorphic lift `Q(P)=[P⁺−P⁻]`) and **D2** (Lang-torsor twist bridge) are the open doors | `[OPEN]` — `RESULT_supersingular_cover_lever_v1.md` §4; unchanged by this file. |

So the framing is right and matches the record. What follows adds the one gate the record never
applied: **the MOV embedding-degree condition, applied to the bridge's *target* rather than to `E`.**

---

## §1 The gate

Every transfer attack (MOV, Frey–Rück, GHS/Weil descent) has two independent requirements, and the
record has only ever checked the first:

1. **A map exists.** — this is where `Hom(E,A_new)=0` bites, and where D1/D2 propose to get around it.
2. **The target group can hold the answer.** — the target must contain an element of order `n`.
   For MOV this is the familiar `n | p^k − 1`.

Requirement 2 is **independent of how the map is built**. It is not an isogeny statement, so Tate is
irrelevant to it, and a non-homomorphic construction does not evade it — provided the recovery of `d`
runs through a discrete log in the target, which is the entire premise of the proposal (the point of
`A_new` is its easy DLP).

**Precise form.** `n` is prime. Let `Q ∈ A_new(F_{p^j})` have order `M`.

- A nonzero group homomorphism `⟨G⟩ ≅ ℤ/n → A_new(F_{p^j})` exists **iff** `n | #A_new(F_{p^j})`.
- More generally, if `n ∤ #A_new(F_{p^j})` then `gcd(n, M) = 1`, so any assignment `d ↦ [αd + β]Q`
  that is well defined on `d ∈ ℤ/n` forces `M | α`, i.e. the `d`-dependence vanishes identically.
  **Every affine-in-the-log transfer is constant.**

---

## §2 The theorem

**Inputs** (both from the record, both `[PROVED]` there): `A_new/F_p` is supersingular at secp; `b₁ = 0`
(the `μ₄`-eigenspace argument at `p ≡ 3 mod 4`, `RESULT_anew_identification_v1.md` §1).

So `P(T) = T⁴ + b₂T² + p²`. Put `u = α/√p`. Supersingularity means every `u` is a root of unity;
`P(√p·u)=0` gives `u⁴ + m u² + 1 = 0` with `m = b₂/p ∈ ℚ`. Since `m` is an elementary symmetric
function of algebraic integers it is an algebraic integer, hence `m ∈ ℤ`; and the roots pair as
`{v,−v,w,−w}` with `|v|=|w|=1`, so `m = −(v²+w²)` gives `|m| ≤ 2`. **Hence `m ∈ {−2,−1,0,1,2}`,
derived — not assumed, and not dependent on which branch holds at secp.**

For each admissible `m`, every root satisfies `α^{e} = p^{e/2}` for the `e` below (checked exactly at
the secp `p` by squarefree-part polynomial division, `anew_n_visibility_v1.log`):

| `m` | `−2` | `−1` | `0` | `1` | `2` |
|---|---|---|---|---|---|
| `#A_new(F_p) = 1+mp+p²` | `(p−1)²` | `p²−p+1` | `p²+1` | `p²+p+1` | `(p+1)²` |
| minimal even `e` with `α^e = p^{e/2}` | 2 | 12 | 8 | 6 | 4 |
| `k := e/2` | 1 | 6 | 4 | 3 | **2** |

> **Theorem.** If `n | #A_new(F_{p^j})` then `ord_n(p) | k·j`, hence
> **`j ≥ ord_n(p) / k`.**
>
> *Proof.* `N_j := #A_new(F_{p^j}) = ∏_i (1 − α_i^j) ∈ ℤ`. Let `𝔫` be a prime of the splitting field
> above `n`. From `n | N_j` some factor lies in `𝔫`, i.e. `α_i^j ≡ 1 (mod 𝔫)` for some `i`. Raising to
> the `e`-th power and using `α_i^e = p^{e/2}` exactly: `p^{kj} ≡ 1 (mod 𝔫)`. As `p^{kj} − 1 ∈ ℤ ∩ 𝔫 =
> nℤ`, we get `n | p^{kj} − 1`, i.e. `ord_n(p) | k·j`. ∎

**Corollary A (`j = 1`, applied to a prime `ℓ | #A_new(F_p)`): `ord_ℓ(p) | k`.** So the `k` in the
table *is* `A_new`'s internal MOV embedding degree. At the secp branch `m = 1` this gives `k = 3` —
**M17's `k=3` at 7/7 primes is forced by `m=1`, and carries no independent weight** (drill rule:
count only unforced hits).

**Corollary B (at secp).** `ord_n(p) = (n−1)/6`, a **254-bit** integer — the record's P7', re-verified
here from the factorisation of `n−1` (each large factor confirmed prime; `p^{ord} ≡ 1`, and minimality
checked by dividing out each prime of `n−1`). Therefore

| branch | bound on the first useful `j` |
|---|---|
| `m = −2` (`k=1`) | `j ≥ ord_n(p)` — **exactly `E`'s own MOV condition**, no gain at all |
| `m = 1` (the secp branch, `[CONDITIONAL on §2 of the m-law]`) | `j ≥ ord_n(p)/3` — **252 bits** |
| worst case over all five admissible `m` (`k ≤ 6`) | `j ≥ ord_n(p)/6` — **251 bits** |

---

## §3 What the theorem says, in one sentence

**The same `k` appears twice, with opposite signs.** `A_new`'s DLP is easy *because* `k` is small (its
order divides `p^k − 1`); and the bridge is useless *because* `k` is small (`j ≥ ord_n(p)/k`). The
product is pinned at `ord_n(p) = (n−1)/6` regardless of branch. A supersingular surface whose `k` were
large enough to make the bridge reachable would have an internal DLP as hard as `E`'s.

The easiness and the inaccessibility are **the same equation**, not two facts that happen to point the
same way. Consequently: **no choice of cover, cubic, or `m`-branch changes the conclusion** — the
theorem quantifies over all five admissible branches, and the best of them buys a factor of 6
(< 3 bits) against a 254-bit requirement.

---

## §4 The exact runs

**Run 1 — `anew_n_visibility_v1.py` / `.log`.** Pre-registration (statistic, outcome map, controls,
instrument checks) is written in the script header **above** the code, fixed before any number was
printed.

- `gcd(n, #A_new(F_{p^j})) = 1` for **all five `m`**, all `j = 1..64`, at the true secp `p` and `n`.
  `#A_new(F_{p^j}) = det(I − M^j)` via the companion matrix, Bareiss fraction-free determinant.
- **This sweep is FORCED by the theorem** and is therefore an instrument check on the code, **not**
  independent evidence for the bound. Recorded as forced.
- **Instrument checks:** `I1` `N₁ = P(1) = 1+mp+p²` ✅; `I2` closed forms `m=−2 → (p^j−1)²` (odd `j`) /
  `(p^{j/2}−1)⁴` (even `j`), `m=1 → p²+p+1` ✅. *`I2` failed on its first execution and the failure was
  mine, in the expected value, not the computation: for `m=±2` the roots are repeated, so even `j`
  gives `(p^{j/2}−1)⁴`. Logged because the check catching it is the only reason it was caught.* The
  same repeated-root fact then invalidated a matrix-level version of the §2 step (`M^e = p^{e/2}I` is
  false for `m=±2`, `M` not being semisimple); the theorem needs only the **eigenvalue** statement, so
  the check was redone on the squarefree part of `P`, where it passes for all five `m`.
- **Firing controls:** `C1` the same detector at small primes reports 80 genuine `gcd > 1` hits ✅;
  `C2` a planted true divisor of `#A_new(F_p)` at secp scale is detected ✅. The detector is not vacuous.

**Run 2 — `anew_d1_forced_check_v1.py` / `.log`.** Exact brute-force counts of `E` and `C` over `F_p`
and `F_{p²}` (`F_{p²} = F_p[t]/(t²+1)`, valid as `p ≡ 3 mod 4`), at M18's own primes:

| `p` | `#E(F_p)` | `m` | `#A_new(F_p)` | `gcd` |
|---|---|---|---|---|
| 43 | 31 (prime) | 1 | 1893 | **1** |
| 67 | 79 (prime) | 1 | 4557 | **1** |
| 79 | 67 (prime) | 1 | 6321 | **1** |

The record's own T1 (`#C(F_p) = p+1−a_p`) reproduces at all three — an independent check on this
point-counting code.

> **Consequence for M18.** At every one of the three primes where D1's lift was measured
> `0/666` additive, the group orders are **coprime**: no nonzero additive map `⟨G⟩ → A_new(F_p)` exists
> there at all. **M18's null is FORCED by order alone.** It is a correct measurement of a forced
> quantity, so it carries **zero** information about whether a *different* lift could be additive —
> which is a sharper statement of the scope caveat the record already attached to it
> (`RESULT_jacobi_closed_form_m_law_v4.md` A6(i): "one small prime, one lift construction, no torsion
> test"). The honest reading is that D1's additivity arm was never able to fire.

---

## §5 Closure grade — object, class, power, scope

Per `feedback_closure_grade_2026_07_28`, stated at the PROVED bar or not at all:

| | |
|---|---|
| **OBJECT** | `A_new(F_{p^j})` as the target group of a transfer from `⟨G⟩ ⊂ E(F_p)`, at the true secp `p`, `n`. |
| **CLASS closed** | Any transfer that recovers `d` via a **discrete-log computation in `A_new(F_{p^j})`** whose log-value is an affine function of `d` — *including non-homomorphic constructions*, since the gate is on group order, not on the map. Covers Route 2, and the affine arm of D1. |
| **POWER** | Exact. Nothing is estimated, so there is no detection floor and no sample size. The bound is a divisibility, not a bound on a statistic. |
| **SCOPE** | `j ≥ ord_n(p)/k ≥ 251 bits` — i.e. the useful range of `j` is empty, since the target field `F_{p^j}` would exceed `2^{2^{250}}`. Rests on: `A_new` supersingular at secp `[PROVED]`, `b₁=0` `[PROVED — UNREVIEWED]`, `ord_n(p)=(n−1)/6` `[VERIFIED, re-verified here]`. Inherits the pending independent pass on the first two. |

---

## §6 What this does **NOT** close — three doors, still open

1. **D1's non-affine arm.** A set map `ψ : ⟨G⟩ → A_new` whose `A_new`-log is *not* affine in `d` is
   untouched: the gate only forbids the structured encoding. The open question the record states —
   does `Q(P)` retain a coset, a bit-band, or a modular constraint on `d`? — is unaffected, and §4 now
   shows the existing measurement never addressed it. **What changes is only that a positive here can
   no longer route through `A_new`'s easy DLP** (that is the part §2 closes); it would have to extract
   `d`-information from the lift's coordinates directly.
2. **D2, the Lang-torsor twist bridge.** D2 is a statement about the **values** of `V(a)` — whether the
   exact `√p·ζ` rigidity survives the twist by `L_{χ_a}` — not a transfer of a point into a group. The
   gate does not apply to it. `[OPEN]`, unchanged, and it is the stronger of the two doors.
3. **Route 3 / N4, the cover-family index calculus.** Index calculus on `Jac(C)` does not need `n` to
   be visible in `A_new`; it works in `E`'s own component. `Õ(p^{4/3})` for one cover, not a family
   bound. `[OPEN]`, unchanged.

---

## §7 The two proposed "glues", placed

- **"Fake GLV".** The record's own placement map (`REFERENCE_tangential_literature_placement_map_v1.md`
  field 5) files it under *ZK proof systems / non-native arithmetic*, `[CITED — real]`. It is a
  scalar-multiplication / in-circuit **verification** technique built on lattice reduction over a known
  scalar relation — it constructs no new correspondence between two abelian varieties. **`[ASSERTED —
  citation-verifier owed]`**: no grade in this file rests on that characterisation, and per CLAUDE.md
  §2 a `citation-verifier` pass is required before any grade moves on it either way.
- **Endomorphism simulation inside SNARKs.** Same field. Simulating an endomorphism in a circuit
  emulates arithmetic that already exists; it cannot manufacture an element of `Hom(E, A_new)`, which
  is `0` as an abelian group (P13). Note this is a remark about the *homomorphic* route only — it
  inherits P13's scope and adds nothing to it.

**One caution on provenance:** the phrasing of the proposal tracks the four user-supplied survey
reports closely, and the placement map already quarantines fabricated landmarks from that same batch
(`"ChronoForge"`, garbled qubit counts, unverified CVE IDs). The `A_new` mathematics above is *ours*
and stands on our own computations; the two "glue" references are the parts that came from the surveys
and are the parts to verify before use.

---

## §8 Next probes (find, not verdict)

1. **D1's non-affine arm, properly instrumented.** The forced-null finding of §4 means the arm needs a
   prime where the null *can* fail: choose `p` with `ℓ | gcd(#E(F_p), #A_new(F_p))` for a large `ℓ`, so
   that an additive map is *possible*; only there does a measured `0/N` mean anything. Such primes
   exist (the `C1` control found 80 co-factor hits at small primes). **This is the firing control the
   D1 measurement never had**, and running it is cheap.
2. **D2 unchanged** and now the higher-value door: the twisted eigenvalues of `L_{χ₂(y)} ⊗ L_{χ_a}`,
   are they exact `√p·ζ`, and structured in `a`?
3. **Regrade M17 and M18** in the master as forced (Corollary A; §4). Both are correct measurements of
   forced quantities. Per CLAUDE.md §2, promoting anything into a consolidated document requires
   `compile-diff` first — not run here, and this file is not a promotion.

---

## §9 Gates

- **`experiment-designer` (pre-registration): NOT invoked.** Reason: not unavailability — a
  session-level instruction not to spawn subagents unasked. The substance was pre-committed inline in
  the script header before the run (statistic, outcome map, two firing controls, two instrument
  checks). Recorded as **owed** per CLAUDE.md §2a(3). The load-bearing result here is the §2 theorem,
  which is a proof and does not run through that gate; the §4 sweep, which does, is **forced by the
  theorem** and is graded as an instrument check, so no grade in this file rests on it.
- **`citation-verifier`: owed** on the two field-5 references (§7). No grade rests on them.
- **`compile-diff`:** not applicable — nothing is promoted into a consolidated document here.
