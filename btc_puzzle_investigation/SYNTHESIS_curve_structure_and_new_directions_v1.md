# Curve structure — what is established, and where the pieces now touch each other

*2026-07-26. A synthesis and a direction list. **Nothing here is promoted; no grade moves.** No
leakage, key-recovery or ECDLP claim is made. Items marked `[MINE — in-session derivation,
UNVERIFIED]` are my own algebra written this session and have had no independent check.*

> **PROVENANCE — what was actually read.** `memory/btc_puzzle_INDEX.md` (lines 1–726 of 1374),
> `OPEN_ITEMS_LEDGER_v1.md` (full), `NEXT_DIRECTIONS_v1.md` (full), `POSITIVE_FINDINGS_MASTER_v4.md`
> Parts I–VII plus the P6b row and the heading list, `RESULT_n1_v_sign_mechanism_v1.md` §§2–4.
> **NOT read:** master Parts VIII–XII bodies, `POSITIVE_FINDINGS_ADDENDUM_1_v1.md`, every other
> `RESULT_*`. Rows sourced only to the index are one compression away from the object and are marked
> as pointers to check, not restatements.

---

## Part 1 — The structure, organized by object

Six layers. Each row is the record's own grade, not a re-grade.

### 1.1 The ambient object: `ℤ[ω]` and its two adjacent ideals

`End(E) = ℤ[ω]` maximal `[PROVED]`. Two ideals matter, and they differ by one:

```
(π_p)              ℤ[ω]/(π_p) ≅ F_p        ← coordinates live here
(π_n) = (π_p − 1)  ℤ[ω]/(π_n) ≅ ℤ/n        ← scalars live here
```

`NEXT_DIRECTIONS §1` already names this as the frame: every proved law is a statement about **one**
quotient; every open frontier of consequence sits in the slippage — the `−1`. Part 2 below argues
that the `−1` has since acquired three more independent appearances, and that they are the same
operator.

### 1.2 Lift geometry on `(π_p)` — closed, exact, continuum-proved

Rhombus theorem (both reduced basis vectors have norm exactly `p`); angle law `p₀(θ)`, pinned pair
`= 1/8`; norm band `s ∈ [0, ¾]`, mean `1/6`, breakpoints `3/16, ¼, ¾`; **Cap Law `[PROVED]`**
(`ε ≠ 0 ⟺ |u−v| > ½`, densities `¾:⅛:⅛`), with `σ = sign(u−v)` **`μ₃`-invariant and `μ₂`-odd**, i.e.
`σ` is the `μ₂`-isotypic part of `μ₆` — Thm A/B, `cap_law_proofs_v1.md`. Frame operator `λ_max/Tr`
exactly `½` on the `μ₃`-core (Schur, `[PROVED — forced]`) and `¾` on the full lift; **`¾ − ½ = ¼` =
the flap fraction.** `C_T` is the tensor square, coupling bounded `< ~1.6%` at `n ≈ 1.3×10⁵`.

Literature status (2026-07-25 sweep): Thm A steps 1+3 are **classical** (disc `−3` has exactly six
automorphs — Gauss/Pell). **Lemma C not located**; it keeps its standing.

### 1.3 Selection rules — one rule, not five walls

Claim S (`μ₆` bidegree) and the strictly stronger Claim F (field bidegree, failure mode = the sextic
twist) `[PROVED + 336/336, 180/180]`. Measured field bidegrees: `σ = (1,0)`, `eps = (0,0)`,
`χ₂ = (1,0)` at `p≡3 mod 4`. Of 240 non-forced FIELD pairs, 72 vanish; 56 are ordinary `F_p*`
orthogonality, and the residual **16 are one live object** — the `σ×χ₂` programme.

**The rule is two-sided.** It says which channels must vanish and therefore **which are permitted to
be nonzero**. Part III advertises this; §2.3 below cashes it out for a pair that has not been run.

### 1.4 CM / L-function / twist / amicability

`4p = t² + 3f²`, `f = 3·79·349·2698097·(91-bit prime)`. `ord_n(p) = (n−1)/6`, `ord_n(2) = (n−1)/64`
— **both dissolved** (selection effect; a `1/6` draw), with `(L1)–(L3)` proved en route.
`π_n = π − 1`; sextic identities; formal-group log `μ₆`-sparse with the order-2 shadow
`R^(2) = T + 3T⁷` exact. **secp is an amicable pair** — `#E(F_n) = p` exactly `[PROVED, full scale]`.
⚠ Framing narrowed 2026-07-25: the Pasta curves are a published, deliberately-constructed amicable
`j=0` pair; the defensible residue is "secp's own instance not located".

**The bridge programme.** `(B1) χ₃(p mod n) = ω^{c₃}·χ₃(n mod p)`, `c₃` in closed form
`[PROVED | classical inputs]`, `12050/12050`, and it **reaches 256 bits intact** — an exact identity
does not decay. `(D1)` prime-order CM curves exist iff `D ≡ 5 mod 8`; `(D3)` `D = −3` is the unique
prime-order CM discriminant with a bridge past `ℓ=2`, and secp sits on it. At `ℓ ≥ 5` the CM route
**collapses by forced algebra**: `π̄ ≡ t−1 (mod ν)` element-wise (250/250), so both bridge sides are
symbols of the **same rational** `U = |t−1|`. Marginal and conditional MI probes find no `ℓ≥5`
bridge, bounded at a `~6%` copy-fraction floor — a bound, not a closure.

### 1.5 The `χ₂(y)` cover, and N1

`C : w⁴ = x³+7`, genus 3, `Jac(C) ~ E × A_new`. `A_new` **supersingular at secp** `[PROVED, §A1.1]`,
`Hom(E, A_new) = 0` `[PROVED]`. Route 3 (cover transfer) stays open.

The N1 chain, as it now stands:

| step | statement | grade |
|---|---|---|
| purity | all four Frobenius eigenvalues of `H¹_c(L_{χ₂(y)} ⊗ L_{χ_a})` have modulus exactly `√p` | `[PROVED — all p]` |
| closure | multiset closed under `α ↦ −ᾱ` | `[PROVED — FORCED]` |
| phase formula | `\|V(a)\| = 2√p·\|sin θ₁ + sin θ₂\| = 2√p·\|u\|` | `[PROVED]` |
| WD bound | `\|Σχ₂(y_P)e_n(ad)\| ≤ 4√p` (`#R = 4`), `\|Σχ₂(x_P)e_n(ad)\| ≤ 2√p` (`#R = 2`) | `[PROVED\|WD]`, P6b |
| **the identity** | `V₂ = V₁² ± 2p`, i.e. `v = u² − 3/4`, i.e. `s₁ = cos(t−60°)`, `s₂ = cos(t+60°)` | **`[VERIFIED — exact]`, 357/357 classes, `9.5e−40`; 8–10 primes. NOT derived.** |
| **the cap** | `S_y := max_a \|V(a)\|/√p ≤ 2` | `[VERIFIED — out-of-sample]`, 120 primes, 4.7M cells. **Open.** |
| refuted | `v ≤ 0` (⟺ `\|V₁\| ≤ √3√p`, a sub-Weil bound at 86.6% of `2√p`) | `[PROVED FALSE — exact counterexamples]` |

### 1.6 The leakage frontier — what is bounded

Bounded-degree **additive** readouts: `|Corr_F(a)| ≤ 2D√p/n` `[PROVED|KS]`; `max|U(a,b,c)| ≤ 4√p+1`
uniform in `(b,c)`. **Multiplicative rows are a different theorem and it is on disk** (P6b, Kummer
sheaf, `weil_deligne_character_bound_v1.md §6′`) — **do not attribute those to KS.** Structured
pairs `v = k·u` collapse into KS at fixed `k`. Covariance:
`|Cov_d(F(x_d), g(d))| ≤ (max|T|/n)·‖F‖_A·‖g‖_A`.

`[GAP]` remains for general poly-time (non-bounded-degree) readouts. The `#1` open lead is a **cheap
partial of the joint `(x,y)` shadow** (aligned readout reaches `0.93`, with the M14 control caveat
attached). `xy` is odd-in-`d` and `μ₃`-weight-1 — the symmetry type the odd half needs.

Thermodynamic layer: Porter–Thomas intensities, no metastable soft mode beyond `μ₆`, single-well
landscape `[EMPIRICAL, p ≤ 2503, joint channel re-run]`.

---

## Part 2 — Where the pieces touch: six connections, and what each makes decidable

### 2.1 ★ The 120° law **is** the cap. `[MINE — in-session derivation, UNVERIFIED]`

Take the three proved steps of §1.5 and the identity, and run the algebra:

`s₁, s₂` are the roots of `z² − uz + v = 0`. They are **real** — that is exactly what purity
(`[PROVED — all p]`) plus the `α ↦ −ᾱ` closure (`[PROVED — FORCED]`) give, since `s_i = sin θ_i`
with `θ_i` real. Substitute the identity `v = u² − 3/4`:

```
disc = u² − 4v = u² − 4u² + 3 = 3(1 − u²)  ≥ 0   ⟺   |u| ≤ 1
```

and `|V(a)| = 2√p·|u|`, so **`|u| ≤ 1` is precisely `S_y ≤ 2`.** Equivalently, in the parametrized
form the record already verified to `9.5e−40`: `u = cos t`, so `|u| ≤ 1` is `|cos t| ≤ 1`.

Three consequences:

1. **`v ≤ 1/4` and `S_y ≤ 2` are the same statement**, not two. `v ≤ 1/4 ⟺ u² ≤ 1 ⟺ 2|u| ≤ 2 ⟺
   max|V|/√p ≤ 2`. `RESULT_n1_v_sign_mechanism_v1.md §3` states them as separate ("whether `1/4` is
   useful for `S_y ≤ 2` is a separate, untested question").
2. ⚠ **A correction is owed to that file's own table.** It derives `v ≤ +1/4` from *"Weil `|u| ≤ 1`"*.
   Weil does not give `|u| ≤ 1`. Purity gives `|s_i| ≤ 1` each, hence `|u| ≤ 2` and `|V₁| ≤ 4√p` —
   which is exactly the `#R = 4` WD bound in P6b, and is the ceiling the same record uses everywhere
   else when it says `χ₂(y)` "saturates `0.470` of `4√p`". Line 59's source column is wrong as
   written; the correct source for that row is the discriminant above. **The mis-attribution is what
   hid the implication** — labelling `|u| ≤ 1` "Weil" makes it look already-had, so nothing points
   from it back to the open cap.
3. **Therefore the whole open inequality is now one exact identity.** `S_y ≤ 2` — 120 primes,
   4.7M cells, no proof, carried as the single open link of the N1 story — follows from
   `V₂ = V₁² ± 2p` by elementary algebra. Nothing else is missing.

**This does not prove the cap.** The identity is `[VERIFIED — exact]` at 8–10 primes, not derived.
What changes is the type of the open item: from "prove an inequality about a maximum over `(n−1)/6`
classes" to **"derive one exact identity from the CM structure"** — and the record already names that
derivation as the next step (`RESULT_n1_v_sign_mechanism_v1.md`: *"next step: derive it from the `μ₆`
action"*). It just does not record what derivation would buy.

**What the mechanism has to be.** `s₁² + s₁s₂ + s₂² = 3/4` is the **Eisenstein norm form** at a fixed
level. The stabilizer of that form is the **six automorphs of discriminant `−3`** — the same Gauss/Pell
fact that Cap Law Thm A step 1 rests on, and which the 2026-07-25 sweep confirmed is classical. The
`μ₆` that collapses `n−1` cells to `(n−1)/6` on the `a`-side (`V(a) = V(aλ)`,
`V(a) = χ₂(−1)V(−a)`) is the candidate for that same group acting on the phase pair `(s₁, s₂)`. The
concrete object: `(x, w) ↦ (βx, w)` is an order-3 automorphism of `C : w⁴ = x³+7` commuting with
Frobenius, so it acts on the 4-dimensional `H¹_c` with `ζ₃`-eigenvalues; the claim to prove is that
its eigenspace decomposition forces the two half-angles `120°` apart.

This is the "translation lens" move in `memory/MEMORY.md` — check whether an existing architecture
transfers before inventing. Thm A's step 1 is the architecture.

**First move is a control, not a proof.** The proposed mechanism is CM/`μ₃`-driven, so it must
**fail** off `j = 0`. Compute `S_y` for the `χ₂(y)` readout on curves with `j ≠ 0` (no `μ₃`), same
`p`, prime order. Predictions are separated:

- mechanism is `μ₃` ⇒ generic curves should run up toward the `#R = 4` ceiling, not stop at `2`;
- `S_y ≤ 2` holds there too ⇒ the mechanism is **not** `μ₃`, and §2.1's route is wrong.

The record has never had a control for the cap that varies the *mechanism* — every control so far
varied the readout or the null. Part VII.1 explicitly warns that `L1`/`L2` are curve-independent and
that this is "the correct scope, not a defect", so curve-independence is live and must be tested, not
assumed. **`experiment-designer` prereg before the sweep** (CLAUDE.md §2 — "sweep" is named).

A second, sharper control is already on disk: the **3-isogenous descendant** `E'` with `End = O_3`,
`j ≠ 0`, **no GLV, no `μ₆`** — exhibited at `p = 43, 127`, and proved to exist at secp
(`v_3(f) = 1`). Same `n`, same `p`, CM by a non-maximal order. It separates "CM" from "`μ₃` on the
cover" in a way a random `j ≠ 0` curve does not.

### 2.2 What proving the cap would actually buy — a factor of 2, in a place that is already load-bearing

Stated carefully, because the neighbouring claim is easy to overstate: **the multiplicative-character
bound is not missing.** P6b proves `|Σχ₂(y_P)e_n(ad)| ≤ 4√p` via a Kummer sheaf, and
`weil_deligne_character_bound_v1.md §6′` carries it. §XII.10's scope gap is closed there, not open.

What the cap adds is the **factor 2**: `4√p → 2√p`, i.e. "four ramification points contribute as
two". Downstream, that halves every covariance bound that runs through the `y`-channel:

```
|Σ_d g(d)·χ₂(y_d)|  ≤  max_a|V(a)| · ‖g‖_A   ≤  2√p·‖g‖_A      (currently 4√p·‖g‖_A)
```

for **any** scalar-side function `g` on `ℤ/n`, where `‖g‖_A = Σ_a |ĝ(a)|` is the Wiener norm. This is
the record's own covariance pattern (Part VI) with the `χ₂(y)` readout in place of the additive one.

**The decidable object this exposes: `‖g‖_A` on `ℤ/n`.** The `y`-channel leakage question reduces to
a Wiener-norm question on the scalar quotient — any `g` with `‖g‖_A ≪ n/√p ≈ √p` is analytically
bounded, and a channel through `χ₂(y)` **must** use a `g` of large Wiener norm. That is a proof-shaped
statement, not a test, and this project's stance is that only those close an avenue.

Concrete and cheap: compute `‖σ_n‖_A`, `‖eis_n‖_A`, `‖bit_j‖_A` at small `n`, and ask whether the
Cap Law geometry gives `‖σ_n‖_A` in closed form (`σ` is a lattice sawtooth; its transform should
factor, plausibly giving `O(log² n)` — in which case the channel in §2.3 is bounded analytically
before any data is drawn).

### 2.3 ★ Move the flap to the **scalar** lattice — the parity-legal repair the flap↔N1 bridge asked for

`RESULT_n1_flap_bridge_v1.md` found a **forced parity obstruction**: `Σ_d χ₂(y_d)·σ(x_d) ≡ 0` for
every `p ≡ 3 mod 4`, because `χ₂(y)` is odd under `P ↦ −P` while `σ` reads only `x`, and `−P` has the
same `x` — so `σ∘x` is **even** in `d`. The file named two repairs: nonzero frequency, or a `y`-aware
flap. There is a third it did not name.

**Put the flap on `(π_n)` instead of `(π_p)`.** Define `σ_n(d) := σ` of the Eisenstein lift of `d` in
the `(π_n)`-lattice — the same Cap Law function, same `|u−v| > ½` region, evaluated on the **scalar**
quotient. Then:

| | `μ₂` (`d ↦ −d`) | `μ₃` (`d ↦ λd`) | bidegree |
|---|---|---|---|
| `χ₂(y_d)`, `p≡3 mod 4` | odd | invariant (`λ` fixes `y`) | `(1,0)` |
| `σ_n(d)` | **odd** (`z ↦ −z` ⇒ `u−v ↦ −(u−v)`) | invariant (`λ ≡ ω mod π_n`) | `(1,0)` |
| product | **even** | invariant | `(0,0)` |

`(1,0) × (1,0) = (0,0)` ⇒ **Claim S permits this pairing to be nonzero.** The parity obstruction does
not apply, because `σ_n` reads `d`, not `x`, and `d ↦ −d` genuinely negates the lift.

It is also distinct from everything already run:

- **not** `eis_p × eis_n` (forced zero by parity: `eis_p` even in `d`, `eis_n` odd);
- **not** ARM 4 (odd `y`-readout against the `μ₆`-graded sextant lift, 6 cells, bounded at `0.5%`
  copy-fraction). `σ` is the `μ₂`-**odd isotype**, a different channel of the same decomposition —
  and "finer than 6 cells" was ARM 4's own named next step.

And §2.2 supplies its analytic companion: `|Σ_d σ_n(d)χ₂(y_d)| ≤ max|V|·‖σ_n‖_A`. **The empirical arm
and the bound meet on the same object** — run the Wiener-norm computation first; if `‖σ_n‖_A` is
polylog, the channel is bounded before any test, which is the stronger outcome.

Prereg mandatory. Controls that must fire: a plant at a known injection level; a `μ₆`-carrying null
(never a plain shuffle — `feedback_residue_vs_component_tautology`); and the **parity ledger printed
for both sides**, so a second forced zero cannot masquerade as a result.

### 2.4 The entire lift-geometry programme has an unrun mirror on `(π_n)`

Parts II and V are stated for `(π_p)` only. Every one of those laws — rhombus, sextant/angle law,
norm band, Cap Law, `σ`, frame operator, `C_T` — is a statement about **an ideal of `ℤ[ω]` with prime
norm**, and `(π_n)` is another one. The amicable geometry is already measured: `P_n` overlaps `P_p` by
`1 − 4.1e−39`, `C_n ⊆ C_p`, slippage `R1_p − R1_n = (0,1)`, `R2_p − R2_n = (1,1)`.

Unrun and cheap:

- `θ_n = arg(π_n) mod 60°` against `θ_p = 50.55°`, and whether the **pinned-pair ↔ Frobenius-angle**
  bridge (`{1,4}` if `θ<30°` else `{0,3}`, 0 violations / 69 primes) gives the **same** pinned pair
  for both ideals. A forced check with a clean falsifier.
- The `h(−n)` analogue of `|FLD| = 6h(−p)`: `Ẽ = E/F_n` has `#Ẽ(F_n) = p`, CM by the same `ℤ[ω]`,
  Frobenius `π_n`. Every `σ×χ₂` object has an `n`-side twin nobody has computed.

**Why it matters structurally:** `ℤ/n` is the base **field** `F_n` of `Ẽ`. On `E` the scalar `d` is an
exponent (hard); on `Ẽ` the same `d` is a **field element** (`χ₂(d)`, `eis_n(d)`, `σ_n(d)` all cost
`O(1)`). The amicable correspondence is the only object in the record that natively relates the hard
scalar to cheap field-element structure. That is why frontier `#3` is where it is, and §2.3 is one
instance of exploiting it.

⚠ **Guard, so nobody re-derives a false lead.** The CRT map `z ↦ (z mod π_p, z mod π_n)` is **not**
the curve map `d ↦ x_d`. If it were, the DLP would be a linear congruence. Any construction that
quietly identifies them is wrong; state which map is in use.

### 2.5 The `−1` is now an operator with four appearances — and it has a proved calculus

The 2026-07-24 general law `[PROVED — every non-principal `χ`, any `p`]`:

```
Σ_s χ(s)·sgn(cs mod p − s) = 2·B_{1,χ}·( χ̄(c) − χ̄(c−1) − 1 ),      B_{1,χ} = (1/p)Σχ(t)t
```

**The entire `c`-dependence is the finite difference `χ̄(c) − χ̄(c−1)`** — the slippage operator. The
same `−1` is: `π_n = π_p − 1` (amicability); `U = t − 1` (the bridge's shared rational,
`π̄ ≡ t−1 mod ν`); and now the coboundary structure of the sawtooth law. Four appearances, one map.

`[MINE — in-session derivation, UNVERIFIED]` **the `3` in `3h(−p)` is the Eisenstein relation.** At
`c = ρ` (primitive 6th root, `ρ − 1 = ρ²` in `ℤ[ω]`) and `χ = χ₂`, with `p ≡ 7 mod 12`:
`χ₂(ρ) = ρ^{(p−1)/2} = ρ³ = −1` and `χ₂(ρ−1) = χ₂(ρ²) = +1`, so the bracket is `−1 −1 −1 = −3`, and
`B_{1,χ₂} = −h`. The class-number multiplier is not a free constant — it is the slippage operator
evaluated at the CM unit, and `ρ − 1 = ρ²` is why it is `3`. ⚠ **The half-range/normalization factor
of 2 is not reconciled** (the law sums over all `s`, `(†)` over `s ≤ H`); check that before repeating
this.

**What it makes free.** Every arithmetically meaningful `c` yields an exact identity at no cost:

- `c = 2` — the Gauss/Eisenstein constant already in `H1`;
- `c = β` — the GLV constant;
- **`c = t`** — gives `χ̄(t) − χ̄(U)`, and `χ₃(U mod p)` is a **bridge-programme symbol**
  (`n ≡ −(t−1) mod p`, 300/300). So a sawtooth lattice count over `F_p` computes a symbol that `(B1)`
  relates to a symbol mod `n`: **an exact identity joining the two quotients, of a species that does
  not decay at `2²⁵⁶`.**

⚠ Both sides here are `d`-independent and cheap. **This carries no leakage content on its own** — it
is structure in the frame of §1.1, and should be reported as such.

### 2.6 The `y`-channel is rank-1 in phase space — which redirects the `#1` lead

`V(a)` is now determined by **one real parameter** `u(a)` per `μ₆` class, capped, with a forced
second moment. Two consequences:

**(a) A new exact conservation to test — `[MINE, UNVERIFIED]`.** Parseval + Hasse force the second
moment (`Σ h₁² = n−1`, the record's own "forced, not curve-special" row) ⇒ `E_a[|V(a)|²] ≈ p` ⇒
`4·E[u²] = 1` ⇒ `E[u²] = 1/4` ⇒ with the identity `v = u² − 3/4`:

```
mean_a v(a) = −1/2   exactly
```

Testable this afternoon against the 357 classes already on disk (which report min `−0.749998`, max
`+0.183395` but not the mean). If it holds, it is an exact conservation of exactly the kind drill
rules 7–13 ask for. If it fails, either the Parseval normalization or the identity's scope is
mis-stated — informative either way. ⚠ Count **unforced** cells only, and reproduce the tally
independently (`feedback_anomaly_drill_protocol`, rules 11–13).

**(b) Where the `0.93` is not coming from.** The joint `(x,y)` aligned readout reaches `0.93` vs
`0.37` for `x`-only. The `y`-factor contributes one bounded real degree of freedom per class — so the
lift cannot be `y`-side richness. It is in `x`, or in the `x`–`y` interaction (`xy`: odd-in-`d`,
`μ₃`-weight 1). The flap↔N1 dimension count says the same thing from the other side (N1 side 1 dof,
flap side 2 dof; any bridge factors through `2D → 1D`). **This narrows §XI.1 positively — it says
where to look, and it is not a closure of anything.**

### 2.7 Two method ports, both with a proved template on disk

**(i) Field → ideal (the Stickelberger move).** The Jacobi law closed because Frobenius constrains the
**field** while Stickelberger constrains the **ideal**, which is what killed the `π²` competitor; then
reduction mod the primes above `2` and `3` forced rationality and fixed the sign. Two stuck items have
that exact shape:

- `#9` **FLD-sign intrinsic-ness** — `sign(FLD) = −χ₂(M)`, 54/54, reduces to no tested intrinsic
  invariant. A **sign** question.
- `L1` — `|Σ_{T⁺}χ₂| = F4`, 86/86. An **absolute value** question, and Stickelberger gives exact ideal
  factorizations of Gauss sums, hence absolute values.

Machinery exists (`jacobi_stickelberger_v1.py`). ⚠ **Inherits (D2)**: Stickelberger's citation is
still UNVERIFIED for `m = 12` (not a prime power), `f = 2` — the `citation-verifier` run has died
three times. Re-run it before any new claim leans on it.

**(ii) `L1` via the proved sawtooth law.** `Σ_{T⁺}χ₂ = ½(FLD + Σ_{flap}χ₂)`. The flap is
`|u−v| > ½`, and `(u−v) mod 1` is already known here to be an additive isomorphism
`ℤ[ω]/(π_p) ≅ (1/p)ℤ/ℤ` — so flap-membership is a **sawtooth interval condition**, making
`Σ_{flap}χ₂` a partial `χ₂` sum over an interval: the same species as `F4 = Σ_{p/4<a<p/2}χ₂(a)`,
which has classical closed forms in `h`. `L1` then reads: *the `χ₂`-mass of the flap equals the
`χ₂`-mass of the quarter-interval.* Source-first — the candidates were already located and **not
opened** in the 2026-07-25 sweep (Berndt–Evans, Monatsh. Math. 84 (1977) 265–273; Berndt, JNT 7
(1975) 413–445; Goldstein–Razar, Nagoya 63 (1976) 93–121). Read them before inventing; this record's
own history is that reading the source dissolved the obstacle four times.

---

## Part 3 — Ranked, with the first move stated

Ordering is a proposal, not a computation. Reorder freely. It is **not** ordered by proximity to a
break; items 1, 2, 5, 6 have no leakage content at all.

| # | direction | first move | cost | falsifier |
|---|---|---|---|---|
| **1** | **§2.1 — the 120° law is the cap.** Derive `V₂ = V₁² ± 2p` from `μ₃` on `H¹_c`, using Thm A's disc-`−3` automorph architecture | **the mechanism control first**: `S_y` for `χ₂(y)` on `j ≠ 0` curves, and on the `End = O_3` descendant at `p = 43, 127`. Prereg first | low | `S_y ≤ 2` off `j=0` ⇒ mechanism is not `μ₃` |
| **2** | **§2.6(a) — the forced mean `mean_a v = −1/2`** | recompute the mean over the 357 classes on disk | trivial | mean ≠ `−1/2` |
| **3** | **§2.3 — `σ_n` × `χ₂(y)`, the parity-legal scalar-side flap** | `‖σ_n‖_A` in closed form **before** any test (§2.2); then prereg the pairing | low → medium | `‖σ_n‖_A` polylog ⇒ bounded analytically, no test needed |
| **4** | **§2.4 — the `(π_n)` mirror of the lift programme** | `θ_n mod 60°` + the pinned-pair bridge on `(π_n)` | low | pinned pair differs ⇒ the two ideals are not interchangeable and the mirror is a different object |
| **5** | **§2.7(ii) — `L1` via the sawtooth law + the classical interval formula** | **read Berndt–Evans / Goldstein–Razar** (located, never opened) | low | the flap is not an interval condition in the `(u−v)` coordinate |
| **6** | **§2.5 — the slippage calculus at `c = t`, `2`, `β`** | reconcile the factor-2 convention, then evaluate `c = t` | low | the `c = ρ` reconstruction of `3h` fails after the convention fix |
| **7** | **§2.7(i) — Stickelberger port to `#9` and `L1`** | re-run `citation-verifier` on Stickelberger (D2) first | medium | — |

**Standing gates.** `experiment-designer` prereg before any sweep/scan/drill (CLAUDE.md §2). Every
bound carries POWER + SCOPE. The control must fire. A drill ends in a sharper law, a bounded
magnitude, or a next probe — never a closure. Retest out-of-sample before naming a zero; count only
**unforced** hits; reproduce the tally.

---

## Part 4 — Forced non-questions (do not spend a run on these)

- **Descent does not move the bridge.** `(B1)` is a statement about `p` and `n` only. A 3-isogenous
  descendant has the same `p` and the same `n`. Nothing to test.
- **The CRT map is not the curve map** (§2.4 guard). If it were, the DLP would be linear.
- **`[−1]` and `ζ₄`** as the N1 splitting mechanism — both are the same map on `E`, refuted on file
  (`NEXT_DIRECTIONS §4`). ⚠ the `ζ₄` derivation there is flagged as the author's own and unverified;
  verify before letting it suppress a candidate.
- **`eis_p × eis_n`** — parity-forced zero. Measuring it measures nothing.
- **`M4` (fourth moment) against the low tail** — blind by construction (`r⁴ ≈ 0` for `r < 0.1`).
- **No PRNG / generation-side work** (standing, repeated).

---

## Part 5 — Corrections and checks owed to existing files

Each is a candidate, stated with what would settle it. None is applied here.

1. **`RESULT_n1_v_sign_mechanism_v1.md` §3, table row 2** — sources `v ≤ +1/4` to *"Weil `|u| ≤ 1`"*.
   Weil/purity gives `|s_i| ≤ 1` hence `|u| ≤ 2`, `|V₁| ≤ 4√p` — the `#R = 4` ceiling that the same
   record uses for the `0.470` saturation. The row's correct source is discriminant non-negativity
   (§2.1). ⚠ Versioning bars an in-place edit (CLAUDE.md §1) — this belongs in a `v2`.
2. **Same file, §3 closing line** — *"whether `1/4` is useful for `S_y ≤ 2` is a separate, untested
   question"*: `v ≤ 1/4` and `S_y ≤ 2` are the same statement (§2.1).
3. **`OPEN_ITEMS_LEDGER_v1.md`, row "N1's phase law"** — asks *"is `|sin θ₁ + sin θ₂| ≤ 1`?"* as a
   thing to test at more primes. Given the identity, it is not an independent question; the item
   should point at the identity's derivation.
4. ⚠ **An object-level conflict worth one cheap check.** P6b proves `|Σχ₂(x_P)e_n(ad)| ≤ 2√p`
   (`#R = 2`), while `RESULT_n1_phase_cap_v2.md` D4 records `χ₂(x)` **exceeding 2 at 51 of 193
   primes**, max excess `0.0203` (at `p ~ 10⁵` that is `≈ +6.4`, more than the `+1` pole allowance).
   Both are in the record; at most one can be right as stated. Candidates: the `#R = 2` ramification
   count for `χ₂(x)`; the normalization or the `a = 0` / `d = 0` handling in the sweep. This bears
   directly on N1, since the `χ₂(y)` cap is the same machinery with `#R = 4`. **Check the instrument
   before the theorem** — this record's own pattern is that an arithmetic impossibility in a printed
   column is the tell.

---

## What this document does not claim

No grade is moved. The cap is **not** proved — §2.1 shows it follows from an identity that is itself
`[VERIFIED — exact]` at 8–10 primes and not derived. §2.2's factor of 2 is contingent on that. §2.3
and §2.4 are unrun objects with no measurement behind them. §2.5's factor-2 convention is
unreconciled. §2.6(a) is arithmetic that has not been checked against the data on disk. Everything in
Part 2 marked `[MINE]` was written in one session with no independent review, and the record's own
history is that in-session derivations which appear to close something are the shape to distrust.

**Scale banner #5 governs everything empirical here.** Every measurement discussed is at
`p ≈ 10²–10⁵` against secp's `2²⁵⁶`. The exceptions that reach scale are the exact identities —
`(B1)`, the amicable relation, the `μ₆`-cover derivations — and, if it is ever derived rather than
verified, the N1 identity.
