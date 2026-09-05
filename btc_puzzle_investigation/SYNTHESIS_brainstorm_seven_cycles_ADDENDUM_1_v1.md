# Brainstorm addendum 1 — what the write-up dropped

*2026-07-26. **ADDITIVE.** Read alongside `SYNTHESIS_brainstorm_seven_cycles_v1.md`; supersedes
nothing in it. Nothing run, nothing promoted, no grade moves. No leakage or ECDLP claim.*

> **Why this file exists.** The user asked me to re-read my own reasoning from the brainstorm. About
> ten items were generated during the seven cycles and then **died at the compression step** — they
> never reached the document. One of them I had explicitly concluded was *"now the highest-value item"*
> mid-reasoning and then omitted entirely.
>
> **That is this project's #1 named institutional failure mode, reproduced at small scale.**
> `DEGRADATION_AUDIT_H3_TO_MASTER_v1.md` records live frontiers going **5 → 0** across one
> consolidation, invisible to tag-count auditing, because *"closure frame enters at the consolidation
> step."* My write-up lost ~10 of ~30 generated items in one pass, and — exactly as the audit
> predicts — **the losses were not random**: what survived was what already had a crisp verdict
> attached, and what died was the open-ended and the cross-referential. A tag count of the brainstorm
> document would show it healthy.

---

## §1 — Inventory: generated, then dropped

| # | generated in-cycle | fate | taken up below |
|---|---|---|---|
| 1 | **`V(a)` is the `A_new` channel**; `μ₁₂ ⊇ μ₃`; 120° = the CM residue surviving the twist | dropped entirely | **§2** |
| 2 | **D2 (Lang-torsor twist bridge) is the item this answers** — I wrote *"D2 is now the highest-value item, and it is ripe"* and then omitted it | dropped entirely | **§2** |
| 3 | Closed form for `V(a)` as a Jacobi/Hecke object; `θ_a` structure; the sequence consequence | only the linear-complexity fragment survived | **§3** |
| 4 | Is `a ↦ θ_a` arithmetically structured? (equidistribution ≠ no structure) | dropped | **§3** |
| 5 | **RMT beyond Porter–Thomas** — only 1 of 5 standard statistics was ever measured | dropped | **§4** |
| 6 | Farey comb (1D) ↔ rhombus (2D) = the two quotients' reduction theories | dropped as "loose" — i.e. **prefiltered**, which is what I was asked not to do | **§5** |
| 7 | secp = reduction of the **global** curve `y²=x³+7/ℚ`; `t` = a CM newform coefficient | compressed to a one-line literature pointer | **§6** |
| 8 | The trichotomy of **what can beat `√p`** | dropped | **§7** |
| 9 | **Forced non-questions** — the whole section, present in the previous synthesis, vanished | dropped | **§8** |
| 10 | CM index calculus; the `(N(z), N(eis(x([z]P))))` joint statistic on short vectors | reduced to generic "short scalars" | **§9.1** |
| 11 | `±`-pairing rows are exactly `b=0` (worked out, then discarded with its conclusion) | dropped | **§9.2** |
| 12 | `3 | f` is probably **not** forced (mod-3 argument worked through) | reduced to "is it forced or a draw?" | **§9.3** |

---

## §2 — ★★ The biggest drop: this is D2, and it also supplies item 12's missing discriminator

### 2.1 Two ledger items I failed to connect

**D2** (`MASTER_v4` Part VII.4, carried as NOT closed):

> *"D2 — the Lang-torsor twist bridge (does the exact `√p·ζ` rigidity survive `L_{χ₂(y)} ⊗ L_{χ_a}`,
> giving `V(a)` exact algebraic values structured in `a`?), untouched by this test."*

**Item 12** (`OPEN_ITEMS_LEDGER_v1.md`, OPEN, both designed tests failed):

> *"A discriminating signature for the CM layer `L3` (N3) … A real test must target the **CM type**
> (the embedding of `ℚ(ζ₁₂)` on the tangent space), **not** which field `L_new` splits over."*

Checked this session: **`PREREG_D2_lang_hypergeometric_relin_v1.md` exists (2026-07-20) and there is
no `RESULT_*` for it — it was never run.** And grep finds **no cross-reference anywhere** between the
120° phase law and `A_new` / `L3` / `M17`; every other "120°" in the corpus is the *lattice* angle
(Cap Law, frame operator), a different object.

### 2.2 The chain

All steps are the record's own except the last two.

1. `A_new` is **supersingular** at every `p ≡ 3 mod 4` `[PROVED from automorphisms; VERIFIED 24/24]`
   ⇒ at secp (subject to N2).
2. Supersingular ⇒ `H¹_new` Frobenius eigenvalues are **exactly `√p·ζ`, `ζ` a root of unity** — the
   record's own words, "maximal rigidity" (M17).
3. **L3:** `μ₁₂ ⊆ Aut(C)` ⇒ `ℚ(ζ₁₂) ⊆ End⁰(A_new)`, degree `4 = 2·dim` ⇒ CM abelian surface. So the
   roots of unity in (2) live in a field containing `ζ₁₂`. **And `μ₁₂ ⊃ μ₃`.**
4. `dim H¹_new = 4` (abelian surface) and `dim H¹_c(L_{χ₂(y)} ⊗ L_{χ_a}) = 4` — **the same dimension**,
   and at `a = 0` the twist is trivial (`V(0) = Σ_P χ₂(y_P) = 0`, `[PROVED]` L1 at `p≡3 mod 4`).
5. `[MINE]` **⇒ `a ↦ {the four eigenvalues}` is a DEFORMATION of the supersingular configuration,
   based at `a = 0`.** That is exactly the object D2 asks about, made concrete.
6. `[MINE]` **⇒ the 120° law is D2's answer, and it is a *partial* one, which is the interesting
   shape:**

> **The absolute angles do NOT survive the twist** — they become the free parameter `θ_a`, which
> equidistributes (Sato–Tate; `mean|u| = 0.408` vs `0.424`).
> **The RELATIVE angle DOES survive, frozen at exactly 120°** (`9.5×10⁻⁴⁰`, 357 classes).
> ⇒ **the `μ₃ ⊂ μ₁₂` part of the CM survives the Lang torsor; the rest does not.**

7. `[MINE]` **⇒ that is item 12's discriminator.** A fixed relative phase of `120°` between the two
   conjugate pairs is a statement about **how `ζ₁₂` embeds**, not about which field `L_new` splits
   over — precisely the distinction item 12 draws. And unlike the two tests that failed, it is
   **per-prime, per-class, exact, and already measured** at 357 classes over 8 primes.

### 2.3 ★ A third measurement of what may be the same fact

`M17`: **MOV embedding degree `k = ord_ℓ(p) = 3` at every tested supersingular prime**
(`p = 31,43,67,79,103,127,139` — 7/7).

For a supersingular abelian variety with `π = √p·ζ`, the group order — and hence the embedding degree
— is determined by `ζ`'s order. **A uniform `k = 3` is what a `μ₃`-structured `ζ` produces.**

⚠ **This is a connection to check, NOT a derivation.** `ord_ℓ(p)` is a statement about the subgroup
order `ℓ`, and I have not verified the relation to `ζ`'s order. **The check is cheap and decisive:
at M17's own 7 primes, compute the untwisted `H¹_new` eigenvalues explicitly and read off `ζ`'s
order.** If the `μ₃` part is there, then M17 (Part VII.2), the 120° law (`RESULT_n1_v_sign_mechanism`),
and item 12 are **one fact measured three times in three parts of the record with no cross-reference.**

### 2.4 What this gives the cap that §1 of the brainstorm did not

The brainstorm derived the `ζ₃` from the ramification structure (three 2-torsion points = one
`μ₃`-orbit; `E/μ₃ ≅ P¹` a cyclic cubic cover). **§2.2 is an independent second route**: the `ζ₃` comes
from `μ₃ ⊂ μ₁₂ ⊆ Aut(C)` acting on a supersingular `H¹_new`. Two independent derivations of one
lemma is this record's own standard — weight-1 was proved two ways (KS Prop 1+2 / Deligne 3.2.3), and
the Jacobi law closed only when Stickelberger replaced Frobenius.

### 2.5 The experiment, and the instrument already exists

**Compute the four eigenvalues at `a = 0` and follow them as `a` increases — the deformation path.**
`n1_twisted_eigenvalues_v1.sage` already computes twisted eigenvalues (control C2 fires at `4.4e−16`);
`a = 0` is the untwisted end it has never been pointed at.

Pre-committed readings, both informative:

- eigenvalues at `a=0` are `√p·(12th roots of unity)` **and** the relative `120°` holds along the whole
  path ⇒ D2 answered as in §2.2, item 12 gets its discriminator, and the cap gets a second mechanism;
- the relative angle drifts with `a` ⇒ **the 120° law is not a CM residue**, §1 of the brainstorm is
  wrong about the mechanism, and D2's answer is "nothing survives".

⚠ Read `PREREG_D2_lang_hypergeometric_relin_v1.md` first and check whether its arms already cover the
relative-angle question; amend rather than re-spec. `experiment-designer` before any sweep.

⚠ **Scope:** `N2` is attached to step 1 — the dim-2 supersingularity implication is `[VERIFIED 24/24]`,
not proved, and its two external inputs still owe an independent re-derivation.

---

## §3 — The closed form for `V(a)`, and the one honest link to the leakage half

### 3.1 Why a closed form is now plausible

D2's second clause — *"giving `V(a)` exact algebraic values **structured in `a`**"* — is the half
nobody has attacked. The brainstorm's own finding makes it more plausible, not less: **the object
collapses to a single sine**, so the twisted family is effectively rank-2, which is Hecke-character
shape. This record has produced exactly this kind of closed form twice already (the `m`-law, the
Jacobi sign law), both times as Gauss/Jacobi sums.

### 3.2 ★ The correctly-scoped consequence — and it is NOT a break

I drifted toward an overclaim mid-reasoning ("a closed form ⇒ the `y`-Legendre sequence becomes
predictable") and corrected it in the same cycle. The corrected version, which is the one worth
keeping:

**A closed form for `V(a)` breaks nothing by itself.** The cap bounds *every individual frequency*
`|V(a)| ≤ 2√p` regardless of whether you can compute it, so knowing which frequency to look at buys
nothing when no frequency is large. Linear complexity is full (DC5: at prime `n` a full-orbit
character sum cannot vanish exactly unless the readout is constant).

**But** — brainstorm §3.3 established that the only single-point escape left is a `d`-side function
with Wiener norm `≳ √p`. Such functions exist (the DLP character has `‖·‖_A ≳ √p` in the coordinate
basis) but are not known to be **cheap**. To *construct* a cheap one you would have to know the
spectrum you are trying to match.

> **⇒ A closed form for `V(a)` is the prerequisite for the only construction §3.3 leaves open.**
> Not a break — the enabling structural input for the one door that stayed open.

That is a genuine link between the structural half and the leakage half of this record, and as far as
I have read, it is not on file. It also explains why D2's second clause is worth as much as its first.

### 3.3 The intermediate question, which is cheap

**Is `a ↦ θ_a` arithmetically structured?** Equidistribution does **not** answer this — the `mean|u|`
match to Sato–Tate is consistent with `θ_a` being both equidistributed and highly structured. Four
tests, all cheap, all decidable at `p ≤ 10³`:

1. **Spacing statistics** of the sorted `{θ_a}` against the Katz–Sarnak prediction for the symmetry
   type (this is §4 below, converging).
2. **Autocorrelation** of `θ_{a+1} − θ_a`.
3. **Multiplicativity:** does `V(a)V(b)/V(ab)` (or `V(a+b)`) behave like a Jacobi-sum relation? A
   Hecke character would show here immediately.
4. **Factorization:** `V(a) ∈ ℤ[ζ_n]` — is its ideal factorization structured? **This is a third
   target for the Stickelberger port** already named in the brainstorm §5, and Stickelberger is
   exactly the tool that gives exact ideal factorizations of Gauss/Jacobi sums. ⚠ inherits (D2-cite):
   the Stickelberger citation is still unverified after three failed `citation-verifier` runs.

---

## §4 — Porter–Thomas is one of five statistics; four were never measured

The record's thermodynamic layer rests on `|T|²` intensities being **Porter–Thomas** `[EMPIRICAL,
p ≤ 2089]`, plus a transfer-operator `|λ₂|` decay. Porter–Thomas is the **intensity distribution** —
one of the standard random-matrix statistics. The others were never measured:

| statistic | measured here? |
|---|---|
| intensity distribution (Porter–Thomas) | **yes** |
| level spacing (Wigner surmise) | no |
| spectral rigidity `Δ₃` | no |
| number variance `Σ²` | no |
| two-point correlation | no |

And the record **cites Katz–Sarnak**, which supplies exact predictions per symmetry type — so the
correct nulls are available and were not used. This is the same shape as brainstorm §4.2 (a Rayleigh
null where a symmetry-type null was available) and §4.3 (mean statistics where the phenomenon is
tail-shaped): **an instrument-class gap, not a data gap.**

The natural object to apply them to is `{θ_a}` — which makes §3.3(1) and this the same experiment.

---

## §5 — Farey (1D) and rhombus (2D) are the two quotients' reduction theories

I generated this and dropped it as "loose", which is precisely the prefiltering I was asked to
suspend. Stated properly it is not loose:

- **Reduction of `x` into the rhombus** = reduction mod a rank-2 lattice in `ℤ[ω]` = **2-dimensional
  continued fractions.** `eis`, sextants, the flap, `σ` all live here.
- **The `k_den` level sets = the primitive Farey comb**, the `T=1` stratum `= {⌊lo/q⌋}` = the Dirichlet
  hyperbola — **1-dimensional continued fractions.** `[VERIFIED exactly + derivable]`, and recorded as
  **d-side only, no curve enters it.**
- The two-quotient frame says coordinates live in `ℤ[ω]/(π_p)` and scalars in `ℤ[ω]/(π_n)`.
  **⇒ the Farey comb and the rhombus are the same ring's two quotients, carrying the 1D and 2D
  reduction theories respectively.** "d-side only, no curve enters it" is then a statement about
  *which quotient*, not about *whether there is structure*.

Three live ledger items sit on this and none of them says it:

- **#19** — curve-side image of the `T=1` Dirichlet island lattice;
- **#22** — the `T=2` stratum, and whether a nested reciprocal lattice `⌊lo/q₁⌋ ± ⌊lo/q₂⌋` sits inside
  `T ≤ 2` (`max T = 2` verified only to `7×10⁵`);
- **#24** — *which* cycles carry the `~3×` `β₁` excess, "organised by Stern–Brocot depth / the
  continued-fraction tree?" — a **location** test.

`[MINE — speculative, no measurement]` **The probe:** `T` counts terms in the 1D reciprocal-lattice
representation and is bounded by 2. Is there a 2D analogue on the coordinate side, and is *it*
bounded? The flap has measure exactly `¼` and the frame-operator anisotropy is exactly `¾ − ½ = ¼`.
Whether `max T = 2` and the flap's `¼` are the same phenomenon in two dimensions is decidable: define
the 2D reciprocal-lattice term count and measure its maximum. **Falsifier:** the 2D count is
unbounded, or bounded by something with no relation to `¼`/the sextant count.

---

## §6 — secp is the reduction of a global curve, and the other project already studied it

Compressed to a one-line literature pointer in the write-up. The framing is the valuable part.

`E` is ordinary with CM by `ℤ[ω]`, so it is the reduction mod `p` of the **global** curve
`y² = x³ + 7` over `ℚ`. Consequences that are classical, not new, but not used here:

- `t = 432420386565659656852420866390673177327` is the `p`-th **Fourier coefficient of an explicit CM
  newform of weight 2**, i.e. `t = ψ(π) + ψ̄(π)` for a Hecke character `ψ` of `ℚ(ω)`.
- For `y² = x³ + D`, the classical formula for `#E(F_p)` runs through the **sextic residue character
  and Jacobi sums** (Ireland–Rosen Ch. 18).
- **⇒ the record's empirically-found `m`-law and `ε = ζ₆^{3−[28/π]₆}` are the sextic-symbol factor of
  that Hecke character.** Not a guess about the literature — a specific, checkable identification.
  Check `ε` against the classical formula's symbol directly.

**★ Cross-project connection nobody has made:** the sibling project `secp256k1_arithmetic/` already
did **BSD on this same curve** — `L(1)/Ω = Ш = 1`, clean (thread D of
`secp256k1_arithmetic_v4.md`). **The global object is on disk in another folder and the curve-structure
work has never cited it.** The Hecke character, the newform, its `L`-function and its special value
are all determined there.

Also worth stating: the lift geometry (rhombus, `¾`, `⅛:⅛`, angle law, norm band) is the
**archimedean** geometry of `ℤ[ω] ⊂ ℂ`, while the curve arithmetic is at `p`. The record has been
computing archimedean invariants of the CM lattice and finding they govern finite-field statistics —
which is *why* the "continuum-proved" laws work at all, and is the honest description of what
"`[PROVED — continuum; VERIFIED at small p]`" means.

---

## §7 — The trichotomy: exactly three things can beat `√p`

Every null in this record — island jointset/GLV, flap group-law/density, `ℓ≥5` bridges, conditional
MI, LBE, D1 affine lift, structured pairs, ARM 4 — bottoms out at a `√p/n ≈ p^{−1/2}` character-sum
barrier. The record has rediscovered one barrier through many instruments. Classically, a character
sum beats `√p` in exactly three ways:

| route | status here |
|---|---|
| **(a) multiplicative degeneracy** — sums over subgroups/cosets | **BLOCKED: `n` is prime.** (And this is `P14` prime-order rigidity, already `[PROVED]`.) |
| **(b) incomplete sums** — a special/short range | **UNTOUCHED** — brainstorm §4.1, zero grep hits |
| **(c) family moments with a main term** — individual sums stay `√p`, the family average has structure | **PARTIALLY** — the 2nd moment is forced and carries no information; `E[u⁴]` (brainstorm §1.5) is the first real instance |

Naming the trichotomy is the point: **(a) is closed by a theorem, and the entire remaining
single-point frontier is (b) and (c).** That is a much sharper statement of where the record stands
than "many nulls at many floors", and both live routes now have a named first move.

---

## §8 — Forced non-questions (this section vanished from the write-up)

Do not spend a run on these.

- **Descent does not move the bridge.** `(B1)` is a statement about `p` and `n` only; a 3-isogenous
  descendant has both. Nothing to test.
- **The CRT map `z ↦ (z mod π_p, z mod π_n)` is not the curve map `d ↦ x_d`.** If it were, the DLP
  would be a linear congruence.
- **An anomalous member of a longer aliquot cycle would not help.** Even if some twist's chain reached
  a curve with `#E(F_q) = q`, the amicable correspondence carries **no homomorphism** (`Hom = 0`,
  coprime orders), so no DLP transfers. Worth checking the cycles for structure; not as an attack.
- **`Φ: d ↦ dlog_Ẽ(x = d)` intertwines `μ₃` automatically.** If `d = x(P)` then `β·d = x([λ']P)` by
  GLV on `Ẽ`. A confirmed `μ₃`-intertwining of `Φ` is **zero information**; only higher structure
  would mean anything.
- **`E[u²]` is forced by Parseval** ⇒ it carries no monodromy information. Only `E[u⁴]` and above do.
- **Weil descent / GHS** needs `F_{q^m}`, `m>1`; embedding `E(F_p)` in an extension and descending
  returns a curve over `F_p`. Blocked.
- **Tate–Lichtenbaum on `E(F_p)/nE(F_p)`** is trivial: `E(F_p) ≅ ℤ/n` exactly, so the quotient is `0`.
- **Non-abelian torsion covers do not exist here.** For a CM curve the mod-`ℓ` Galois image lies in the
  normalizer of a Cartan ⇒ every torsion-level cover is essentially abelian ⇒ Kummer or
  Artin–Schreier ⇒ **already inside the two families the record has bounded.** There is no third
  cover family at torsion level to hunt for.

---

## §9 — The remaining recovered items

### 9.1 CM index calculus, and a non-Fourier statistic on short vectors

The multi-point door **is** the index-calculus door: a `k`-point readout is a `k`-dimensional character
sum with square-root cancellation *unless the variety degenerates*, and the natural degenerate
varieties are the summation-polynomial ones (`Σ P_i = O` ⟺ `Σ d_i ≡ 0`) — Semaev, item 4.

Factor-base candidates from the lift geometry (flap, sextants, norm bands) have **density `Θ(1)`** —
far too large. Shrinking via the norm band `s < δ` gives `|{x : N(eis x) < δp}| ≈ (2π/√3)δ·p`, so
`δ ~ p^{−1/3}` gives a set of size `~p^{2/3}` with **cheap membership**. It is `μ₆`-stable
(`eis(βx) = ω·eis(x)`), which yields the known factor-6 and nothing more, and `eis` is not a
homomorphism so the set has no group-law structure.

`[MINE — speculative]` **The one statistic worth building:** decompose in `ℤ[ω]` rather than `ℤ` (GLV
already does this), and measure the **joint distribution of `(N(z), N(eis(x([z]P))))` over short
`z ∈ ℤ[ω]`.** This is (i) a short-vector family, so brainstorm §4.1 applies and **no character-sum
bound covers it**, and (ii) a joint distribution, not a Fourier correlation, so §4.3 applies too.
It is the natural bridge between the two untouched regimes, and it asks the two-quotient question in
its sharpest form: *does the ideal-lattice structure of the scalars talk to the coordinate lattice?*

### 9.2 The exact `±` rows are exactly `b = 0`

Worked out mid-cycle and discarded with its conclusion. For `g ∈ μ₆` to satisfy
`(bx+cy)∘g = −(bx+cy)`:

- `g = [−1]` (`x` fixed, `y ↦ −y`): gives `bx − cy`, which equals `−(bx+cy)` **iff `b = 0`**;
- `g = [λ]` (`x ↦ βx`, `y` fixed): forces `c = 0` and `b(β+1) = 0` ⇒ trivial only.

**⇒ the rows carrying an exact odd symmetry are exactly `b = 0, c ≠ 0` — the pure-`y` rows, which are
exactly the `V(a)` rows**, the ones with the forced `α ↦ −ᾱ` pairing. Consistent, and it says the
`±`-pairing structure is confined to the `χ₂(y)` channel. So the `±`-pairing story is **not** an
explanation for a low-tail excess spread over general `(b,c)` — which is a reason to prefer the
wrong-null hypothesis (brainstorm §4.2), and worth recording so the `±` idea is not re-proposed.

### 9.3 `3 | f` is probably not forced

`4p = t² + 3f²`, `f = 3·79·349·2698097·(91-bit)`. Is `3 | f` forced by `n` prime?

Mod 3: `p ≡ 1` ⇒ `4p ≡ 1`. If `3 ∤ f` then `t² ≡ 1`, so `t ≡ ±1`. With `n = p+1−t ≡ 2−t`:
`t ≡ −1 ⇒ n ≡ 0 mod 3`, impossible for prime `n > 3`. So **`t ≡ 1 mod 3` is forced** — and that is
consistent with `3 ∤ f`. **⇒ `3 | f` is not forced by prime order; it looks like a draw.**

Consequence: secp's `End = O_3` descendant — the whole volcano-descent direction, and the
`(8+√37)/16` frame — **exists contingently, not structurally.** Worth confirming with a count over
primes before either direction is invested in.

### 9.4 Two small structural statements

- **The formal group is as linear as `μ₆` allows.** `μ₆ ⊆ Aut` forces the log's exponents `≡ 1 mod 6`,
  so the first possible nonlinearity is at `T⁷`, and it is there: `R^(2) = T + 3T⁷`, coefficient
  `b·C(3,1)/7 = 3b/7`, integral exactly because `b = 7`. The `7` in the ASD congruence
  `7^k C(3k,k) ≡ a_ℓ` is the same `b`.
- **`ν₂(n−1) = 6 = |μ₆|`** — noted and half-dismissed. It is what makes `ord_n(2) = (n−1)/64` a
  selection effect, and it is the `64` in the `(X·Y) mod 64 → D mod 64` shadow (brainstorm §2.3). Two
  sixes; whether they are the same six is exactly what the cross-curve test in §2.3 decides.

---

## §10 — What changes in the ranking

Additive to brainstorm §6; the previous eight stand.

| new # | move | why | cost |
|---|---|---|---|
| **1′** | **§2.5 — the `a = 0` deformation path** (untwisted eigenvalues, then track `a`) | answers **D2** (prereg on file, never run), supplies **item 12**'s missing discriminator, and gives the cap a second independent mechanism. **Three ledger items, one measurement, instrument already written.** | low |
| **2′** | **§2.3 — read `ζ`'s order at M17's own 7 primes** | decides whether `k=3`, the 120° law, and item 12 are one fact measured three times | trivial |
| **3′** | **§3.3 — is `a ↦ θ_a` structured?** (spacing, autocorrelation, multiplicativity, ideal factorization) | D2's untouched second clause; §3.2 makes it the prerequisite for the one open construction | low |
| **4′** | **§4 — the four unmeasured RMT statistics on `{θ_a}`** | same experiment as 3′(1); the correct Katz–Sarnak nulls are already cited and were never used | low |
| **5′** | **§6 — check `ε` against Ireland–Rosen's sextic symbol; pull in `secp256k1_arithmetic/`'s BSD work** | the global Hecke character is the parent of the `m`-law, and the sibling project already computed it | low |
| **6′** | **§5 — the 2D reciprocal-lattice term count vs `max T = 2` and the flap's `¼`** | items 19/22/24 share a frame nobody has stated | medium |
| **7′** | **§9.1 — `(N(z), N(eis(x([z]P))))` on short `z`** | the only statistic that is simultaneously short-vector **and** non-Fourier | medium |

---

## §11 — What this document does not claim

No grade moves. §2's chain rests on the 120° law, which is `[VERIFIED — exact]` at 8–10 primes and
**not derived**, and on `N2`, which is `[VERIFIED 24/24]` and not proved in dimension 2. §2.3 is a
connection to check, not a derivation — I have not verified the relation between `ord_ℓ(p)` and `ζ`'s
order. §3.1, §3.2, §5, §9.1 are hypotheses with no measurement behind them. §9.3's mod-3 argument is
one line of arithmetic that has not been independently checked, and "looks like a draw" is a
prediction, not a count.

**Everything recovered here was generated in the previous session and lost in the write-up.** The
lesson is not about any one item: **the compression step is where this project loses things, and it
loses the open-ended items preferentially.** That is what `DEGRADATION_AUDIT_H3_TO_MASTER_v1.md`
documents at scale, and a tag count of the document I wrote would not have caught any of it.
