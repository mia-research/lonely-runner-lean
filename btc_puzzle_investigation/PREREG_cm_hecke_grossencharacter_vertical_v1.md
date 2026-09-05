# PREREG v1 — the CM-type Hecke Grössencharacter as the VERTICAL forcing of the 120° law

**Date:** 2026-08-21. **Status: SPEC ONLY — NO confirmatory computation performed.** This file freezes
the object, the single decidable artifact, the anti-tautology construction, the matched/firing
controls, exactness, power, scope, and falsification for the CM-Hecke (vertical) mechanism BEFORE any
Grössencharacter is evaluated, any charpoly is factored p-adically, or any split-prime match is run.
Nothing runs until this file is frozen (SHA-256 alongside) and the frame gate returns on *this* file.

This spec is the object-level probe that `PREREG_omega_twisted_lefschetz_120deg_v1.md` §9 named and
left to a separate pre-registration, after establishing (pre-data, decidably) that the [ω]-twisted
Lefschetz point-count is NOT an object-level test of the vertical mechanism (R1 forced-zero on the
orbit-summed null; R2 ill-defined on a single fibre; R3 circular). Read that file for the obstruction;
this design does not reuse its statistic.

**SCOPE BANNER (binding).** Output is a STRUCTURAL characterization ONLY: does a p-INDEPENDENT
CM-type / Hecke-Grössencharacter input exist for `E: y²=x³+7` and force `ρ(a)=α₂/α₁=ζ₃` uniformly over
`a∈(ℤ/N)*`. This is a statement about CM-type, infinity-type, conductor, and Frobenius eigenvalue
structure. It MUST NEVER be reported as, or bridged to, scalar extraction, "carry bounds," key
recovery, or any ECDLP / security consequence. The map from eigenvalue/CM structure to any scalar `d`
is a separate, unbuilt object, explicitly OUT OF SCOPE here. Both terminal outcomes — mechanism
SUPPORTED and mechanism REFUTED-or-ABSENT — are positive, scoped results. No dismissal vocabulary.

Grades: `[PROVED]` exact identity, all p in the class · `[REPRODUCED-exact]` exact, finite sample as
stated · `[VERIFIED-exact]` exact single/finite instance · `[CITED]` external · `[OPEN]` not shown ·
`[FORCED]` algebraically forced ⇒ zero information · `[STRUCTURAL]` p-independent, established on the
endomorphism/idele side (not by a finite prime sample).

---

## 1. OBJECT

`p` prime, `p ≡ 7 mod 12` (⊇ secp; forces `ω=ζ₃∈F_p`, `p≡3 mod 4`, so `χ₂(−1)=ε=−1`); `E: y²=x³+7`;
`N=#E(F_p)` prime, `N≡1 mod 3`. For `a∈(ℤ/N)*` the rank-4 lisse sheaf `F_a = L_{χ₂(y)}⊗L_{χ_a}` on
`E` minus its tame points; `dim H¹_c=4`; Frobenius eigenvalues `α₁(a),…,α₄(a)`, Weil weight 1
(`|α_i|=√p`); `L*_a(T)=∏(1−α_iT)`. `ρ(a)=α₂(a)/α₁(a)`; the "120° law" is `ρ(a)=ζ₃=ω`.

**The object of THIS test is not the ratio abstractly, nor a max over cells. It is the rank-2 ORDINARY
UNIT-ROOT motive `U_a` of `H¹_c(F_a)` (Newton slopes `{0,0}`) and its CM-type / Hecke-character
structure.** Aiming the artifact at `U_a` is aiming it AT the predicted subspace, for a decidable
reason established below: the ω-ratio lives entirely inside `U_a`.

**Neutral established facts (given; NOT re-derived here).**
- (Per-cell law) `[REPRODUCED-exact, p≤211, all cells]` multiset `{α, ωα, −ᾱ, −ω̄ᾱ}`; `ρ=ω`; `g=2`.
- (ω-descent, horizontal) `[PROVED]` `V_k(a)=V_k(λa)` ∀k ⇒ `L*_a=L*_{λa}=L*_{λ²a}` as polynomials,
  `λ∈(ℤ/N)*` of order 3 = the action of `[ω]:(x,y)↦(ωx,y)` on `E(F_p)≅ℤ/N`. This is HORIZONTAL
  (moves cell `a→λa`, fixes `a` only at `a=0`); it reduces the per-`p` work to one orbit representative
  per orbit but supplies NO base case — the open content is a single orbit representative (obstruction
  analysis §3).
- (Newton polygon, a≠0) `[VERIFIED-exact, p=43, a=1]` slopes `{0,0,1,1}` — ORDINARY. Within each
  ι-pair `{α,−ᾱ}`, `v_𝔭(α)+v_𝔭(−ᾱ)=v_𝔭(p)=1`: one unit, one non-unit; the ω-partner shares its
  source's valuation (`ω` a unit). **Hence the two UNIT roots are `{α, ωα}` and the two non-unit roots
  are `{−ᾱ, −ω̄ᾱ}`.** `⇒ ρ=ω is EXACTLY "the two unit roots differ by ω," i.e. a statement about `U_a`
  alone.` This is why `U_a` is the object.
- (Newton polygon, a=0) `[CITED — record L1/v2]` `A_new` at `a=0` is SUPERSINGULAR, slopes
  `{½,½,½,½}`, eigenvalues `√p·{ω,ω²,−ω,−ω²}` (ζ₂₄ exps {4,8,16,20}). **There is NO {0,0} unit-root
  part at a=0.** `0∉(ℤ/N)*`, so a=0 is outside the open quantifier — AND outside the target's
  Newton-polygon regime. (This tension is load-bearing for the firing control; see §4.)
- (CM field) `[VERIFIED — Sage]` `End(E)=ℤ[ω]`; `p` SPLITS in `ℚ(ω)` as `𝔭·𝔭̄`, `π_E` a generator of
  `𝔭` with `N(π_E)=p`; `p` is INERT in `ℚ(ζ_N)`. So the classical Stickelberger framing over `ℚ(ζ_N)`
  is mis-specified (`ANALYSIS_n1_120deg_stickelberger_misspecified_v1.md`); the CM/Hecke story lives
  over `ℚ(ω)` where `p` splits.

**OPEN quantifier (the target):** `ρ(a)=ω` for ALL `a∈(ℤ/N)*`, ALL `p≡7 mod 12`, to `p≈2²⁵⁶`.

**Hypothesis (CM-Hecke vertical mechanism), decomposed into three checkable sub-objects.**
- **CM-i** (endomorphism side): the ordinary unit-root motive `U_a` (slopes `{0,0}`) carries CM by an
  order in a field `K ⊇ ℚ(ω)` — i.e. `ℤ[ω]=End(E)` embeds in `End_{F_p}(A_new)` and acts on `U_a`.
- **CM-ii** (Hecke value): the unit-root Frobenius is `ψ(𝔭)=ψ₀(𝔭)·χ_a`, where `ψ₀` is a Hecke
  Grössencharacter of `K` with an **infinity-type and conductor that are data INDEPENDENT of `p`**, and
  `χ_a` is the finite-order twist carrying ALL the `a`-dependence.
- **CM-iii** (ω-forcing / uniformity): the CM-type — the action of `ω∈ℤ[ω]` on the split prime `𝔭` —
  forces the two unit-root eigenvalues to be `ψ(𝔭)` and `ω·ψ(𝔭)`; since `χ_a` cancels in the ratio,
  `ρ=ω` holds at every split prime and every `a` simultaneously (that cancellation IS the uniformity).

---

## 2. STATISTIC (exactly one) and its distribution under the null

**The statistic is a DECIDABLE EXACT EQUALITY of algebraic data, per split prime — not a fit, not a
z-score, not a max over cells.**

Per split prime `𝔭=(π)` (`p≡7 mod 12`) and per `a≠0` orbit representative:

> `S(𝔭,a) := [ U_a(T) == (T − ψ(𝔭))·(T − ω·ψ(𝔭)) ]`   (exact equality in the CM ring, see §8)

where
- `U_a(T)` = the degree-2 UNIT-ROOT factor of the exact charpoly `f_a(T)=∏(T−α_i)` over `ℤ_p`,
  extracted by exact Newton-polygon / Hensel factorization to p-adic precision `p^M` (§8). Computed
  from exact point counts `V_1..V_4` by a code path that NEVER references `ω`, `ρ`, or `ψ`.
- `ψ(𝔭)=ψ₀(𝔭)·χ_a` = the PREDICTED unit-root value, with `ψ₀`'s infinity-type + conductor DERIVED
  from the CM/ramification data of `(E,F_a)` (§ anti-tautology, requirement 2 below), evaluated
  exactly as an ideal generator in `ℤ[ω]` normalized by the root-of-unity the conductor fixes.

The verdict per prime is the Boolean `S(𝔭,a)`. Because the prediction is an UNORDERED set match
`{unit roots} == {ψ(𝔭), ω·ψ(𝔭)}`, `S` simultaneously tests CM-ii (unit roots ARE Hecke values) and
CM-iii (they differ by ω) WITHOUT ever labelling "which root is α₁" — closing the labelling-circularity
door (both unit roots have `v_𝔭=0`, so nothing but the ratio could order them; the set match needs no
order).

**CM-i is a separate, prior, endomorphism-side gate (§ requirement, below), decided WITHOUT eigenvalue
data.** `S` is only evaluated on objects that pass CM-i.

**Distribution under the null.** The matched null is a curve/branch on which no `ℚ(ω)`-CM forces the
ratio (§3). Under that null the predicted set `{ψ₀(𝔭), ω ψ₀(𝔭)}` (if the ω-forcing were manufactured)
does NOT match the measured unit roots — `S` is FALSE. Under the mechanism, `S` is TRUE at every
tested split prime. `S` has no continuous distribution; it is an exact Boolean per prime, so the null is
"expected FALSE unless the mechanism holds."

**Primary (STRUCTURAL) artifact — the uniformity tier.** Per-prime `S` gives refutation power but a
finite set of TRUE `S` values does NOT prove uniformity (a p-dependent formula can match finitely many
primes; §5). The uniformity claim is decided by EXHIBITING `ψ₀` as a genuine Hecke character: a
p-independent `(infinity-type, conductor 𝔣)` verified to be a character of the ray class group
`Cl_𝔣(K)` on a generating set (finite reciprocity check). IF `ψ₀` is exhibited AND its CM-type gives
the ω-scaling, uniformity in `p` is a definitional consequence (a Hecke character is not attached to
one prime). The per-prime `S` values are then firing/consistency checks (§4) and the refutation
instrument (§9). **Tier A (exhibit ψ₀) is the SUPPORT verdict; Tier B (per-prime S) is the REFUTATION
verdict.**

---

## 2R. ANTI-TAUTOLOGY (requirement 2 — mandatory, decided pre-run)

The failure mode to prevent (the one that sank the twisted-Lefschetz probe): read `ρ=ω` off the
eigenvalues, then "derive" a character engineered to output `ω`, then confirm. This design forbids it
by **deriving every input of `ψ₀` from data disjoint from the eigenvalue ratio, and pinning `ψ₀` before
any unit root is looked at.**

- **CM field `K` and its embedding:** from `End(E)=ℤ[ω]` and the μ₃-cover geometry (`π:E→P¹_y`,
  `(x,y)↦y`, Galois `⟨[ω]⟩`; `L_{χ₂(y)}=π*M`), NOT from eigenvalues. `p`-independent.
- **Infinity-type of `ψ₀`:** fixed by the WEIGHT (weight 1, `|α_i|=√p`, Weil purity — `[FORCED]`) and
  the Hodge/CM-type of the unit-root motive read off the μ₃-cover monodromy. It is the integer datum
  `(1,0)` on the relevant CM embedding. Derived from purity + cover, NOT from `α₂/α₁`.
- **Conductor `𝔣`:** from the RAMIFICATION of `F_a` — the tame points of `E`, the ramification of the
  Lang-torsor `χ_a`, and the `χ₂(y)` branch locus. Geometric ramification data, `p`-independent, NOT
  from eigenvalues.
- **`χ_a`:** the finite-order twist; its order and conductor come from `E(F_p)≅ℤ/N` and the frequency
  `a`, NOT from eigenvalues. It carries ALL `a`-dependence and CANCELS in the ratio.

**The ω-prediction (CM-iii) is DERIVED, not read off.** `ω·ψ(𝔭)` as the second unit root is a
consequence of `ω∈ℤ[ω]` acting on `𝔭` through the CM-type (a structural fact about how the endomorphism
`ω` permutes/scales the two 𝔭-adic eigenlines of `U_a`), established on the endomorphism side. It is
NOT obtained by measuring `α₂/α₁`. **Circularity trip-wires (any ⇒ redesign):**
1. If fixing `(infinity-type, 𝔣, χ_a)` requires the measured value `α₂/α₁`, the test is circular. It
   must not — all four inputs above are eigenvalue-free.
2. If "the CM-type forces `ω`" is asserted by DEFINING the two eigenlines as `α` and `ω·α`, it is
   vacuous. The eigenlines must be identified by an eigenvalue-ratio-independent label (the `ℤ[ω]`- /
   Frobenius-module structure of `U_a`), and only THEN the ω-relation checked — or, as `S` does, the
   UNORDERED set match avoids the labelling entirely.
3. If `ψ₀(𝔭)` is "computed" by first taking a unit root `α` and setting `ψ₀(𝔭):=α`, that is the
   identity map, not a prediction. `ψ₀(𝔭)` must be the ideal-generator evaluation of the pinned
   character, computed by a code path that never reads `U_a`.

**Disjointness statement (binding):** the PREDICTION path (`ψ₀` from CM/ramification/purity →
`ψ₀(𝔭)·χ_a` → predicted set) and the MEASUREMENT path (`V_k` point counts → `f_a` → Newton
factorization → `U_a`) share NO intermediate and NO input beyond `(E, p, a)`. Enforced by requiring two
separate functions with disjoint inputs, mirroring the `m_chi4` discipline of
`PREREG_mu4_eigenvalue_individual_v1.md` §5.

---

## 3. MATCHED CONTROLS (each destroys exactly ONE ingredient; all decided pre-run)

The matched null must reproduce every structure the real object has EXCEPT the one being tested. Three
controls, each removing a single ingredient of CM-i/ii/iii:

- **(MC-a) Generic-`j` NON-CM curve** (e.g. `y²=x³+ax+b`, `j≠0,1728`, `End=ℤ`). Destroys CM entirely.
  Prediction: **CM-i must FAIL** — no `ℚ(ω)` (indeed no imaginary quadratic) embeds in `End`, no CM
  Hecke character of a CM field exists. If the CM-detection step "succeeds" here, the detector is
  broken and NO verdict may be issued. Preserves: rank-4 sheaf shape, purity, the `L_{χ₂(y)}⊗L_{χ_a}`
  construction. Destroys: the CM field.
- **(MC-b) `j=1728` curve** `y²=x³+Ax` (`End=ℤ[i]`, CM by `μ₄`, NOT `μ₃`). Destroys `μ₃`, substitutes
  `μ₄`. Prediction: the machinery yields a `ℚ(i)`-Hecke character whose CM-type forces the **μ₄**
  eigenvalue relation (cf. the recorded μ₄ law, `PREREG_mu4_eigenvalue_individual_v1.md`), NOT an
  ω-ratio. The ω-set-match `S` must **FAIL** (there is no ω-scaling); an `i`-scaling appears instead.
  If the ω-forcing appeared here, the derivation is reading `ω` from something other than the CM field
  — tautology. Preserves: CM, split prime, weight-1 purity. Destroys: the μ₃ CM-type. (Recorded
  structural fact: `j=1728` has 2-torsion `(0,0)`, never prime order — arm exists only as the
  μ₄-vs-μ₃ discriminator, never as a secp-setting analog.)
- **(MC-c) `m=−2` cubic-RESIDUE branch of the SAME curve `E`** (a=0 anchor, `B=7` a cubic residue mod
  the relevant `p`; anchor multiset `√p·{1,1,−1,−1}`, orders `[1,1,2,2]`, `g=0`). Right curve, right
  CM field `ℚ(ω)`, but the cubic class kills the ω-ratio. Prediction: the CM-type here gives eigenvalue
  ratio `±1`, so the **ω-scaling (CM-iii) must be ABSENT** — `S` against `{ψ₀,ωψ₀}` must FAIL, while a
  match against `{ψ₀,+ψ₀}` / `{ψ₀,−ψ₀}` (no ω) holds. If the ω-forcing were present in BOTH the `m=1`
  (non-residue) and `m=−2` (residue) branches, the "CM-type forces ω" claim would be vacuous.
  Preserves: curve, CM field, split prime. Destroys: the ω-branch of the CM-type.

**A shuffle / random-gluing surrogate is an INVALID null here** and is not used: it would destroy the
ω-descent isomorphism the object has by definition (the logged "shuffle breaks the artifact as it
breaks real signal" failure), so it cannot expose the tautology `2R` guards against. The matched nulls
are structural (different curve / different branch), each preserving the forced symmetries and removing
exactly one CM ingredient.

---

## 4. FIRING (PLANTED) CONTROLS — with the regime tension disclosed

A positive control must inject a KNOWN CM-Hecke structure and fire. **The a=0 anchor alone is
INSUFFICIENT because it is in a DIFFERENT Newton-polygon regime than the target** (a=0 supersingular,
slopes `{½,½,½,½}`, NO `{0,0}` unit-root part; target a≠0 ordinary, slopes `{0,0,1,1}`). Relying on a=0
alone would be "a plant that fires only outside the object's regime" — a documented failure mode.
Therefore TWO firing controls, and the disclosure of what each can and cannot fire:

- **(FC-1, PRIMARY — ordinary regime) The curve `E: y²=x³+7` ITSELF.** `E` is a CM elliptic curve,
  ORDINARY at `p≡1 mod 3` (⊇ `p≡7 mod 12`), with a classical Hecke Grössencharacter `ψ_E` of `ℚ(ω)`:
  infinity-type `(1,0)`, conductor a known divisor (textbook, `[CITED — Deuring/Weil CM theory]`), and
  `ψ_E(𝔭)=π_E` (a generator of `𝔭`). The machinery MUST: derive `(infinity-type, conductor)` of `ψ_E`
  from `E`'s CM data by the SAME code that will be applied to `U_a`, evaluate `ψ_E(𝔭)` exactly in
  `ℤ[ω]`, and confirm `π_E+π̄_E = p+1−#E(F_p)` (`#E(F_p)` by exact point count, a disjoint path). This
  fires the `(∞-type, conductor)→ordinary-Frobenius` pipeline in the SAME regime as the target. **If
  FC-1 does not fire, the pipeline is broken; NO verdict may be issued.**
- **(FC-2, SECONDARY — supersingular regime) The a=0 anchor.** At a=0 the eigenvalues `√p·{ω,ω²,−ω,−ω²}`
  are classical supersingular Gauss/Jacobi sums = values of a Weil Jacobi-sum Grössencharacter
  (`[CITED]`). The machinery predicts these exactly (by exact reduction in `ℤ[x]/Φ₂₄`, per the standing
  rule that a pasted root system was previously wrong — DERIVE, do not paste). **Disclosure:** FC-2
  fires the "Frobenius = Hecke-character value" pipeline (CM-ii) and the CM-i endomorphism claim
  (`ℤ[ω]↪End` holds at a=0 too), but it CANNOT fire the ordinary-unit-root claim CM-i-slopes-`{0,0}`,
  because that object is VACUOUS at a=0 (no `{0,0}` part). So FC-2 is a Gauss-sum consistency control,
  not a test of the ordinary machinery — that role is FC-1's.

**Consequence for the verdict (decided now):** a SUPPORT verdict requires FC-1 (ordinary pipeline) to
fire AND `ψ₀` to be exhibited as a genuine Hecke character (Tier A, §2). FC-2 firing alone licenses no
a≠0 conclusion. This mirrors the twisted-Lefschetz finding that a plant firing only outside the target
regime cannot validate the target — but here FC-1 supplies a plant INSIDE the ordinary regime, so the
null is NOT rendered uninformative (the reason this probe is admissible where the Lefschetz one was not).

---

## 5. POWER

- **CM-i (endomorphism side):** `[STRUCTURAL]`, decidable with power 1 at every `p`. `[ω]` is an
  `F_p`-automorphism of `E` for all `p≡1 mod 3`; whether it induces `ℤ[ω]↪End_{F_p}(A_new)` acting on
  `U_a` is a geometric fact computable from the cover, essentially `p`-independent. A non-CM control
  (MC-a) must fail it; power to distinguish CM from non-CM = 1.
- **CM-iii refutation (per-prime `S`):** power 1 to REFUTE at any reachable split prime — a single
  `S(𝔭,a)=FALSE` (measured unit-root ratio ≠ ω) is an exact, decidable falsification. No `n`, no
  averaging, no threshold.
- **Uniformity SUPPORT (Tier A):** a finite set of `S=TRUE` values does NOT prove uniformity to `2²⁵⁶`
  — a `p`-dependent rule can match any finite prime set (this is the standing "finite sample ≠ all p"
  limit, and the exact reason per-prime matching is NOT the support artifact). Uniformity is supported
  ONLY by EXHIBITING `ψ₀` as a genuine Hecke character (a finite reciprocity check on ray-class-group
  generators mod `𝔣`), which is `p`-independent by construction. Power for uniformity therefore lives
  entirely in the Tier-A exhibition, not in the prime count.
- **Reachable primes (exact computability).** `U_a` needs `V_1..V_4` (counts over `F_{p^k}`, `k≤4`),
  exact by integer enumeration at `p ≲ 10³–10⁴` (cost `~p⁴`), or larger via Jacobi/Gauss-sum evaluation
  of the `V_k` character sums (`~O(p)` per sum) and via CM. `ψ₀(𝔭)` and `ψ_E(𝔭)` are exact ideal-
  generator computations in `ℤ[ω]` at ANY `p` that splits (including secp's `p`, for consistency only).
  At each reachable split prime, ONE orbit representative gives ONE decisive `S`. Expected decisive
  primes: dozens–hundreds of `p≡7 mod 12` below the enumeration bound. secp's own `p` may be used ONLY
  for `ψ₀(𝔭)`/`ψ_E(𝔭)` consistency, NEVER as the sole evidence and never for an `a≠0` point count.

---

## 6. SCOPE (every number this run would print inherits this string)

```
E: y²=x³+7 (j=0, CM by ℤ[ω]); primes p ≡ 7 mod 12 (ε=χ₂(−1)=−1);
a ∈ (ℤ/N)*, one orbit representative per ⟨λ⟩-orbit (ω-descent covers the orbit);
U_a = ordinary unit-root (slopes {0,0}) rank-2 factor of H¹_c(F_a);
p ≲ 10³–10⁴ for exact V_k point counts (larger via Jacobi-sum evaluation);
ψ₀, ψ_E evaluated exactly in ℤ[ω] at split 𝔭 (any p incl. secp, consistency only).
Controls: MC-a generic non-CM j; MC-b j=1728 (ℤ[i]); MC-c m=−2 cubic-residue anchor of E;
FC-1 E itself (ordinary); FC-2 a=0 anchor (supersingular).
```
Any number this design could produce inherits one of: "`[STRUCTURAL]` CM-i endomorphism fact",
"`[VERIFIED-exact]` per-prime `S` at the named `𝔭`", or "`[STRUCTURAL]` ψ₀ exhibited as a Hecke
character". It may NEVER be stated as an `a≠0` uniformity result to `2²⁵⁶` unless Tier A is met, and
NEVER bridged to ECDLP/scalar/key recovery (SCOPE BANNER).

---

## 7. EXACTNESS

- Point counts `V_1..V_4` exact over `F_{p^k}` (integer enumeration or exact Jacobi/Gauss-sum
  evaluation); charpoly `f_a∈ℤ[T]` from exact `e_1..e_4`.
- Newton-polygon / Hensel extraction of `U_a(T)` done in `ℤ/p^M` (exact integer arithmetic mod `p^M`),
  `M` fixed BEFORE the run large enough that the degree-2 algebraic-integer factor is uniquely pinned
  (`p^M > 2·(coefficient bound ~ 2√p·|unit|)`; the explicit `M` is frozen in the run script, not chosen
  after seeing coefficients). NO float p-adic routines.
- `ψ₀(𝔭)`, `ψ_E(𝔭)`, `ω`, and root-of-unity memberships by EXACT reduction in `ℤ[ω]` / `ℤ[x]/Φ_k`
  (`k∈{3,6,12,24}`), NEVER a numeric root-finder. The a=0 anchor multiset and any CM-type root system
  are DERIVED by exact reduction in `ℤ[x]/Φ₂₄` (standing rule: a pasted root system in a related slot
  was WRONG — derive, do not repeat).
- The verdict `S(𝔭,a)` is an exact equality of polynomials over `ℤ/p^M` (equivalently of algebraic
  integers in `ℤ[ω]`); NO float threshold decides any verdict. `check_no_float.sh` must pass before any
  computation.
- No float carve-out is needed; none is taken. (If a numeric value is printed for orientation it is
  labelled `informational, not used for any pass/fail`, per the mu4 prereg discipline.)

---

## 8. THE DECIDABLE ARTIFACT (assembled, restated for the auditor)

For each split `𝔭` (`p≡7 mod 12`) and `a≠0` orbit representative, after CM-i passes and FC-1 fires:

1. MEASURE (disjoint path): `V_1..V_4` → `f_a(T)` → Newton factorization mod `p^M` → `U_a(T)∈(ℤ/p^M)[T]`.
2. PREDICT (disjoint path): `(∞-type,𝔣)` of `ψ₀` from CM/ramification/purity (eigenvalue-free) →
   `ψ₀(𝔭)·χ_a` → predicted set `{ψ(𝔭), ω·ψ(𝔭)}` reduced mod `p^M` via `ℚ(ω)↪ℚ_p` at `𝔭`.
3. VERDICT: `S(𝔭,a) = [ U_a(T) == (T−ψ(𝔭))(T−ω·ψ(𝔭)) ]`, exact.

TIER A (uniformity): EXHIBIT `ψ₀` as a genuine Hecke character (`(∞-type,𝔣)` verified a character of
`Cl_𝔣(ℚ(ω))` on generators). If exhibited AND its CM-type gives the ω-scaling, uniformity in `p`
follows by definition of a Hecke character.

---

## 9. PRE-COMMITMENT + FALSIFICATION (filled BEFORE the run)

| # | Outcome | Pre-committed conclusion |
|---|---|---|
| 0 | FC-1 does not fire (machinery fails to reproduce `ψ_E`/`π_E` on `E`) OR MC-a "detects CM" on a non-CM curve | **Pipeline broken / detector uninformative.** Output = the disagreement only. NO verdict on CM-i/ii/iii. |
| 1 | CM-i FAILS: `U_a` (equiv. `A_new`) carries NO CM by a field `⊇ℚ(ω)` (endomorphism side) | **Mechanism REFUTED at CM-i.** `[STRUCTURAL]`. Redirect: the ω-ratio is not CM-forced; pivot to a monodromy (`L-mono`) or ideal-factorization (`L-Stick over ℚ(ω)`) mechanism. NOT a closure of the 120° question. |
| 2 | CM-i holds; some reachable split `𝔭` (a≠0 rep) has `S(𝔭,a)=FALSE` (measured unit-root ratio ≠ ω) | **Mechanism REFUTED at CM-iii**, at that `𝔭`. Report the `(𝔭,a)` and the measured `U_a` vs predicted set. `[VERIFIED-exact]`. Redirect, not closure. |
| 3 | CM-i holds; `S(𝔭,a)=TRUE` at all tested split primes; `ψ₀` NOT exhibited as a genuine Hecke character | **Consistent, uniformity UNPROVEN.** `[VERIFIED-exact per prime; OPEN for uniformity]`. Report as consistent at the named primes; state explicitly that finite matches do not give `p`-independence (§5). Next step: attempt the Tier-A exhibition. |
| 4 | CM-i holds; `S=TRUE` at all tested primes; `ψ₀` EXHIBITED as a genuine Hecke character with the ω-scaling CM-type | **Mechanism SUPPORTED; uniformity in `p` follows** `[STRUCTURAL]` (a Hecke character is not per-prime). Report ∞-type + conductor + the reciprocity check. Still `[STRUCTURAL]`, NOT bridged to ECDLP (SCOPE BANNER). |
| 5 | MC-b (`j=1728`) shows an ω-forcing (same ω-set-match succeeds there) | **Anti-tautology tripwire: ω is being read from outside the CM field.** The derivation is circular; HALT and redesign `2R`. |
| 6 | MC-c (`m=−2` residue branch) shows the ω-scaling present | **CM-iii is vacuous** (ω "forced" in a branch whose ratio is `±1`). HALT and redesign. |

**FALSIFICATION (of the CM-Hecke mechanism), decided pre-run.** REFUTED if EITHER (i) the unit-root
part carries NO CM by a field `⊇ℚ(ω)` (outcome 1), OR (ii) there is a split prime `𝔭` (a≠0 orbit rep)
where the exactly-computed unit roots are not `{ψ(𝔭), ω·ψ(𝔭)}` — i.e. `α₂≠ω·α₁` (outcome 2).
SUPPORTED if a `p`-independent infinity-type + conductor is exhibited as a genuine Hecke character
whose CM-type forces `α₂=ω·α₁`, and whose `ψ₀(𝔭)` matches at every tested split prime (outcome 4).
Both are informative and reported with power+scope and no dismissal vocabulary: a refutation REDIRECTS
(to `L-mono` or `L-Stick over ℚ(ω)`); it does NOT close the 120° uniformity question, which remains
`[OPEN]` in that event.

---

## 10. Freeze / deviations

Freeze = SHA-256 of this file (in `PREREG_cm_hecke_grossencharacter_vertical_v1.md.sha256`). Any
departure from this spec is logged in `PREREG_cm_hecke_grossencharacter_vertical_v1_DEVIATIONS.md`,
opened at freeze. NO confirmatory computation is run under this task; this file is SPEC ONLY.
