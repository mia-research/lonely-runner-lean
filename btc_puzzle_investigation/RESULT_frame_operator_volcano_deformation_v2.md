# RESULT v2 — CORRECTION of v1: one strawman retracted, one restatement re-scoped, the descendant claim de-rated

*2026-07-24. Supersedes `RESULT_frame_operator_volcano_deformation_v1.md`. Triggered by a self-audit
(the word "Honest" in the hand-off flagged a claim the evidence was not carrying). Three corrections
below; each was checked against the record's actual text or re-derived, not reread. Curve/CM/lattice
geometry; no leakage / key-recovery / ECDLP claim.*

---

## 0. Summary of what changed

| v1 claim | status in v2 |
|---|---|
| §3 "`¾` is not a hexagonal fingerprint; recommend annotating M10" | **RETRACTED — strawman.** M10 makes no converse claim. |
| §1 "the `½` is pure symmetry" (framed as a result) | **RE-SCOPED.** M10 already states it; v2 keeps only the added *reason*. |
| §2 descendant frame operator `≈ 0.88` at `ℓ=3` | **DE-RATED** from `[DERIVED — UNVERIFIED]` to `[CONJECTURE — two unstated assumptions]`. |
| §0 crater fact; §2 exact `L_ℓ` lattice values | **STAND** (but §0 is a restatement of a known Part IV fact). |

---

## 1. RETRACTION — the "hexagonal fingerprint" caveat was a manufactured issue

v1 §3 wrote: *"Master Part V calls `¾` 'θ-independent lattice geometry' … any claim of the form
`¾ ⟹ hexagonal structure` is too strong … Recommend annotating M10."*

**M10 makes no such claim.** Its actual text (`POSITIVE_FINDINGS_MASTER_v4.md:173`):
> "`λ_max/Tr` is exactly ½ on the μ₃-core … and **¾ on the full lift**"

and Part V (`:346`): "**¾ on the full lift** (uniform 60° rhombus, diagonal ratio `√3:1`, θ-independent)."
Both state **hexagonal rhombus ⟹ ¾** — the correct direction. **Neither asserts the converse
`¾ ⟹ hexagonal`.** I invented the converse, refuted it with the `ℓ=2` rectangle, and framed the
refutation as "sharpening the record." That is the manufactured-issue failure mode
(CLAUDE.md §3; [[feedback_verify_external_critiques_2026_07_17]]: refuting a mechanism ≠ refuting a
claim — here I refuted a claim that was never made).

**What is true and kept, without the framing:** the `ℓ=2` reduced cell is a `1:√3` rectangle and its
uniform second moment also has `λ_max/Tr = ¾` `[VERIFIED — exact]`. This is a genuine coincidence of two
distinct lattices at that one statistic. It **does not contradict M10** and warrants **no** edit to the
record. It is filed as a lattice curiosity, nothing more.

## 2. RE-SCOPE — the `½`-is-symmetry point is M10's, not mine

M10 states the `½` with its mechanism already attached: *"(exact-integer isotropy test: a 120°-symmetric
point set has `C ∝ I`)."* v1 §1 re-presented this as an established finding. **The fact that `½` is a
μ₃-isotropy statement is the record's, not a contribution here.**

**The only new content, kept and correctly scoped:** M10 supports the isotropy by an *exact-integer
check at tested `p`*; the representation-theoretic *reason it is forced* is that the 2-D real
representation of `C₃` is irreducible, so by Schur the only invariant symmetric 2-tensor is scalar. This
upgrades M10's `½` from `[exact at tested p]` to **`[PROVED — forced, scale-free]`** for any
μ₃-symmetric set. That is a modest promotion of an existing row, not a new law. `[VERIFIED — μ₃-symmetrized
cloud gives `C = c·I` exactly.]`

## 3. DE-RATE — the descendant number rests on two unstated assumptions

v1 §2 gave `λ_max/Tr ≈ 0.88` at `ℓ=3` and called the descendant application `[DERIVED — UNVERIFIED]`.
That grade was too generous. The step "a conductor-`ℓ` descendant curve's frame operator equals the
`L_ℓ` reduced-cell ratio" assumes **both**:

- **(a) the lattice.** A descendant with `End = ℤ + ℓℤ[ω]` has CM by that order, but its period lattice
  is some **ideal class** of the order — not necessarily the *principal* lattice `ℤ + ℓℤ[ω]` I used.
  Different ideals in the class group have **different shapes**, hence different `λ_max/Tr`. I did not
  determine the class. (For `ℓ = 3` the order `ℤ+3ℤ[ω]` has class number `> 1` in general, so this is a
  real gap, not a formality.)
- **(b) equidistribution.** That the descendant's eis points fill that cell uniformly — the record's
  *empirically established* model at `ℓ = 1`, here **assumed**, not checked, at `ℓ > 1`.

**⇒ `≈ 0.88` is not a prediction about any curve.** It is the exact ratio of the *principal* lattice
`ℤ+3ℤ[ω]`, and whether a real 3-isogenous descendant realises it is **open on two counts.** Re-graded
**`[CONJECTURE]`**.

## 4. What actually stands

- **§0 crater fact `[PROVED, but a restatement].** Every `j=0` curve has `[ω] ∈ End` ⇒ `End = ℤ[ω]`
  maximal ⇒ secp at the crater. Correct and full-scale — **but the maximality is already Part IV's
  `[PROVED]`, so "at the crater" is a rephrasing, not new ground.**
- **§2 exact lattice values `[VERIFIED — exact algebraic]`, as statements about lattices only:**
  `λ_max/Tr` of the reduced cell of `ℤ+ℓℤ[ω]` is `¾ (ℓ=1)`, `¾ (ℓ=2, a 1:√3 rectangle)`, `½+√37/16
  (ℓ=3)`, `½+√13/8 (ℓ=5)`, `→1 (ℓ→∞)`. Re-derived `ℓ=3` by hand: reduced basis lengths² `(1,7)`,
  `C ∝ [[5/4,−3√3/4],[−3√3/4,27/4]]`, tr `8`, det `27/4`, eigs `(8±√37)/2`, ratio `(8+√37)/16`. ✓.
  These are correct **and carry no curve claim.**
- **§1 promotion of M10's `½` to forced/scale-free `[PROVED]`** — the one real, if modest, contribution.
- The observation that Cap Law / flap / `ε` / sextant are **defined via the μ₃ β-action and so have no
  form on a `β`-free descendant** — correct, and nearly tautological. Kept as an observation, not
  starred.

## 5. Net assessment, corrected

The volcano probe's genuine yield is: **(i)** M10's `½` is now *proved* forced (not just checked), and
**(ii)** the exact reduced-cell ratios of the orders `ℤ+ℓℤ[ω]`. Everything I framed as "the lift-geometry
programme is a crater phenomenon, the frame constants deform, `¾` isn't a fingerprint" was some mix of
**restatement, conjecture, and a strawman**. The single decidable next step remains — and it is the thing
that would make any of the descendant talk real:

> Build a 3-isogenous descendant `E'` at a small crater prime, **determine its actual period-lattice
> ideal class**, compute its eis, and measure `λ_max/Tr`. Only then is there a curve statement. Until
> then §2 is lattice arithmetic and §3's `0.88` is a conjecture with a named gap.

---

*Grades: §1 `[PROVED — forced]` (rep theory) + `[VERIFIED]`; §2 `[VERIFIED — exact, lattices only]`;
§0 `[PROVED — restatement of Part IV]`; §3 descendant value `[CONJECTURE]`. v1's §3 caveat and its
"annotate M10" recommendation are **withdrawn**.*
