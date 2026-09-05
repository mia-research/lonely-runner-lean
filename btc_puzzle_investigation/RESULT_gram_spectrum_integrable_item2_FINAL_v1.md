# RESULT — ITEM 2 FINAL: the `|T(a,b)|²` operator is INTEGRABLE. The RMT battery is answered in closed form.

**Date:** 2026-08-01. **Script:** `gram_spectrum_exact_v1.py`.
**Grade: `[PROVED]`** — derivation plus exact numerical verification at 6 primes (agreement `1e-11`).
**Supersedes** the transfer-operator detour in `RESULT_rmt_battery_on_spectrum_item2c_v1.md` as the
answer to *this* question.

## 0. What I did wrong, and it is the more serious of the two

I derived this spectrum analytically, saw it was perfectly degenerate, concluded *"no room for RMT
level statistics to emerge"* — and **changed the object**, running the battery on an unrelated
324-state Markov operator instead, finding nothing, and closing the item.

**A perfectly degenerate spectrum is not an obstacle to the answer. It IS the answer.** Discovering
that the operator underlying the intensities has a two-point, integrable spectrum mathematically
*precludes* Wigner–Dyson repulsion and `Δ₃` rigidity — which is the strongest possible result the
battery could return, in the strongest direction. I discarded a closed-form algebraic constraint
because it made my script unusable.

## 1. The derivation

`T[b,a] = Σ_d e_p(b·x_d)·e_n(a·d)`. With `M[b,d] = e_p(b·x_d)` and `F[d,a] = e_n(a·d)` (`FF* = nI`):

> `T = M·F` ⇒ **`T T* = n·(M M*) =: n·H`** — all spectral content lives in the Gram operator `H`.

`H[b,b'] = Σ_d e_p((b−b')·x_d) = c(b−b')`, so **`H` is CIRCULANT**, with eigenvalues

`μ_k = Σ_m c(m) e_p(−km) = Σ_d Σ_m e_p(m(x_d − k)) = p·#{d : x_d = k}`.

`d` runs over `1…n−1` (the identity has no `x`-coordinate); `n` odd ⇒ no rational 2-torsion ⇒
`x³+Ax+B` has **no root** in `F_p` ⇒ every `x`-coordinate is shared by exactly the two points
`(x, ±y)`. Hence `#{d : x_d = k} = 1 + χ₂(k³+Ak+B)` and

> ### `μ_k = p·(1 + χ₂(k³ + Ak + B))`, taking ONLY the values `2p` and `0`.
> multiplicity of `2p` is exactly `(n−1)/2`; of `0`, exactly `p − (n−1)/2`.
> Hence `spec(T T*) = {2np with multiplicity (n−1)/2, 0 otherwise}`.

## 2. Verification

| p | n | circulant | ‖eig − closed form‖ | # distinct eigenvalues | spectrum | mult(2p) = (n−1)/2 |
|---|---|---|---|---|---|---|
| 127 | 127 | 1.7e−12 | 1.2e−11 | **2** | 254×63, 0×64 | YES |
| 163 | 139 | 1.7e−12 | 1.4e−11 | **2** | 326×69, 0×94 | YES |
| 211 | 199 | 3.4e−12 | 2.7e−11 | **2** | 422×99, 0×112 | YES |
| 349 | 313 | 6.4e−12 | 7.5e−11 | **2** | 698×156, 0×193 | YES |
| 397 | 397 | 7.7e−12 | 9.8e−11 | **2** | 794×198, 0×199 | YES |
| 433 | 397 | 1.0e−11 | 1.3e−10 | **2** | 866×198, 0×235 | YES |

`x³+7` has zero roots at every prime tested, as `n` odd requires.

## 3. The RMT battery, answered

- **Level spacing / Wigner surmise:** every gap is `0` or `2p`. **No level repulsion — the spectrum
  is maximally degenerate.** There is no spacing distribution to compare to Wigner.
- **`Δ₃` spectral rigidity:** the counting function is a **two-step staircase**; `Δ₃` is fixed by the
  two multiplicities alone and has no fluctuation content.
- **`Σ²` number variance:** likewise determined by `(n−1)/2` and `p − (n−1)/2`.

**The operator is integrable, not chaotic.** This is a `[PROVED]` structural statement, not an
empirical null, and it holds at every prime with `n` odd — including secp256k1.

## 3b. The sharper consequence — the singular spectrum is BLIND TO THE GROUP LAW

`H[b,b'] = Σ_d e_p((b−b')·x_d)` sums over `d`, so it depends only on the **multiset** `{x_d}` and is
invariant under **arbitrary permutation of the index `d`**. Since `T = M·F` with `FF* = nI`, the whole
singular spectrum of `T` inherits that invariance.

**Verified:** re-ordering `d` by random permutations leaves the spectrum fixed to `2e-13`, while
`|T|` itself changes by 2–3× its own mean (p = 127, 163, 211).

> **Every statistic built from the spectrum / singular values of `T` is provably incapable of
> distinguishing the curve's group ordering from a random shuffle of it.** The `d`-dependence — the
> only place discrete-log information can live — is carried **entirely by the singular vectors**.

This is the operational content. It is a `[PROVED]` blindness result: object = the singular spectrum
of `T`; class = every function of the singular values; power = exact, by invariance; scope = all `p`,
`n` odd. It closes a channel by theorem rather than by a scoped null, and it says where to look
instead (the eigenvectors, not the spectrum).

## 4b. The specific label this corrects

`masked_structure_findings_v18.md:24` infers from the bounded intensity tail:
*"(bounded max ≈ 8×, sub-exponential) = spectral rigidity, the GUE/critical signature."*

**Spectral rigidity is a property of a spectrum, and this spectrum is two-valued** — the opposite
pole from GUE rigidity. The tail measurement is fine; the label attached to it is not, and the
inference "GUE/critical signature" does not follow from it.

That file's conclusion — *"no scar, no condensed mode … hunting magnitude structure is closed"* — is
**correct, and is now strengthened**: the magnitude/spectral layer is blind to `d` by theorem, not by
absence of evidence. **The record reached the right conclusion by the wrong route; it now has a proof
instead of a heuristic.**

## 4c. What this is NOT — stated to prevent the opposite error

- **Not deep.** The derivation is four lines and elementary; the degeneracy is forced by `M` being
  additive characters evaluated on a 2-to-1 multiset. Anyone who asked "what is the spectrum?" would
  have it in an afternoon. Its value is that nobody asked.
- **It removes a bounded channel:** statistics that are functions of the singular values ALONE.
  ⚠ **RETRACTED from an earlier draft: "not a leak, and not a step toward one."** That is an
  unbounded claim about all future compositions, with no object/class/scope — the exact overclaim
  this project's closure-grade rule forbids, written one line after correctly meeting that bar.
  I cannot know how an exact algebraic identity will compose. §4d names four ways it already might.
- **Does not touch** the Porter–Thomas result (a statement about entries, which stands), the Koopman
  operator (a different object), or anything at `2^256` beyond the hypothesis `n` odd.

## 4. What this clarifies about the record's thermodynamic layer

`masked_structure_findings_v18.md` reads the `|T(a,b)|²` intensities as Porter–Thomas and calls the
object *"thermal … quantum-chaotic … CUE-random in phase beyond its single conserved charge `μ₆`"*.

**Both can hold, and the distinction matters:** Porter–Thomas describes the distribution of the
**entries** of `T`; the Gram **operator** is provably integrable. So the intensity marginal looking
thermal does **not** license an operator-level chaos reading. Any inference of the form *"the
spectrum is GUE/rigid, therefore …"* does not survive §1 — the spectrum is two-valued.

## 5. Status of the transfer-operator run

`RESULT_rmt_battery_on_spectrum_item2c_v1.md` remains valid **as a statement about a different
object** — the coarse-grained Koopman operator of `P → P+G`, whose full spectrum the record had
never examined (it pulled only `|λ₂|`). Its battery result (NULL at 10 primes, plants firing at
`z = +15…+343`) stands on its own terms. It is **not** the answer to the `|T(a,b)|²` question, and
it is relabelled accordingly.

## 6. Method note

**Do not discard an exact algebraic constraint because it makes a statistical test inapplicable.**
When the mathematics forces a degenerate outcome, the degeneracy is the measurement. Changing the
object to keep a script runnable is how a definitive structural result gets converted into a null
about something else.


## 4d. Concrete ways this composes — so the retraction is not abstract

**(i) `T` annihilates the odd subspace, exactly.** The `d`-side Gram is
`M*M = p·(I + J)`, `J` = the negation permutation `d ↦ −d` — verified to `0.00e+00`, and
`rank(T) = (n−1)/2` exactly. The forced-oddness that has silently mis-specified **five or more**
probes on this project (the parity pre-screen) is therefore not a heuristic: it is the **kernel of an
explicit operator**. Any future probe's parity obstruction can be read off `ker(T) = odd`.

**(ii) `μ_k = p(1 + χ₂(k³+Ak+B))` is a bridge, not a wall.** Anything that later needs the curve's
Legendre sequence *as a spectral object* now has an exact operator realisation of it.

**(iii) Exact rank deficiency of exactly one half.** A hard algebraic constraint that interacts with
any low-rank, bilinear or lattice framing built on `T`.

**(iv) A provably permutation-invariant quantity is an ideal instrument control.** Any statistic that
*ought* to be blind to the group ordering can be validated against it. The record already has this
pattern — the proved cap `|V| ≤ 2√p` "earning its keep as an instrument check."

## 4e. A second over-statement in the same result

"The `d`-dependence lives **entirely in the singular vectors**" is also too strong. `T*T = p·F*(I+J)F`
is likewise explicit and forced, so **both** singular eigenspaces are degenerate and determined; what
actually carries the `d`-dependence is the **pairing** (the isometry) between the two degenerate
eigenspaces, not either factor's vectors. Corrected.

## 6b. The pattern worth recording

Twice in this result I bounded the finding correctly and then, in the very next sentence, attached an
unbounded closure to it. **The closure reflex does not attack the graded claim — it attaches to the
sentence after it**, where no one is looking for a grade.

---

# ADDENDUM — the technique generalises, and it closes a whole layer

## A1. General theorem (elementary, exact)

For any object of the form `H(k,a) = Σ_d c(d)·φ_k(d)·e_n(a·d)` — a readout `c` times a phase family
`φ_k` — the Gram over the `a`-index is

`G[k,k'] = Σ_a H(k,a)·conj(H(k',a)) = n·Σ_d |c(d)|²·φ_k(d)·conj(φ_{k'}(d))`.

> **If `|c(d)| = 1`, the readout cancels identically. The singular values of `H` do not depend on `c`.**

Every readout in this project is unimodular (`χ₂`, `χ₃`, `χ₆`, sextant, `eis`). Therefore:

> ### The singular-value layer of every readout × phase object is READOUT-INDEPENDENT.
> No statistic built from it can distinguish the curve from noise — by identity, not by power.

## A2. Verified on the record's own escape hatch

The chirp plane `H(k,a) = Σ_d χ₂(y_d)·e_n(kd² + ad)` was built specifically to escape the Weil
closure (`RESULT_chirp_hologram_plane_v1.md`). Its Gram is `G[k,k'] = n·Σ_d e_n((k−k')d²)` — a
quadratic Gauss sum, so `G` is circulant with eigenvalues `n²·#{d≠0 : d² = j}`:

> `spec = {2n² with multiplicity (n−1)/2, 0 with multiplicity (n+1)/2}` — **exactly two-valued again.**

| p | n | circulant | spectrum measured | predicted |
|---|---|---|---|---|
| 823 | 829 | 2.8e−08 | 1374482 × 414, 0 × 415 | `2n²=1374482` × 414, 0 × 415 |
| 1051 | 1093 | 3.4e−08 | 2389298 × 546, 0 × 547 | `2n²=2389298` × 546, 0 × 547 |
| 1303 | 1249 | 2.2e−07 | 3120002 × 624, 0 × 625 | `2n²=3120002` × 624, 0 × 625 |

**And curve-independence, measured:** the spectrum for the real curve, for a random `±1` sequence,
and for all-ones agree to `4e−09` against a scale of `1.4e+06` — **15 orders of magnitude.**

Note this is *stronger* than the `|T(a,b)|²` case: there the eigenvalues at least encoded
`χ₂(x³+Ax+B)`; here they encode nothing but quadratic residuosity **mod n**, and are the same for
any unimodular weight whatsoever.

## A3. Scope — what is and is not closed

**Closed, by identity:** any statistic that is a function of the **singular values** of a
readout × phase object. Object, class, power (exact), scope (all such objects, all unimodular
readouts) all named.

**NOT closed:** the **entries** `|H(k,a)|` — which is what the chirp-plane work actually measured
(beams, maxima, the `k=0` dark fringe). Those depend on `c` and are untouched. Also untouched: phase
structure, and everything outside the singular-value layer.

## A4. The standing pre-screen this yields

> **Never build a statistic from the singular values / spectrum of a readout × phase object.**
> It cannot see the readout. This is checkable in one line (`is |c| ≡ 1?`) and is strictly stronger
> than the parity pre-screen, which only rules out sign-cancellation.

Remaining cheap sweep: apply the same Gram diagonalisation to the other 2-D objects in the record
(the interval sum/difference sets, the joint-SET objects, `C_T`) to map which of their layers are
provably blind **before** spending measurement on them.
