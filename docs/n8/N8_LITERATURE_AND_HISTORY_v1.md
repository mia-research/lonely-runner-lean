# Where n = 8 Sits — the Literature, and the Version History

**T. Palelei.** Documentation file, v1, 2026-09-18. Companion to `N8_PROOF_v9_3_DOC_v1.md`.

Two things this set otherwise lacks: what is already known about the Lonely Runner Conjecture and
how this framework relates to it, and how the manuscript reached its present state.

---

## 1. The conjecture

Eight runners start together on a circle of circumference 1 at distinct constant speeds. At `n`
runners the conjecture asserts each runner is, at some instant, at circle distance at least `1/n`
from every other.

**Two conventions, and they collide.** Much of the literature states the problem with a **stationary
runner and `k` non-zero speeds**, separation `1/(k+1)`. So "`k = 7`" in that convention is
**eight runners**. This framework holds no runner still and counts runners, so `n = 8` here is
`k = 7` there. The Lean tree follows the runner count: `intLRC 8` is `Fin 7` speeds at bound `1/8`.

---

## 2. What is known, order by order

| order | status in the literature | status in this project's Lean tree |
|---|---|---|
| 3, 4, 5 | classical | **axiom-clean**, `[propext, Classical.choice, Quot.sound]`, zero `sorry` |
| 6 | classical (BHK 2001) | **axiom-clean**, complete 2026-06-25, including both Proposition 11 cores |
| 7 | **Barajas–Serra 2008** — the largest case with a proof that is **not** computer-assisted | **axiom-clean**, complete 2026-09-07, no `native_decide` |
| **8** | **Rosenfeld 2025**, by computer verification. **No analytic proof is known** | this framework: Construction and Localisation proved; **Existence open** |
| 9–13 | the computational line, Rosenfeld and co-authors, then Sungkawichai–Trakulthongchai 2026 | not attempted |
| general `n` | open | the general-`n` programme, separate lineage |

**The relevant fact about this framework's position:** at eight runners there is a proof, and it is a
computation. What does not exist is an analytic one. That is the gap this framework addresses, and
Existence is the part of it still open.

---

## 3. Rosenfeld 2025 — what it actually does

*The lonely runner conjecture holds for eight runners*, arXiv:2509.14111, submitted 17 September
2025, revised 16 October 2025. Reviewed from the PDF at `docs/n8/ROSENFELD_REVIEW_v1.md`.

**Theorem 1.** For all sets of integers `{v₁, …, v₇}` of size 7 there exists a real `t` such that for
all `i`, `‖t·vᵢ‖ ≥ 1/8`. This is exactly `intLRC 8`.

**The architecture, in six steps.**

1. **Theorem 2** (cited, Malikiosis–Santos–Schymura): if the conjecture holds for `k`, it holds for
   `k+1` for every `k`-tuple with `gcd = 1` and a gcd-sum exceeding an explicit bound.
2. **Corollary 3** (AM–GM on Theorem 2): a counterexample must have **bounded product** —
   for `k = 7`, `∏vᵢ < 7.4 × 10⁵⁴`.
3. **Lemma 4** (elementary): `lcm(2, …, k+1)` divides `∏vᵢ` for any set without the lonely-runner
   property.
4. **Lemma 5**: a gcd condition, assuming the conjecture for `k−1`.
5. **Lemmas 6 / 7** (the engine): for a given prime `p`, a **finite** condition over tuples implies
   `p` divides `∏vᵢ` for every non-lonely-runner set. Lemma 7 is the set-cover reformulation
   actually computed.
6. **The contradiction**: verify Lemma 7 for 27 primes `{31, 37, …, 163}`; then `∏vᵢ` is divisible by
   an lcm of about `1.82 × 10⁵⁵`, exceeding the bound of step 2. No counterexample exists.

**Two points of contact with this project.**

- **Rosenfeld's n = 8 proof is conditional on the conjecture at seven runners** — Lemmas 5 and 6 both
  assume it — which is precisely the result this project has machine-verified and axiom-clean.
- **The computation is large.** Verifying Lemma 7 for the single largest prime `p = 163` takes
  roughly **32 hours** on one core, in C++ with bitsets and four backtracking optimisations. It is
  not reachable by the kernel-`rfl` technique that carried the n = 7 work, and pruned backtracking
  is exactly what kernel reduction cannot exploit. **Formalising the computation as-is is not on the
  table by the present method.** The analytic scaffolding — steps 1–5 — is ordinary mathematics and
  is formalisable.

**Rosenfeld's own stated open direction**, §7: "There might even be a good provable reason for which
Lemma 6 holds for all `k`, for any large enough integer `p`. That could lead to a proof of the lonely
runner conjecture." Proving that would make `k = 7` computer-free, hence mechanisable, and would
attack all `k` by one argument.

**The exception pattern is the falsification test.** Empirically, for `k = 3, 4, 5` every prime
larger than 7, 17, 23 respectively appears to work; for `k = 6`, every `p > 31` and also 13 and 19,
but **not** 17, 23, 29; for `k = 7`, every `p ≥ 31` **other than 41**. Any proposed proof of the
large-`p` statement must predict those exceptions, and they are cheap to reproduce.

**Two corrections recorded against an automated summary of the paper**, so neither propagates: the
speeds need **not** be pairwise coprime (the only normalisation is `gcd = 1`, which is without loss
of generality), and the minimal-counterexample bound is **Malikiosis–Santos–Schymura**, not Cusick
1973.

---

## 4. How this framework differs from the known proof

Not a claim of superiority — a statement of what the two do.

| | Rosenfeld 2025 | this framework |
|---|---|---|
| what it establishes | **no counterexample exists** at eight runners | for each runner, **an instant** at which it is lonely |
| method | a minimal-counterexample bound, plus a prime search closing a contradiction | a determinator fixed by the speeds, run from `1/(8·d_min)` |
| frame | a stationary runner and seven non-zero speeds | no runner pinned; each of the eight read against the others |
| conditional on | the conjecture at seven runners | nothing at another order |
| the computation | 27 primes, ~32 hours for the largest | exact rational arithmetic; the census is decidable arithmetic |
| status | complete | Construction and Localisation proved; **Existence open** |
| formalised | not by the present method | every proved link, axiom-clean, no `sorry` |

**The type difference matters more than the method difference.** An existence proof concludes that
some point survives; this construction names which. That is why the objections in
`N8_WHY_OTHER_ROUTES_FAIL_v1.md` §3.1 record covering and candidate-counting as inapplicable *by
type* rather than as merely unsuccessful.

---

## 5. References

**Barajas, J. and Serra, O. (2008).** *The lonely runner with seven runners.* Electronic Journal of
Combinatorics **15**, R48. — seven runners; the largest case with a proof that is not
computer-assisted. Verified in this project's Lean tree, axiom-clean.

**Rosenfeld, M. (2025).** *The lonely runner conjecture holds for eight runners.* arXiv:2509.14111,
submitted 17 September 2025, revised 16 October 2025. — eight runners by computer verification, with
bounds on a minimal counterexample. States the problem with a stationary runner and seven non-zero
speeds.

**Sungkawichai, T. and Trakulthongchai, T. (2026).** *Eleven, twelve, and thirteen lonely runners.*
arXiv:2604.23906, submitted 26 April 2026, revised 1 September 2026. — extends the computational line
to `k ∈ {10, 11, 12}` non-stationary speeds, thirteen runners, building on the method of Rosenfeld
and the second author, which had reached `k ≤ 9`.

**Palelei, T. (2026).** *The φ(n) Law for Arithmetic Progressions in the Lonely Runner Conjecture:
Algebraic Structure and Computational Fragility.* Working paper v1.0, 4 January 2026. Zenodo, DOI
**10.5281/zenodo.18158886**. — Theorem 3.1(a)–(b), the instants of perfect isolation for a
progression and their count. **No longer cited as a dependency**: derived in Lean at general `n`
from the framework's own objects.

**Malikiosis, R.-D., Santos, F. and Schymura, M.** — the minimal-counterexample bound Rosenfeld's
Theorem 2 cites. **Not obtained or verified by this project.** It is load-bearing for Rosenfeld's
argument and is currently `[CITED]`, not verified.

---

## 6. Version history of the manuscript

### 6.1 The shape of it

| version | date | what it was |
|---|---|---|
| v7 | — | the first-window construction: two families, evaluation confined to `u ∈ [1/8, 7/8]` |
| v8 | — | the window withdrawn; the cascade stated; the three outcomes |
| v8.1, v8.2 | 2026-09-15 | Appendix C (objections), §2.3 (the AP fit), lap-and-phase |
| v9, v9.1 | 2026-09-15 | redraft against two audits (54 + 17 findings); flanks added |
| v9.2 | 2026-09-17 | Propositions 6.10–6.11 stated, ruling pending |
| **v9.3** | 2026-09-17 | **6.10–6.11 withdrawn.** The body documented in `N8_PROOF_v9_3_DOC_v1.md` |
| v9.4 | 2026-09-17 | Theorems 6.12–6.13 |
| v9.5 | 2026-09-18 | Theorem 6.14; the digest defect corrected |
| **v9.6** | 2026-09-18 | **the target amended** to an arrangement. Manuscript of record |

### 6.2 v7 → v8, the consequential transition

This is where the framework's most damaging imported restriction came out.

| v7 | v8 | reason |
|---|---|---|
| §1.3, the first-window target | removed; §1.3 states the cascade | the framework does not confine the evaluation |
| §1.2 "a cell is settled by its two ends" | withdrawn; decided by an interior point | counterexample |
| §1.1, §2.2 unconditional exactness | exact for commensurate speeds; real band test otherwise | the method is real-valued |
| §5 external debt | §5 **no** external dependency | the `φ(n)` instants derived in Lean |
| §7.4, the Claim | §6: the cascade; Existence, open | **the Claim is refuted as written** by `(1, 31, 75, …, 225)`, runner 1, lonely at `9/40` in lap 6. Its wording stopped the cascade at lap 0 |
| §7.4 settled-cases table | §4.5 | relabelled "settled at once" rather than "reach" |
| references: "the two formulations agree by the standard reduction" | removed | nothing uses a reduction to a stationary runner |
| — | §4.6, §2.3, Appendix C | gap migration; the AP fit (open); the objection ledger |

**The pattern the transition exposed.** v7's confinement to the first lap was not a property of the
framework but a restriction imposed on it, and every coverage figure v7 reported — 81.9%, 66.0%,
86.8% — was a statement about that window rather than about the construction's reach. Four further
restrictions of the same kind were found afterwards: `p ∈ {1,3,5,7}`, the lap in the output contract,
`a ≡ 1 (mod 8)`, and `D ∈ ℤ`.

### 6.3 v8.2 → v9, the audit redraft

v8.2 was frozen and audited twice — an isolated audit (54 findings) and an own audit (17). v9 was
redrafted against both; the compile-diff before promotion found **0 findings unaddressed** and all 22
carried numbered results present at the same grade. v9.1 restored seven small losses the redraft had
dropped and removed six contradictions it had introduced, most of them symbol collisions
(`ρ`, `q`, `m`, now separated as `z`, `κ`, `w`, `b`, `ρ_j`).

Notable rulings from that pass:

- `R < 4` at order 5 is **not** the obligation — it is a stronger sufficient statement, and it is the
  first window in disguise. Order 5 is stated open.
- Bounds on **when** an instant falls are not requirements of any result, so the maxima are reported
  without a conjecture attached.
- The instant for runner 2 of `(1, 1 + √2/100, 3, …, 8)` was corrected: the cascade gives
  `(497/8)/(7 − √2/100)` after two moves, and `75√2/4` is a **later** lonely instant. The earlier
  wording contradicted Theorem 6.2(b).

### 6.4 v9.3 → v9.6

Covered in full in `N8_PROOF_v9_3_DOC_v1.md` §D. In summary: **Existence at order 8 did not move.**
What moved is what the obligation is *stated on* (a disparity set became an arrangement), how much of
the search is provably *finite* (Theorems 6.13, 6.14), and how many equivalent *doors* onto it are
machine-checked. No grade was promoted.

### 6.5 What the history is kept for

Superseded versions are frozen and header-stamped, never edited, and withdrawn propositions get a
retraction record rather than a deletion. Two reasons, both recorded in the project's own rules: a
version is the record of its own moment, and a claim that was once made and then dropped is exactly
the thing a reader needs to be able to find.
