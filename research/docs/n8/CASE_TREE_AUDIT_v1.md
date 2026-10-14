# The n=8 case tree is not exhaustive — and the shape split is an artefact

2026-09-10. Scripts `experiments/n8/ok_shapes_v1.py`, `ok_treecover_v1.py`,
`ok_uncovered_hard_v1.py`. Answers the question "are (H′) and (NR) the right targets".
**Short answer: not first.**

---

## 1. The finding  `[PROVED — enumeration]`

A tuple's leaf is fixed by its multiset of residues mod 8. Enumerating multisets rather
than tuples is box-free. Of the **3312** realisable size-7 residue multisets (gcd 1 needs
one odd residue), the three proved leaf theorems plus Case 1 cover **4 shapes / 1806
multisets**. **23 shapes / 1506 multisets — 45.5% — are covered by nothing.**

Examples, each a valid n=8 tuple: `E = {1,2,3,4,5,7,8}` (Unit-Complete, `|R_non| = 6`);
`E = {1,3,5,7,8,9,11}` (Unit-Complete, `|R_non| = 4`); `E = {1,2,3,4,8,9,10}`
(dropped-unit, `|R_non| = 4`).

## 2. Why: `|R_non| = 5` is assumed by all three leaves, never derived  `[quoted]`

- `reports/n8_dropped_unit.md:16–18` — "`R_non = {ρ_e …}`. **Assume** … `|R_non| = 5` —
  exactly two of the classes `{1,…,7}` are absent".
- `docs/n8/PARITY_MECHANISM_v1.md:10–11` — "Unit-Complete: the two residue classes of
  `{1,…,7}` absent from `R_non` are both non-units, so `R_non` = `{1,3,5,7}` together with
  **exactly one** `ρ₀ ∈ {2,4,6}`."
- `docs/n8/SAFE_FIBRE_THEOREM_v1.md:56` — "Under the hypotheses of §1, `|E_non| = 5` and
  `|E| = 7`, so `|E_div| = 2` always".

The genuinely exhaustive split is the one `reports/n8_agent_branch_inventory.md:31` states
— "(A) some unit class `d ∉ R_non`; (B) no unit class is [missing]" — with **no**
constraint on `|R_non|`. Our leaves realise only the `|R_non| = 5` slice of it.

## 3. The claim this makes false  `[quoted]`

`STATUS_n8_ANALYTIC_v1.md` §3:

> "Given (H′), together with §2's reduction, the Dilation theorem, and Lemma D for the one
> primitive exception, the non-representative case closes **and with it n=8**."

Closing (H′) and (NR) leaves 23 shapes untouched. The leaf theorems are each correct
**within their stated hypotheses**; it is this summary sentence, and the four-row tree it
sits under, that overreach.

## 4. How hard the uncovered shapes are  `[EMPIRICAL — scoped]`

For every 7-subset of `[1..26]` with gcd 1, sampled ≤60 per shape, exact rationals, entry
evaluation: **every uncovered shape closes by the plain union bound, 0 failures**, with
margin `|S| − |∪B_m|` from **0.107** (`UC |R_non|=6, |E_div|=1`) to **0.378**. The
uncovered region is *easier* than the covered one — which is the point: `|R_non| = 5` is
the tight balance between "enough runners to cover" and "not so many that they waste".

**Scope, stated plainly.** Speeds `≤ 26` and sampled, so this is representative-ish speeds
only. Each uncovered shape carries its own representative / non-representative split, and
**none of those has been examined**. This is evidence that the shapes are cheap, not proof.

## 5. `|E_div| ≥ 4` was invisible to any small-box search  `[PROVED / OPEN]`

Six shapes have `|E_div| ∈ {4,5,6}`, and `[1..26]` cannot hold four multiples of 8, so the
box enumeration could not produce them at all. Max realisable is `|E_div| = 6`.

- **`|E_div| = 6` closes in one line `[PROVED]`.** `|E_non| = 1`, and a single
  non-divisible runner blocks at most 4 residues (max over `gcd(e,8) ∈ {1,2,4}` is 4, at
  `ρ = 4`), so some `r` is always free; `LRC(7)`, which we own axiom-clean, gives `t` with
  `‖m_i t‖ ≥ 1/7 > 1/8` for the six `m_i`.
- **`|E_div| = 4, 5` do not `[OPEN]`.** I first wrote that `|E_non| ≤ 3` blocks "≤ 6 < 8"
  residues. **That is wrong** — a `ρ ≡ 4 (mod 8)` runner blocks 4, so three of them reach
  12, and two can already block all 8. Corrected before use.

## 6. What the shape split is hiding, and the recommendation

`S^c = U(E_non)`: the set where the **non-divisible** runners block every residue. A
divisible runner `8m` blocks every `r` exactly on `B_m`. So a witness exists iff
`S \ ⋃B_m ≠ ∅`, and one sufficient condition covers **every leaf at once**:

> **`u(E_non) + |⋃_{8m ∈ E_div} B_m| < 1`**,  `u(E_non) = |{x : E_non blocks all of ℤ/8}|`.

Every one of the three leaf theorems is a computation of `u(E_non)` for one residue shape;
`|S^c| < 1/2` in (H′) is exactly `u < 1/2` against the B-lemma's `|B_{m₁} ∪ B_{m₂}| < 1/2`.
The 27-shape fragmentation is an artefact of computing `u` shape by shape.

**Recommendation — in order:**

1. **Bound `u(E_non)` for an arbitrary set of `≤ 6` non-divisible speeds.** Shape-free,
   subsumes all 27 shapes and both open leaves. Needed: `u < 3/4` for `|E_div| = 1`,
   `u < 1/2` for `= 2` (the B-lemma), and a 3-runner B-lemma for `= 3`.
2. **Close `|E_div| = 4, 5`** by the placement argument (`LRC(d+1)` gives an interval, not
   just a point, since `1/(d+1) > 1/8` strictly); `|E_div| = 6` is done.
3. **Then** (H′) and (NR), which are the `|R_non| = 5` residue — genuinely the hardest
   slice, but not the whole problem and not closable into n=8 on their own.

Doing 3 before 1 optimises a 55% slice while the size of the other 45% is unknown.

## 7. Grades

§1 shape enumeration and §2/§3 quotations: **PROVED**. §4 difficulty: **EMPIRICAL**,
speeds `≤ 26`, sampled, representative-ish only. §5 `|E_div| = 6`: **PROVED** (cites
`LRC(7)`, ours, axiom-clean); `|E_div| = 4,5`: **OPEN**. §6 master criterion: **PROVED**
(it is the framework's own bridge, restated); the `u` bound itself: **OPEN**.
