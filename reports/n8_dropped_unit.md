# The n = 8 dropped-unit leaf, closed for representative speeds

2026-09-08. Companion to `docs/n8/UNITCOMPLETE_THEOREM_v1.md` (both absent classes
non-units, `|E_div| = 2`) and `docs/n8/TWIN_CASE_THEOREM_v1.md` (`|E_div| = 1`).
Artifacts: `experiments/n8/du2_*.py` and the `du2_*.out` logs beside them.
Exact integer / rational arithmetic throughout; no floating point enters any decision.
Nothing here verifies LRC(8) numerically — its truth is known and is not the question.

---

## 0. Statement

> **Theorem (dropped-unit leaf, representative speeds).**  `[PROVED]`
> Let `E` be a set of 7 distinct positive integers with some element divisible by 8.
> Write `E_non` for the elements not divisible by 8, `E_div` for those that are, and
> `R_non = {ρ_e = e mod 8 : e ∈ E_non}`. Assume
>
> * `|R_non| = 5` — exactly two of the classes `{1,…,7}` are absent;
> * **at least one absent class is a unit** of `ℤ/8` (units are `{1,3,5,7}`);
> * **representative speeds**: `e = ρ_e` for every `e ∈ E_non`.
>
> Then there is an integer `k` with `‖e·k / (8L)‖ ≥ 1/8` for every `e ∈ E`, where
> `L = lcm(E)`; that is, `x₀(E) ≥ 1`.

Representativeness forces `|E_non| = |R_non| = 5` (two speeds in one class would have
to be equal), hence `|E_div| = 2` and

    E  =  R_non  ∪  {8m₁, 8m₂},        m₁ ≠ m₂ positive integers.

There are `C(7,2) − C(3,2) = 21 − 3 = 18` admissible absent pairs: `C(4,2) = 6` with
both absent classes units, `4 · 3 = 12` with one unit and one non-unit.

**`gcd(E) = 1` is not used.** All 18 `E_non` have `gcd = 1` on their own
(`du2_lemma_checks_v1.out`, L6), so the hypothesis is automatic here; the proof never
appeals to it. **No upper bound on `m₁, m₂` is assumed.**

The proof is a union bound. The five non-divisible runners leave a safe set `S` of
measure at least `19/35`; the two divisible runners remove a set of measure at most
`1/2`; `19/35 − 1/2 = 3/70 > 0`.

---

## 1. The bridge and the reduction  `[PROVED — framework axiom, restated]`

`L = lcm(E)`, `N = 8L`. Every `k ∈ [0, 8L)` is uniquely `k = b + rL` with `b ∈ [0,L)`
and `r ∈ ℤ/8`. Writing `e·b = t_e·L + s_e` with `t_e = ⌊e·b/L⌋` and `0 ≤ s_e < L`,

    e·k mod 8L  =  ((t_e + e·r) mod 8)·L + s_e.

Since `0 ≤ s_e < L`, the loneliness condition `e·k mod 8L ∈ [L, 7L]` holds **if**
`(e·r + t_e) mod 8 ∈ {1,…,6}`. With `x = b/L` and `t_e = ⌊e·x⌋`, define

    bad(e,t) = { r ∈ ℤ/8 : (e·r + t) mod 8 ∈ {0,7} },
    C(x)     = ⋃_{e ∈ E} bad(e, ⌊e·x⌋),

**the union running over all of `E`, divisible runners included.** If `C(x) ≠ ℤ/8` for
some `x = b/L` with `b` an integer, then any `r ∉ C(x)` gives a witness `k = b + rL`.

`bad(e,t)` depends only on `e mod 8` and `t mod 8`
(`du2_lemma_checks_v1.out`, L1/L2: 0 violations over all `ρ`, all `t mod 8`, and all
speeds `8q + ρ` with `q ≤ 11`).

---

## 2. What each runner contributes  `[PROVED]`

Verified exhaustively in `du2_lemma_checks_v1.py` (L1–L3, 0 violations).

**Units (`ρ ∈ {1,3,5,7}`).** `ρ² ≡ 1 (mod 8)`, so
`bad(ρ,t) = {−tρ, −(t+1)ρ}` — exactly two residues differing by the odd number `ρ`,
hence one odd and one even.

**`ρ ∈ {2,6}` (`gcd(e,8) = 2`).** `bad(e,t)` is a single coset of `H₂ = {0,4}`, of size
exactly 2, **never empty**, and contained in one parity class.

**`ρ = 4` (`gcd(e,8) = 4`).** `bad(e,t)` is the set of even residues for `t ≡ 0,7`, the
set of odd residues for `t ≡ 3,4`, and **empty** for `t ≡ 1,2,5,6 (mod 8)`.

*(The framework's phrasing "a single coset of `H_g` or empty" is correct as a superset
statement; the emptiness option is realised only at `g = 4`.)*

**Divisible (`e = 8m`).** `e·r ≡ 0 (mod 8)`, so `bad(8m,t) = ℤ/8` when `t mod 8 ∈ {0,7}`
and `bad(8m,t) = ∅` otherwise — **independent of `r`**. In `x`-coordinates

    B_m := { x ∈ [0,1) : ⌊8m x⌋ mod 8 ∈ {0,7} }
         = ⋃_j [ j/m − 1/(8m),  j/m + 1/(8m) )      (indices mod 1)
         = { x : ‖m x‖ < 1/8 },      |B_m| = 1/4 exactly.

The floor form and the closed form were computed as interval sets **two independent
ways in two independent scripts** and agree for `m = 1..30`, with measure exactly `1/4`
(`du2_bm_and_endtoend_v1.out` Part A, `du2_lemma_checks_v1.out` L3, and the cross-check
of `Bm_clip` against `Bm_floor_form`).

So, setting

    S := { x ∈ [0,1) : ⋃_{e ∈ E_non} bad(e, ⌊e·x⌋) ≠ ℤ/8 },

we have

    C(x) ≠ ℤ/8   ⟺   x ∈ S  and  x ∉ B_{m₁} ∪ B_{m₂}.                       (★)

---

## 3. The B-lemma, with proof  `[PROVED]`

> **B-Lemma.** For distinct positive integers `m₁ ≠ m₂`, with `g = gcd(m₁,m₂)` and
> `M = max(m₁,m₂)`,
>
>     |B_{m₁} ∪ B_{m₂}|  ≤  1/2 − g/(4M)  <  1/2.

*Proof.* `|B_{m₁} ∪ B_{m₂}| = 1/4 + 1/4 − |B_{m₁} ∩ B_{m₂}|`, so it suffices that
`|B_{m₁} ∩ B_{m₂}| ≥ g/(4M)`. The `g` points `c = i/g`, `i = 0,…,g−1`, are simultaneously
of the form `j/m₁` and `j'/m₂`. Around each, `B_{m_i} ⊇ [c − 1/(8m_i), c + 1/(8m_i))`,
so `B_{m₁} ∩ B_{m₂} ⊇ [c − 1/(8M), c + 1/(8M))`, an interval of length `1/(4M)`.
These `g` intervals are pairwise disjoint because `1/(4M) < 1/g` (indeed `g ≤ min ≤ M`).
Summing gives `|B_{m₁} ∩ B_{m₂}| ≥ g/(4M)`. Strictness of the second inequality is
`g ≥ 1`, `M < ∞`. ∎

Checked exhaustively for all `1 ≤ m₁ < m₂ ≤ 40` by exact interval algebra: **0
violations**; the bound is **attained with equality** at 76 of the 435 pairs
`m₁,m₂ ≤ 30` (e.g. every `(1,m)`). The largest union over `1 ≤ m₁ < m₂ ≤ 40` is
`13/28 = 0.464285…`, attained at exactly five pairs: `(1,7), (2,14), (3,21), (4,28),
(5,35)`.

**Only `|B_{m₁} ∪ B_{m₂}| ≤ 1/2` is used below.** The sharpened form matters only in §10.

---

## 4. Integrality  `[PROVED]`

Every `e ∈ E` divides `L`. The breakpoints of `S` are the points `j/e`, `e ∈ E_non`, so
in `b`-coordinates they are `jL/e ∈ ℤ`. The endpoints of `B_m` are `(8j±1)/(8m)`, so in
`b`-coordinates `(8j±1)·(L/(8m)) ∈ ℤ`, because `8m ∈ E` divides `L`.

`S` is a finite union of half-open intervals `[a,b)` (cells of the breakpoint
decomposition), and `B_m` is likewise left-closed and right-open. Hence
`S \ (B_{m₁} ∪ B_{m₂})` is a finite union of half-open intervals with **integer**
`b`-endpoints. If it has positive measure, some component `[a,β)` has `β − a ≥ 1/L`,
i.e. length at least 1 in `b`-coordinates, and `a·L` is an integer lying in it.

**No rounding term is ever needed, and cardinality in `b` equals `L ×` measure in `x`
exactly.** The `x`-measure of `S` was independently recomputed for all 18 pairs by pure
integer enumeration over `b ∈ [0,L)`, `L = lcm(E_non)` — no `Fraction` arithmetic at all
— and matched the exact cell measure in all 18 (`du2_safe_measure_v1.out`).

---

## 5. The safe set `S` of the five representative non-divisible runners  `[PROVED]`

Computed by exact rational cell decomposition on the breakpoints `j/e`, `e ∈ E_non`.
The **full per-cell certificate** — every cell, the five floors `t_e`, the covered set,
and the complete uncovered set `U` — is Appendix A. The summary:

| absent | `E_non` | `\|S\|` | float | `\|S\|−1/2` | maximal windows of `S` (length; residues uncovered throughout) |
|---|---|---|---|---|---|
| (1,2) | 3,4,5,6,7 | `1` | 1.00000 | `1/2` | `[0,1)`, len `1` |
| (1,3) | 2,4,5,6,7 | `1` | 1.00000 | `1/2` | `[0,1)`, len `1` |
| (1,4) | 2,3,5,6,7 | `1` | 1.00000 | `1/2` | `[0,1)`, len `1` |
| (1,5) | 2,3,4,6,7 | `1` | 1.00000 | `1/2` | `[0,1)`, len `1` |
| (1,6) | 2,3,4,5,7 | `1` | 1.00000 | `1/2` | `[0,1)`, len `1` |
| (1,7) | 2,3,4,5,6 | `1` | 1.00000 | `1/2` | `[0,1)`, len `1` |
| (2,3) | 1,4,5,6,7 | `5/6` | 0.83333 | `1/3` | `[0,1/6)` `{5}`; `[1/4,3/4)` len `1/2`; `[5/6,1)` `{2}` |
| (2,5) | 1,3,4,6,7 | `1` | 1.00000 | `1/2` | `[0,1)`, len `1` |
| (2,7) | 1,3,4,5,6 | `5/6` | 0.83333 | `1/3` | `[0,1/6)` `{1}`; `[1/4,3/4)` len `1/2`; `[5/6,1)` `{6}` |
| **(3,4)** | **1,2,5,6,7** | **`19/35`** | **0.54286** | **`3/70`** | `[0,1/5)` `{6}`; `[3/7,4/7)` len `1/7`; `[4/5,1)` `{1}` |
| (3,5) | 1,2,4,6,7 | `1` | 1.00000 | `1/2` | `[0,1)`, len `1` |
| (3,6) | 1,2,4,5,7 | `1` | 1.00000 | `1/2` | `[0,1)`, len `1` |
| (3,7) | 1,2,4,5,6 | `5/6` | 0.83333 | `1/3` | `[0,1/6)` `{1,5}`; `[1/4,3/4)` len `1/2`; `[5/6,1)` `{2,6}` |
| (4,5) | 1,2,3,6,7 | `1` | 1.00000 | `1/2` | `[0,1)`, len `1` |
| (4,7) | 1,2,3,5,6 | `13/15` | 0.86667 | `11/30` | `[0,1/3)` `{2}`; `[2/5,3/5)` len `1/5`; `[2/3,1)` `{5}` |
| (5,6) | 1,2,3,4,7 | `1` | 1.00000 | `1/2` | `[0,1)`, len `1` |
| (5,7) | 1,2,3,4,6 | `1` | 1.00000 | `1/2` | `[0,1)`, len `1` |
| (6,7) | 1,2,3,4,5 | `1` | 1.00000 | `1/2` | `[0,1)`, len `1` |

    min over the 18 pairs of |S|  =  19/35  =  0.542857…   (absent pair (3,4))
    min over the 18 pairs of |S| − 1/2  =  3/70  =  0.0428571…

Thirteen of the eighteen have `S = [0,1)`: **no** `x` is blocked at all, whatever the
divisible runners do to the rest. Only `(2,3)`, `(2,7)`, `(3,4)`, `(3,7)`, `(4,7)` lose
anything, and only `(3,4)` comes within `3/70` of the union bound.

### 5.1 The extremal case `(3,4)`, worked

`E_non = {1,2,5,6,7}`; sixteen cells; the safe ones are exactly

    [0,1/7) [1/7,1/6) [1/6,1/5)   |  [3/7,1/2) [1/2,4/7)  |  [4/5,5/6) [5/6,6/7) [6/7,1)

grouping into three maximal windows

    W₁ = [0, 1/5)   length 1/5,   residue 6 uncovered throughout
    W₂ = [3/7, 4/7) length 1/7,   residue 2 on [3/7,1/2), residue 5 on [1/2,4/7)
    W₃ = [4/5, 1)   length 1/5,   residue 1 uncovered throughout

`|S| = 1/5 + 1/7 + 1/5 = 7/35 + 5/35 + 7/35 = 19/35`. `W₂` has **no** residue valid
across the whole window, which is precisely why requirement (ii) — track every
uncovered residue, not one — is load-bearing: a single-residue tracker reports `W₂`
covered and lands on `|S| = 14/35 = 2/5 < 1/2`, and the union bound then fails.

The row-by-row certificate for `(3,4)` is in Appendix A.

---

## 6. Proof of the theorem

Let `E = R_non ∪ {8m₁, 8m₂}` satisfy the hypotheses, and let `A` be the absent pair.

1. By §5, `|S| ≥ 19/35`, with equality only for `A = (3,4)`.
2. By §2 and §3, `|B_{m₁} ∪ B_{m₂}| ≤ 1/4 + 1/4 = 1/2`.
3. Hence `|S \ (B_{m₁} ∪ B_{m₂})| ≥ 19/35 − 1/2 = 3/70 > 0`.
4. By §4 that set is a finite union of half-open intervals with integer `b`-endpoints,
   so it contains an integer `b ∈ [0,L)`; put `x = b/L`.
5. By (★), `C(x) ≠ ℤ/8`. Choose `r ∉ C(x)`. By §1, `k = b + rL` satisfies
   `e·k mod 8L ∈ [L, 7L]`, i.e. `‖e·k/(8L)‖ ≥ 1/8`, for every one of the seven `e ∈ E`.

Therefore `x₀(E) ≥ 1`. ∎

Every inequality used is exact: `19/35 > 1/2` because `38 > 35`; `3/70 > 0`. No
equidistribution input, no appeal to LRC(8), no bound on `m₁, m₂`, no use of `gcd(E)=1`.

### 6.1 The witnesses are real, and were checked as integers

`du2_bm_and_endtoend_v1.py` Part B ran the construction on **all 18 absent pairs ×
all `1 ≤ m₁ < m₂ ≤ 14` = 1638 tuples**. For each: `b` was *located* by exact interval
algebra (never by searching over `b`), then `k = b + rL` was *checked* in pure integer
arithmetic against all seven runners.

    1638 tuples, 0 failures.
    min over all tuples of  min_e ‖e·k/(8L)‖  =  1/8  exactly
    (attained e.g. at E = {3,4,5,6,7,8,16}, L = 1680, b = 210, r = 7, k = 11970).

One explicit witness per absent pair, at `(m₁,m₂) = (1,2)` so `E = E_non ∪ {8,16}`:

| absent | `E` | `L` | `b` | `r` | `k = b + rL` | `min_e ‖ek/N‖` |
|---|---|---|---|---|---|---|
| (1,2) | 3,4,5,6,7,8,16 | 1680 | 210 | 7 | 11970 | `1/8` |
| (1,3) | 2,4,5,6,7,8,16 | 1680 | 210 | 5 | 8610 | `1/8` |
| (1,4) | 2,3,5,6,7,8,16 | 1680 | 210 | 2 | 3570 | `1/8` |
| (1,5) | 2,3,4,6,7,8,16 | 336 | 42 | 3 | 1050 | `1/8` |
| (1,6) | 2,3,4,5,7,8,16 | 1680 | 210 | 7 | 11970 | `1/8` |
| (1,7) | 2,3,4,5,6,8,16 | 240 | 30 | 1 | 270 | `1/8` |
| (2,3) | 1,4,5,6,7,8,16 | 1680 | 210 | 5 | 8610 | `1/8` |
| (2,5) | 1,3,4,6,7,8,16 | 336 | 42 | 3 | 1050 | `1/8` |
| (2,7) | 1,3,4,5,6,8,16 | 240 | 30 | 1 | 270 | `1/8` |
| (3,4) | 1,2,5,6,7,8,16 | 1680 | 210 | 2 | 3570 | `1/8` |
| (3,5) | 1,2,4,6,7,8,16 | 336 | 42 | 3 | 1050 | `1/8` |
| (3,6) | 1,2,4,5,7,8,16 | 560 | 70 | 5 | 2870 | `1/8` |
| (3,7) | 1,2,4,5,6,8,16 | 240 | 30 | 1 | 270 | `1/8` |
| (4,5) | 1,2,3,6,7,8,16 | 336 | 42 | 2 | 714 | `1/8` |
| (4,7) | 1,2,3,5,6,8,16 | 240 | 30 | 1 | 270 | `1/8` |
| (5,6) | 1,2,3,4,7,8,16 | 336 | 42 | 3 | 1050 | `1/8` |
| (5,7) | 1,2,3,4,6,8,16 | 48 | 6 | 1 | 54 | `1/8` |
| (6,7) | 1,2,3,4,5,8,16 | 240 | 30 | 1 | 270 | `1/8` |

---

## 7. Boundary exactness  `[PROVED — no cell centre is ever evaluated]`

Requirement (i). For every cell `[a,β)` of every decomposition used above, and every
`e ∈ E_non`:

* **Completeness.** Let `k₀ = ⌊e·a⌋ + 1`, the least integer strictly greater than `e·a`.
  Then no integer `k` has `a < k/e < β` iff `k₀/e ≥ β`, an exact rational comparison.
  Reported count of interior breakpoints: **0**, across all 18 pairs (246 cells in total),
  and **0** again on the audited subsamples of the non-representative sweeps of §10.
* **Entry equals exit.** `⌊e·a⌋` (the value on the left-closed endpoint) equals
  `lim_{x→β⁻} ⌊e·x⌋ = ⌊e·β⌋ − [e·β ∈ ℤ]`. Reported mismatches: **0**.
  The bracket term is not decorative: at `n = 8` the hits `5·(3/5) = 3` and
  `7·(5/7) = 5` are exact, so `⌊e·β⌋` and the exit value differ at those endpoints.
* **Covered set at entry equals covered set at exit.** Computed separately from the two
  floor vectors and compared as sets. Reported differences: **0**.

These three counts are printed by `du2_safe_measure_v1.py` (all 18 pairs), asserted
inside `du2_cell_tables_v1.py` (the Appendix A generator aborts on either failure), and
re-reported on sampled subsets by `du2_nonrep_v1.py` and `du2_nonrep_deep_v1.py`.

**Which side an inclusion errs on.** The bridge of §1 is stated as an implication, not
an equivalence: when `(t_e + e·r) ≡ 7 (mod 8)` **and** `s_e = 0`, runner `e` is in fact
satisfied even though `r ∈ bad(e,t_e)`. So the floor-built `bad` set is a **superset**
of the true one, `S` as computed is a **subset** of the true safe set, and every
conclusion of the form "a safe fibre exists" is **conservative** — it can understate the
safe set, never overstate it.

Measured: over 54 tuples (18 absent pairs × `(m₁,m₂) ∈ {(1,2),(2,3),(3,5)}`), with
`(b,r)` enumerated over the full `[0,L) × ℤ/8`,

    floor-criterion witnesses  30910
    true witnesses             31428     (>= floor, as predicted)
    floor-but-not-true             0     (every floor witness is a true witness)

(`du2_lemma_checks_v1.out`, L5.)

---

## 8. Controls  `[PROVED — the test is not forced]`

The load-bearing step is the union bound `|S| > 1/2`. It is not an identity of the code;
it fails on inputs where it should (`du2_controls_v1.out`).

* **C1 / C3 — the union bound can be negative.** Over all 21 two-element absent sets,
  **exactly one** fails `|S| > 1/2`: the pair `(2,6)`, i.e. the *Unit-Complete* case
  `ρ₀ = 4`, `E_non = {1,3,4,5,7}`, `|S| = 5/14 = 0.357…`. That is the companion leaf
  which needs Lemma D rather than a measure bound. All 18 dropped-unit pairs pass.
  This also reproduces `UNITCOMPLETE_THEOREM_v1.md` §4 exactly and independently:
  `|S(2)| = 22/35`, `|S(4)| = 5/14`, `|S(6)| = 6/7`.
* **C2 — the machinery can return empty.** `E_non = {1,…,7}` (all seven classes present)
  gives `|S| = 0` and 0 safe cells, so the witness locator has nothing to pick. A search
  over all 6188 five-element `E_non` with speeds `≤ 19`, all six-element `E_non` with
  speeds `≤ 15`, and 40 000 random five-element sets with speeds `≤ 40`, found **no**
  empty `S`, so this control had to be built from the seven-class set.
* **C4 — mutation control.** Replacing the bad-residue set `{0,7}` by `{0,1,7}` changes
  `|S|` in **18 of 18** pairs (e.g. `(3,4)`: `19/35 → 1/5`; `(2,3)`: `5/6 → 1/28`), so
  `|S|` responds to the criterion rather than being an artefact of the cell code.
* **Independent recomputation.** The measure of `S` for all 18 pairs, recomputed by pure
  integer enumeration over `b ∈ [0, lcm(E_non))` with no `Fraction` arithmetic: agrees
  in all 18.
* **Two independent `B_m` implementations** (`du2_bm_and_endtoend_v1.Bm_floor_form`,
  `du2_nonrep_endtoend_v1.Bm_clip`) agree as interval sets for `m = 1..30`.
* **Brute-force locator control.** On the subsample where `L ≤ 200 000`, an independent
  integer scan for the first safe `b` was run alongside the interval-algebra locator:
  **79/79** and **2/2** found one, and where both ran they agreed on the value
  (e.g. `E = {2,3,5,12,14,24,40}`: locator `b = 35`, scan first safe `b = 35`).

---

## 9. Relation to the two refuted results  `[VERIFIED-INSTANCE]`

Neither refuted statement is used anywhere above; the leaf is proved directly.

* **Lemma 11.3c is false at `n = 8`** on `E = (1,2,3,4,6,8,24)`, `L = 24`, where its
  `b = 6`, `r_d = 1` gives `k = 30`, and runner 6 has `6·30 mod 192 = 180 > 7L = 168`.
  Reproduced. That tuple **is** in this leaf: `E_non = {1,2,3,4,6}`, absent pair
  `(5,7)` (both units), representative, `E_div = {8·1, 8·3}`. The theorem above applies
  and delivers `b = 3`, `r = 1`, `k = 27`, with `min_e ‖e·k/192‖ = 1/8` — the first of
  the 38 true witnesses in `[0, 192)` (found by exhaustive integer enumeration).
* **Lemma 11.3a′ Case III is false** on `E = (1,2,3,4,5,6,64)`, `L = 960`, `b̂ = 839`,
  where `bad(64, 55) = ℤ/8`. That tuple is **outside** this leaf: `R_non = {1,…,6}` has
  six classes, so only one class is absent and `|E_div| = 1`. It belongs to the
  one-absent-class configuration, which this report does not claim. (For information
  only: the same framework applied to it gives `|S| = 7/10`, `|S \ B₈| = 87/160`, and
  the witness `b = 15`, `r = 1`, `k = 975`, slack `1/8`.)

---

## 10. Without representativeness — what survives, and what does not

Drop `e = ρ_e` and keep everything else: `E_non = {e_ρ = 8q_ρ + ρ : ρ ∈ R_non}` with
`q_ρ ≥ 0` arbitrary, `|E_div| = 2`.

**Speed-independent — survives verbatim:**

| step | why |
|---|---|
| §1 bridge and (★) | stated for arbitrary `e ∈ E`; no size or residue assumption |
| §2 pair rule and the non-unit shapes | `bad(e,t)` depends only on `e mod 8`, `t mod 8` — checked for all `q ≤ 11` (L1/L2, 0 violations) |
| §2 `B_m`, `\|B_m\| = 1/4` | `E_div` is untouched by representativeness |
| §3 B-lemma | a statement about `m₁, m₂` alone |
| §4 integrality | uses only `e \| L` for every `e ∈ E`, which still holds |
| §7 boundary discipline | a property of the cell decomposition, recomputed per instance |

**Not speed-independent — the one thing that has to be redone:** the value of `|S|` in
§5. The breakpoints move from `j/ρ` to `j/(8q_ρ+ρ)`, so the cell table is different for
every `q`-vector, and §5's table proves nothing about them.

**What the sweeps show.**  `[EMPIRICAL — verified scope, not proved]`

| sweep | instances | `min \|S\|` | instances with `\|S\| < 1/2` |
|---|---|---|---|
| exhaustive, all 18 pairs, `q_ρ ≤ 4` | 56 250 | `1/2` exactly | 0 |
| exhaustive, absent `(1,7)`, `q_ρ ≤ 6` | 16 807 | `1/2` exactly | 0 |
| random, all 18 pairs, `q_ρ ≤ 25` | 3 000 | `0.7190…` | 0 |
| random mixed (half the coordinates `q ≤ 3`), `q_ρ ≤ 40` | 4 000 | `0.6937…` | 0 |

Boundary audit on the sampled subsets of every sweep: 0 interior breakpoints,
0 entry/exit mismatches, 0 entry-vs-exit covered-set differences.

The minimum is `|S| = 1/2` **exactly**, attained at exactly one instance of the
exhaustive `q ≤ 4` sweep of all 18 pairs (and at none below it):

    E_non = {2, 3, 12, 5, 14}   (ρ = 2,3,4,5,6; absent pair (1,7))
    S     = [0, 1/4) ∪ [3/4, 1) = { x : ‖x‖ < 1/4 },   |S| = 1/2,
            residue 7 uncovered throughout [0,1/4), residue 0 throughout [3/4,1).

At `|S| = 1/2` the crude bound `|B_{m₁} ∪ B_{m₂}| ≤ 1/2` is exhausted and **the
sharpened B-lemma of §3 is what closes the case**: `|S| − |B_{m₁} ∪ B_{m₂}| ≥ g/(4M) > 0`.
That margin is attained, not merely bounded — the worst tuple found in the exhaustive
`q ≤ 2`, `m ≤ 6` end-to-end run is

    E = {2,3,5,12,14,8,48},  m₁ = 1, m₂ = 6:  |S| = 1/2, |B₁ ∪ B₆| = 11/24,
    surplus = 1/24 = gcd(1,6)/(4·6)  exactly.

**End-to-end, non-representative:**

    exhaustive  q_ρ ≤ 2, 1 ≤ m₁ < m₂ ≤ 6 :  65 610 tuples, 0 failures
    random      q_ρ ≤ 20, m ≤ 200        :   1 500 tuples, 0 failures
    random      q_ρ ≤ 1,  m ≤ 4          :     400 tuples, 0 failures,
                                              brute-force control 79/79

with `b` located by exact interval algebra and `k` checked as an integer against all
seven runners in every case.

**The exact residual gap.** Everything in §6 goes through for arbitrary speeds once

> **(NR)** `|S| ≥ 1/2` for every admissible non-representative `E_non` in this leaf,

since §3 upgrades `≥ 1/2` to a strict surplus. **(NR) is verified on 80 000+ instances
and is not proved.** It is not a formality: the companion Unit-Complete leaf has
`|S| = 5/14 < 1/2` at `ρ₀ = 4` already for representative speeds, so no argument that
would prove (NR) for all five-class `E_non` can be correct. Two natural strengthenings
are false and were checked:

* `{x : ‖x‖ < 1/4} ⊆ S` — false; absent `(3,4)` representative has `S ∩ [0,1/4) = [0,1/5)`.
* a single-residue bound — for a fixed `r` and a single runner `e`, the set killing `r`
  is `{x : ⌊ex⌋ mod 8 ∈ {a, a−1}}` for one `a`, of measure at most `1/4 + 2/e`. Summing
  five of those bounds the killed set by `5/4 + 2·Σ 1/e_ρ`, which exceeds 1 — the union
  bound over the five runners at a **fixed** `r` carries no information. (NR) has to come
  from the union **over `r`**, not from any one `r`.

The statement of scope is therefore:

> **Non-representative status.** All structural ingredients transfer unchanged. The leaf
> is closed for representative speeds `[PROVED]`, and for the non-representative
> instances actually enumerated `[VERIFIED-INSTANCE: 56 250 + 16 807 + 65 610 + …]`.
> A general non-representative proof needs (NR), or a `q`-uniform window argument in
> place of the measure bound — the analogue of what `TWIN_CASE_THEOREM_v1.md` does for
> the sixth runner. `[OPEN]`

---

## 11. Artifacts

| file | what it produces |
|---|---|
| `experiments/n8/du2_safe_measure_v1.py` | §5 table; boundary audit; independent integer recount |
| `experiments/n8/du2_cell_tables_v1.py` | Appendix A (asserts the boundary conditions) |
| `experiments/n8/du2_bm_and_endtoend_v1.py` | §2 `B_m` two ways; §6.1 end-to-end, 1638 tuples |
| `experiments/n8/du2_lemma_checks_v1.py` | §2 L1–L3, §3 B-lemma, §7 inclusion direction, gcds |
| `experiments/n8/du2_controls_v1.py` | §8 falsification controls |
| `experiments/n8/du2_nonrep_v1.py`, `du2_nonrep_deep_v1.py` | §10 sweeps |
| `experiments/n8/du2_nonrep_endtoend_v1.py` | §10 end-to-end with general speeds |
| `experiments/n8/du2_report_tables_v1.py` | §5 and §6.1 tables as printed here |

Every one writes a `.out` log beside itself.

---

## Appendix A — full per-cell certificate, all 18 absent pairs

Generated by `experiments/n8/du2_cell_tables_v1.py`, which **asserts** for every cell and
every `e` that (a) no integer `k` has `a < k/e < β` and (b) the entry floor equals the
exit floor, and aborts if either fails. `t_e` is the constant value of `⌊e·x⌋` on the
cell. `U` is the complete uncovered set; a cell is safe iff `U ≠ ∅`.


### absent (1, 2)   E_non = [3, 4, 5, 6, 7]
| cell | t_3 | t_4 | t_5 | t_6 | t_7 | covered | U | safe | length |
|---|---|---|---|---|---|---|---|---|---|
| `[0,1/7)` | 0 | 0 | 0 | 0 | 0 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/7` |
| `[1/7,1/6)` | 0 | 0 | 0 | 0 | 1 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/42` |
| `[1/6,1/5)` | 0 | 0 | 0 | 1 | 1 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/30` |
| `[1/5,1/4)` | 0 | 0 | 1 | 1 | 1 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/20` |
| `[1/4,2/7)` | 0 | 1 | 1 | 1 | 1 | [0, 1, 2, 3, 5, 6] | [4, 7] | YES | `1/28` |
| `[2/7,1/3)` | 0 | 1 | 1 | 1 | 2 | [0, 1, 2, 3, 5, 6] | [4, 7] | YES | `1/21` |
| `[1/3,2/5)` | 1 | 1 | 1 | 2 | 2 | [1, 2, 3, 5, 6] | [0, 4, 7] | YES | `1/15` |
| `[2/5,3/7)` | 1 | 1 | 2 | 2 | 2 | [1, 2, 3, 5, 6] | [0, 4, 7] | YES | `1/35` |
| `[3/7,1/2)` | 1 | 1 | 2 | 2 | 3 | [1, 2, 3, 4, 5, 6] | [0, 7] | YES | `1/14` |
| `[1/2,4/7)` | 1 | 2 | 2 | 3 | 3 | [1, 2, 3, 4, 5, 6] | [0, 7] | YES | `1/14` |
| `[4/7,3/5)` | 1 | 2 | 2 | 3 | 4 | [1, 2, 4, 5, 6] | [0, 3, 7] | YES | `1/35` |
| `[3/5,2/3)` | 1 | 2 | 3 | 3 | 4 | [1, 2, 4, 5, 6] | [0, 3, 7] | YES | `1/15` |
| `[2/3,5/7)` | 2 | 2 | 3 | 4 | 4 | [1, 2, 4, 5, 6, 7] | [0, 3] | YES | `1/21` |
| `[5/7,3/4)` | 2 | 2 | 3 | 4 | 5 | [1, 2, 4, 5, 6, 7] | [0, 3] | YES | `1/28` |
| `[3/4,4/5)` | 2 | 3 | 3 | 4 | 5 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/20` |
| `[4/5,5/6)` | 2 | 3 | 4 | 4 | 5 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/30` |
| `[5/6,6/7)` | 2 | 3 | 4 | 5 | 5 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/42` |
| `[6/7,1)` | 2 | 3 | 4 | 5 | 6 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/7` |

**18 of 18 cells safe; |S| = 1 = 1.000000 > 1/2; surplus 1/2.**

### absent (1, 3)   E_non = [2, 4, 5, 6, 7]
| cell | t_2 | t_4 | t_5 | t_6 | t_7 | covered | U | safe | length |
|---|---|---|---|---|---|---|---|---|---|
| `[0,1/7)` | 0 | 0 | 0 | 0 | 0 | [0, 1, 2, 3, 4, 6] | [5, 7] | YES | `1/7` |
| `[1/7,1/6)` | 0 | 0 | 0 | 0 | 1 | [0, 1, 2, 3, 4, 6] | [5, 7] | YES | `1/42` |
| `[1/6,1/5)` | 0 | 0 | 0 | 1 | 1 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/30` |
| `[1/5,1/4)` | 0 | 0 | 1 | 1 | 1 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/20` |
| `[1/4,2/7)` | 0 | 1 | 1 | 1 | 1 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/28` |
| `[2/7,1/3)` | 0 | 1 | 1 | 1 | 2 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/21` |
| `[1/3,2/5)` | 0 | 1 | 1 | 2 | 2 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/15` |
| `[2/5,3/7)` | 0 | 1 | 2 | 2 | 2 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/35` |
| `[3/7,1/2)` | 0 | 1 | 2 | 2 | 3 | [0, 1, 3, 4, 5, 6] | [2, 7] | YES | `1/14` |
| `[1/2,4/7)` | 1 | 2 | 2 | 3 | 3 | [1, 2, 3, 4, 6, 7] | [0, 5] | YES | `1/14` |
| `[4/7,3/5)` | 1 | 2 | 2 | 3 | 4 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/35` |
| `[3/5,2/3)` | 1 | 2 | 3 | 3 | 4 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/15` |
| `[2/3,5/7)` | 1 | 2 | 3 | 4 | 4 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/21` |
| `[5/7,3/4)` | 1 | 2 | 3 | 4 | 5 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/28` |
| `[3/4,4/5)` | 1 | 3 | 3 | 4 | 5 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/20` |
| `[4/5,5/6)` | 1 | 3 | 4 | 4 | 5 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/30` |
| `[5/6,6/7)` | 1 | 3 | 4 | 5 | 5 | [1, 3, 4, 5, 6, 7] | [0, 2] | YES | `1/42` |
| `[6/7,1)` | 1 | 3 | 4 | 5 | 6 | [1, 3, 4, 5, 6, 7] | [0, 2] | YES | `1/7` |

**18 of 18 cells safe; |S| = 1 = 1.000000 > 1/2; surplus 1/2.**

### absent (1, 4)   E_non = [2, 3, 5, 6, 7]
| cell | t_2 | t_3 | t_5 | t_6 | t_7 | covered | U | safe | length |
|---|---|---|---|---|---|---|---|---|---|
| `[0,1/7)` | 0 | 0 | 0 | 0 | 0 | [0, 1, 3, 4, 5] | [2, 6, 7] | YES | `1/7` |
| `[1/7,1/6)` | 0 | 0 | 0 | 0 | 1 | [0, 1, 2, 3, 4, 5] | [6, 7] | YES | `1/42` |
| `[1/6,1/5)` | 0 | 0 | 0 | 1 | 1 | [0, 1, 2, 3, 4, 5] | [6, 7] | YES | `1/30` |
| `[1/5,2/7)` | 0 | 0 | 1 | 1 | 1 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `3/35` |
| `[2/7,1/3)` | 0 | 0 | 1 | 1 | 2 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/21` |
| `[1/3,2/5)` | 0 | 1 | 1 | 2 | 2 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/15` |
| `[2/5,3/7)` | 0 | 1 | 2 | 2 | 2 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/35` |
| `[3/7,1/2)` | 0 | 1 | 2 | 2 | 3 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/14` |
| `[1/2,4/7)` | 1 | 1 | 2 | 3 | 3 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/14` |
| `[4/7,3/5)` | 1 | 1 | 2 | 3 | 4 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/35` |
| `[3/5,2/3)` | 1 | 1 | 3 | 3 | 4 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/15` |
| `[2/3,5/7)` | 1 | 2 | 3 | 4 | 4 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/21` |
| `[5/7,4/5)` | 1 | 2 | 3 | 4 | 5 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `3/35` |
| `[4/5,5/6)` | 1 | 2 | 4 | 4 | 5 | [2, 3, 4, 5, 6, 7] | [0, 1] | YES | `1/30` |
| `[5/6,6/7)` | 1 | 2 | 4 | 5 | 5 | [2, 3, 4, 5, 6, 7] | [0, 1] | YES | `1/42` |
| `[6/7,1)` | 1 | 2 | 4 | 5 | 6 | [2, 3, 4, 6, 7] | [0, 1, 5] | YES | `1/7` |

**16 of 16 cells safe; |S| = 1 = 1.000000 > 1/2; surplus 1/2.**

### absent (1, 5)   E_non = [2, 3, 4, 6, 7]
| cell | t_2 | t_3 | t_4 | t_6 | t_7 | covered | U | safe | length |
|---|---|---|---|---|---|---|---|---|---|
| `[0,1/7)` | 0 | 0 | 0 | 0 | 0 | [0, 1, 2, 4, 5, 6] | [3, 7] | YES | `1/7` |
| `[1/7,1/6)` | 0 | 0 | 0 | 0 | 1 | [0, 1, 2, 4, 5, 6] | [3, 7] | YES | `1/42` |
| `[1/6,1/4)` | 0 | 0 | 0 | 1 | 1 | [0, 1, 2, 4, 5, 6] | [3, 7] | YES | `1/12` |
| `[1/4,2/7)` | 0 | 0 | 1 | 1 | 1 | [0, 1, 2, 4, 5] | [3, 6, 7] | YES | `1/28` |
| `[2/7,1/3)` | 0 | 0 | 1 | 1 | 2 | [0, 1, 2, 3, 4, 5] | [6, 7] | YES | `1/21` |
| `[1/3,3/7)` | 0 | 1 | 1 | 2 | 2 | [0, 1, 2, 3, 4, 5] | [6, 7] | YES | `2/21` |
| `[3/7,1/2)` | 0 | 1 | 1 | 2 | 3 | [0, 1, 2, 3, 4, 5] | [6, 7] | YES | `1/14` |
| `[1/2,4/7)` | 1 | 1 | 2 | 3 | 3 | [2, 3, 4, 5, 6, 7] | [0, 1] | YES | `1/14` |
| `[4/7,2/3)` | 1 | 1 | 2 | 3 | 4 | [2, 3, 4, 5, 6, 7] | [0, 1] | YES | `2/21` |
| `[2/3,5/7)` | 1 | 2 | 2 | 4 | 4 | [2, 3, 4, 5, 6, 7] | [0, 1] | YES | `1/21` |
| `[5/7,3/4)` | 1 | 2 | 2 | 4 | 5 | [2, 3, 5, 6, 7] | [0, 1, 4] | YES | `1/28` |
| `[3/4,5/6)` | 1 | 2 | 3 | 4 | 5 | [1, 2, 3, 5, 6, 7] | [0, 4] | YES | `1/12` |
| `[5/6,6/7)` | 1 | 2 | 3 | 5 | 5 | [1, 2, 3, 5, 6, 7] | [0, 4] | YES | `1/42` |
| `[6/7,1)` | 1 | 2 | 3 | 5 | 6 | [1, 2, 3, 5, 6, 7] | [0, 4] | YES | `1/7` |

**14 of 14 cells safe; |S| = 1 = 1.000000 > 1/2; surplus 1/2.**

### absent (1, 6)   E_non = [2, 3, 4, 5, 7]
| cell | t_2 | t_3 | t_4 | t_5 | t_7 | covered | U | safe | length |
|---|---|---|---|---|---|---|---|---|---|
| `[0,1/7)` | 0 | 0 | 0 | 0 | 0 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/7` |
| `[1/7,1/5)` | 0 | 0 | 0 | 0 | 1 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `2/35` |
| `[1/5,1/4)` | 0 | 0 | 0 | 1 | 1 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/20` |
| `[1/4,2/7)` | 0 | 0 | 1 | 1 | 1 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/28` |
| `[2/7,1/3)` | 0 | 0 | 1 | 1 | 2 | [0, 2, 3, 4, 5, 6] | [1, 7] | YES | `1/21` |
| `[1/3,2/5)` | 0 | 1 | 1 | 1 | 2 | [0, 2, 3, 4, 5, 6] | [1, 7] | YES | `1/15` |
| `[2/5,3/7)` | 0 | 1 | 1 | 2 | 2 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/35` |
| `[3/7,1/2)` | 0 | 1 | 1 | 2 | 3 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/14` |
| `[1/2,4/7)` | 1 | 1 | 2 | 2 | 3 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/14` |
| `[4/7,3/5)` | 1 | 1 | 2 | 2 | 4 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/35` |
| `[3/5,2/3)` | 1 | 1 | 2 | 3 | 4 | [1, 2, 3, 4, 5, 7] | [0, 6] | YES | `1/15` |
| `[2/3,5/7)` | 1 | 2 | 2 | 3 | 4 | [1, 2, 3, 4, 5, 7] | [0, 6] | YES | `1/21` |
| `[5/7,3/4)` | 1 | 2 | 2 | 3 | 5 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/28` |
| `[3/4,4/5)` | 1 | 2 | 3 | 3 | 5 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/20` |
| `[4/5,6/7)` | 1 | 2 | 3 | 4 | 5 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `2/35` |
| `[6/7,1)` | 1 | 2 | 3 | 4 | 6 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/7` |

**16 of 16 cells safe; |S| = 1 = 1.000000 > 1/2; surplus 1/2.**

### absent (1, 7)   E_non = [2, 3, 4, 5, 6]
| cell | t_2 | t_3 | t_4 | t_5 | t_6 | covered | U | safe | length |
|---|---|---|---|---|---|---|---|---|---|
| `[0,1/6)` | 0 | 0 | 0 | 0 | 0 | [0, 2, 3, 4, 5, 6] | [1, 7] | YES | `1/6` |
| `[1/6,1/5)` | 0 | 0 | 0 | 0 | 1 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/30` |
| `[1/5,1/4)` | 0 | 0 | 0 | 1 | 1 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/20` |
| `[1/4,1/3)` | 0 | 0 | 1 | 1 | 1 | [0, 1, 3, 4, 5, 6] | [2, 7] | YES | `1/12` |
| `[1/3,2/5)` | 0 | 1 | 1 | 1 | 2 | [0, 1, 2, 3, 4, 5, 6] | [7] | YES | `1/15` |
| `[2/5,1/2)` | 0 | 1 | 1 | 2 | 2 | [0, 1, 2, 4, 5, 6] | [3, 7] | YES | `1/10` |
| `[1/2,3/5)` | 1 | 1 | 2 | 2 | 3 | [1, 2, 3, 5, 6, 7] | [0, 4] | YES | `1/10` |
| `[3/5,2/3)` | 1 | 1 | 2 | 3 | 3 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/15` |
| `[2/3,3/4)` | 1 | 2 | 2 | 3 | 4 | [1, 2, 3, 4, 6, 7] | [0, 5] | YES | `1/12` |
| `[3/4,4/5)` | 1 | 2 | 3 | 3 | 4 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/20` |
| `[4/5,5/6)` | 1 | 2 | 3 | 4 | 4 | [1, 2, 3, 4, 5, 6, 7] | [0] | YES | `1/30` |
| `[5/6,1)` | 1 | 2 | 3 | 4 | 5 | [1, 2, 3, 4, 5, 7] | [0, 6] | YES | `1/6` |

**12 of 12 cells safe; |S| = 1 = 1.000000 > 1/2; surplus 1/2.**

### absent (2, 3)   E_non = [1, 4, 5, 6, 7]
| cell | t_1 | t_4 | t_5 | t_6 | t_7 | covered | U | safe | length |
|---|---|---|---|---|---|---|---|---|---|
| `[0,1/7)` | 0 | 0 | 0 | 0 | 0 | [0, 1, 2, 3, 4, 6, 7] | [5] | YES | `1/7` |
| `[1/7,1/6)` | 0 | 0 | 0 | 0 | 1 | [0, 1, 2, 3, 4, 6, 7] | [5] | YES | `1/42` |
| `[1/6,1/5)` | 0 | 0 | 0 | 1 | 1 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/30` |
| `[1/5,1/4)` | 0 | 0 | 1 | 1 | 1 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/20` |
| `[1/4,2/7)` | 0 | 1 | 1 | 1 | 1 | [0, 1, 2, 3, 5, 6, 7] | [4] | YES | `1/28` |
| `[2/7,1/3)` | 0 | 1 | 1 | 1 | 2 | [0, 1, 2, 3, 5, 6, 7] | [4] | YES | `1/21` |
| `[1/3,2/5)` | 0 | 1 | 1 | 2 | 2 | [0, 1, 2, 3, 5, 6, 7] | [4] | YES | `1/15` |
| `[2/5,3/7)` | 0 | 1 | 2 | 2 | 2 | [0, 1, 2, 3, 5, 6, 7] | [4] | YES | `1/35` |
| `[3/7,1/2)` | 0 | 1 | 2 | 2 | 3 | [0, 1, 3, 4, 5, 6, 7] | [2] | YES | `1/14` |
| `[1/2,4/7)` | 0 | 2 | 2 | 3 | 3 | [0, 1, 2, 3, 4, 6, 7] | [5] | YES | `1/14` |
| `[4/7,3/5)` | 0 | 2 | 2 | 3 | 4 | [0, 1, 2, 4, 5, 6, 7] | [3] | YES | `1/35` |
| `[3/5,2/3)` | 0 | 2 | 3 | 3 | 4 | [0, 1, 2, 4, 5, 6, 7] | [3] | YES | `1/15` |
| `[2/3,5/7)` | 0 | 2 | 3 | 4 | 4 | [0, 1, 2, 4, 5, 6, 7] | [3] | YES | `1/21` |
| `[5/7,3/4)` | 0 | 2 | 3 | 4 | 5 | [0, 1, 2, 4, 5, 6, 7] | [3] | YES | `1/28` |
| `[3/4,4/5)` | 0 | 3 | 3 | 4 | 5 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/20` |
| `[4/5,5/6)` | 0 | 3 | 4 | 4 | 5 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/30` |
| `[5/6,6/7)` | 0 | 3 | 4 | 5 | 5 | [0, 1, 3, 4, 5, 6, 7] | [2] | YES | `1/42` |
| `[6/7,1)` | 0 | 3 | 4 | 5 | 6 | [0, 1, 3, 4, 5, 6, 7] | [2] | YES | `1/7` |

**14 of 18 cells safe; |S| = 5/6 = 0.833333 > 1/2; surplus 1/3.**

### absent (2, 5)   E_non = [1, 3, 4, 6, 7]
| cell | t_1 | t_3 | t_4 | t_6 | t_7 | covered | U | safe | length |
|---|---|---|---|---|---|---|---|---|---|
| `[0,1/7)` | 0 | 0 | 0 | 0 | 0 | [0, 1, 2, 4, 5, 6, 7] | [3] | YES | `1/7` |
| `[1/7,1/6)` | 0 | 0 | 0 | 0 | 1 | [0, 1, 2, 4, 5, 6, 7] | [3] | YES | `1/42` |
| `[1/6,1/4)` | 0 | 0 | 0 | 1 | 1 | [0, 1, 2, 4, 5, 6, 7] | [3] | YES | `1/12` |
| `[1/4,2/7)` | 0 | 0 | 1 | 1 | 1 | [0, 1, 2, 5, 7] | [3, 4, 6] | YES | `1/28` |
| `[2/7,1/3)` | 0 | 0 | 1 | 1 | 2 | [0, 1, 2, 3, 5, 7] | [4, 6] | YES | `1/21` |
| `[1/3,3/7)` | 0 | 1 | 1 | 2 | 2 | [0, 1, 2, 3, 5, 7] | [4, 6] | YES | `2/21` |
| `[3/7,1/2)` | 0 | 1 | 1 | 2 | 3 | [0, 1, 2, 3, 4, 5, 7] | [6] | YES | `1/14` |
| `[1/2,4/7)` | 0 | 1 | 2 | 3 | 3 | [0, 2, 3, 4, 5, 6, 7] | [1] | YES | `1/14` |
| `[4/7,2/3)` | 0 | 1 | 2 | 3 | 4 | [0, 2, 4, 5, 6, 7] | [1, 3] | YES | `2/21` |
| `[2/3,5/7)` | 0 | 2 | 2 | 4 | 4 | [0, 2, 4, 5, 6, 7] | [1, 3] | YES | `1/21` |
| `[5/7,3/4)` | 0 | 2 | 2 | 4 | 5 | [0, 2, 5, 6, 7] | [1, 3, 4] | YES | `1/28` |
| `[3/4,5/6)` | 0 | 2 | 3 | 4 | 5 | [0, 1, 2, 3, 5, 6, 7] | [4] | YES | `1/12` |
| `[5/6,6/7)` | 0 | 2 | 3 | 5 | 5 | [0, 1, 2, 3, 5, 6, 7] | [4] | YES | `1/42` |
| `[6/7,1)` | 0 | 2 | 3 | 5 | 6 | [0, 1, 2, 3, 5, 6, 7] | [4] | YES | `1/7` |

**14 of 14 cells safe; |S| = 1 = 1.000000 > 1/2; surplus 1/2.**

### absent (2, 7)   E_non = [1, 3, 4, 5, 6]
| cell | t_1 | t_3 | t_4 | t_5 | t_6 | covered | U | safe | length |
|---|---|---|---|---|---|---|---|---|---|
| `[0,1/6)` | 0 | 0 | 0 | 0 | 0 | [0, 2, 3, 4, 5, 6, 7] | [1] | YES | `1/6` |
| `[1/6,1/5)` | 0 | 0 | 0 | 0 | 1 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/30` |
| `[1/5,1/4)` | 0 | 0 | 0 | 1 | 1 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/20` |
| `[1/4,1/3)` | 0 | 0 | 1 | 1 | 1 | [0, 1, 3, 5, 6, 7] | [2, 4] | YES | `1/12` |
| `[1/3,2/5)` | 0 | 1 | 1 | 1 | 2 | [0, 1, 2, 3, 5, 6, 7] | [4] | YES | `1/15` |
| `[2/5,1/2)` | 0 | 1 | 1 | 2 | 2 | [0, 1, 2, 5, 6, 7] | [3, 4] | YES | `1/10` |
| `[1/2,3/5)` | 0 | 1 | 2 | 2 | 3 | [0, 1, 2, 5, 6, 7] | [3, 4] | YES | `1/10` |
| `[3/5,2/3)` | 0 | 1 | 2 | 3 | 3 | [0, 1, 2, 4, 5, 6, 7] | [3] | YES | `1/15` |
| `[2/3,3/4)` | 0 | 2 | 2 | 3 | 4 | [0, 1, 2, 4, 6, 7] | [3, 5] | YES | `1/12` |
| `[3/4,4/5)` | 0 | 2 | 3 | 3 | 4 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/20` |
| `[4/5,5/6)` | 0 | 2 | 3 | 4 | 4 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/30` |
| `[5/6,1)` | 0 | 2 | 3 | 4 | 5 | [0, 1, 2, 3, 4, 5, 7] | [6] | YES | `1/6` |

**8 of 12 cells safe; |S| = 5/6 = 0.833333 > 1/2; surplus 1/3.**

### absent (3, 4)   E_non = [1, 2, 5, 6, 7]
| cell | t_1 | t_2 | t_5 | t_6 | t_7 | covered | U | safe | length |
|---|---|---|---|---|---|---|---|---|---|
| `[0,1/7)` | 0 | 0 | 0 | 0 | 0 | [0, 1, 3, 4, 7] | [2, 5, 6] | YES | `1/7` |
| `[1/7,1/6)` | 0 | 0 | 0 | 0 | 1 | [0, 1, 2, 3, 4, 7] | [5, 6] | YES | `1/42` |
| `[1/6,1/5)` | 0 | 0 | 0 | 1 | 1 | [0, 1, 2, 3, 4, 5, 7] | [6] | YES | `1/30` |
| `[1/5,2/7)` | 0 | 0 | 1 | 1 | 1 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `3/35` |
| `[2/7,1/3)` | 0 | 0 | 1 | 1 | 2 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/21` |
| `[1/3,2/5)` | 0 | 0 | 1 | 2 | 2 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/15` |
| `[2/5,3/7)` | 0 | 0 | 2 | 2 | 2 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/35` |
| `[3/7,1/2)` | 0 | 0 | 2 | 2 | 3 | [0, 1, 3, 4, 5, 6, 7] | [2] | YES | `1/14` |
| `[1/2,4/7)` | 0 | 1 | 2 | 3 | 3 | [0, 1, 2, 3, 4, 6, 7] | [5] | YES | `1/14` |
| `[4/7,3/5)` | 0 | 1 | 2 | 3 | 4 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/35` |
| `[3/5,2/3)` | 0 | 1 | 3 | 3 | 4 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/15` |
| `[2/3,5/7)` | 0 | 1 | 3 | 4 | 4 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/21` |
| `[5/7,4/5)` | 0 | 1 | 3 | 4 | 5 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `3/35` |
| `[4/5,5/6)` | 0 | 1 | 4 | 4 | 5 | [0, 2, 3, 4, 5, 6, 7] | [1] | YES | `1/30` |
| `[5/6,6/7)` | 0 | 1 | 4 | 5 | 5 | [0, 3, 4, 5, 6, 7] | [1, 2] | YES | `1/42` |
| `[6/7,1)` | 0 | 1 | 4 | 5 | 6 | [0, 3, 4, 6, 7] | [1, 2, 5] | YES | `1/7` |

**8 of 16 cells safe; |S| = 19/35 = 0.542857 > 1/2; surplus 3/70.**

### absent (3, 5)   E_non = [1, 2, 4, 6, 7]
| cell | t_1 | t_2 | t_4 | t_6 | t_7 | covered | U | safe | length |
|---|---|---|---|---|---|---|---|---|---|
| `[0,1/7)` | 0 | 0 | 0 | 0 | 0 | [0, 1, 2, 4, 6, 7] | [3, 5] | YES | `1/7` |
| `[1/7,1/6)` | 0 | 0 | 0 | 0 | 1 | [0, 1, 2, 4, 6, 7] | [3, 5] | YES | `1/42` |
| `[1/6,1/4)` | 0 | 0 | 0 | 1 | 1 | [0, 1, 2, 4, 5, 6, 7] | [3] | YES | `1/12` |
| `[1/4,2/7)` | 0 | 0 | 1 | 1 | 1 | [0, 1, 2, 4, 5, 7] | [3, 6] | YES | `1/28` |
| `[2/7,1/3)` | 0 | 0 | 1 | 1 | 2 | [0, 1, 2, 3, 4, 5, 7] | [6] | YES | `1/21` |
| `[1/3,3/7)` | 0 | 0 | 1 | 2 | 2 | [0, 1, 2, 3, 4, 5, 7] | [6] | YES | `2/21` |
| `[3/7,1/2)` | 0 | 0 | 1 | 2 | 3 | [0, 1, 3, 4, 5, 7] | [2, 6] | YES | `1/14` |
| `[1/2,4/7)` | 0 | 1 | 2 | 3 | 3 | [0, 2, 3, 4, 6, 7] | [1, 5] | YES | `1/14` |
| `[4/7,2/3)` | 0 | 1 | 2 | 3 | 4 | [0, 2, 3, 4, 5, 6, 7] | [1] | YES | `2/21` |
| `[2/3,5/7)` | 0 | 1 | 2 | 4 | 4 | [0, 2, 3, 4, 5, 6, 7] | [1] | YES | `1/21` |
| `[5/7,3/4)` | 0 | 1 | 2 | 4 | 5 | [0, 2, 3, 5, 6, 7] | [1, 4] | YES | `1/28` |
| `[3/4,5/6)` | 0 | 1 | 3 | 4 | 5 | [0, 1, 2, 3, 5, 6, 7] | [4] | YES | `1/12` |
| `[5/6,6/7)` | 0 | 1 | 3 | 5 | 5 | [0, 1, 3, 5, 6, 7] | [2, 4] | YES | `1/42` |
| `[6/7,1)` | 0 | 1 | 3 | 5 | 6 | [0, 1, 3, 5, 6, 7] | [2, 4] | YES | `1/7` |

**14 of 14 cells safe; |S| = 1 = 1.000000 > 1/2; surplus 1/2.**

### absent (3, 6)   E_non = [1, 2, 4, 5, 7]
| cell | t_1 | t_2 | t_4 | t_5 | t_7 | covered | U | safe | length |
|---|---|---|---|---|---|---|---|---|---|
| `[0,1/7)` | 0 | 0 | 0 | 0 | 0 | [0, 1, 2, 3, 4, 6, 7] | [5] | YES | `1/7` |
| `[1/7,1/5)` | 0 | 0 | 0 | 0 | 1 | [0, 1, 2, 3, 4, 6, 7] | [5] | YES | `2/35` |
| `[1/5,1/4)` | 0 | 0 | 0 | 1 | 1 | [0, 1, 2, 3, 4, 6, 7] | [5] | YES | `1/20` |
| `[1/4,2/7)` | 0 | 0 | 1 | 1 | 1 | [0, 1, 2, 3, 4, 6, 7] | [5] | YES | `1/28` |
| `[2/7,2/5)` | 0 | 0 | 1 | 1 | 2 | [0, 2, 3, 4, 6, 7] | [1, 5] | YES | `4/35` |
| `[2/5,3/7)` | 0 | 0 | 1 | 2 | 2 | [0, 1, 2, 3, 4, 6, 7] | [5] | YES | `1/35` |
| `[3/7,1/2)` | 0 | 0 | 1 | 2 | 3 | [0, 1, 3, 4, 6, 7] | [2, 5] | YES | `1/14` |
| `[1/2,4/7)` | 0 | 1 | 2 | 2 | 3 | [0, 1, 3, 4, 6, 7] | [2, 5] | YES | `1/14` |
| `[4/7,3/5)` | 0 | 1 | 2 | 2 | 4 | [0, 1, 3, 4, 5, 6, 7] | [2] | YES | `1/35` |
| `[3/5,5/7)` | 0 | 1 | 2 | 3 | 4 | [0, 1, 3, 4, 5, 7] | [2, 6] | YES | `4/35` |
| `[5/7,3/4)` | 0 | 1 | 2 | 3 | 5 | [0, 1, 3, 4, 5, 6, 7] | [2] | YES | `1/28` |
| `[3/4,4/5)` | 0 | 1 | 3 | 3 | 5 | [0, 1, 3, 4, 5, 6, 7] | [2] | YES | `1/20` |
| `[4/5,6/7)` | 0 | 1 | 3 | 4 | 5 | [0, 1, 3, 4, 5, 6, 7] | [2] | YES | `2/35` |
| `[6/7,1)` | 0 | 1 | 3 | 4 | 6 | [0, 1, 3, 4, 5, 6, 7] | [2] | YES | `1/7` |

**14 of 14 cells safe; |S| = 1 = 1.000000 > 1/2; surplus 1/2.**

### absent (3, 7)   E_non = [1, 2, 4, 5, 6]
| cell | t_1 | t_2 | t_4 | t_5 | t_6 | covered | U | safe | length |
|---|---|---|---|---|---|---|---|---|---|
| `[0,1/6)` | 0 | 0 | 0 | 0 | 0 | [0, 2, 3, 4, 6, 7] | [1, 5] | YES | `1/6` |
| `[1/6,1/5)` | 0 | 0 | 0 | 0 | 1 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/30` |
| `[1/5,1/4)` | 0 | 0 | 0 | 1 | 1 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/20` |
| `[1/4,1/3)` | 0 | 0 | 1 | 1 | 1 | [0, 1, 3, 4, 5, 6, 7] | [2] | YES | `1/12` |
| `[1/3,2/5)` | 0 | 0 | 1 | 1 | 2 | [0, 1, 3, 4, 5, 6, 7] | [2] | YES | `1/15` |
| `[2/5,1/2)` | 0 | 0 | 1 | 2 | 2 | [0, 1, 4, 5, 6, 7] | [2, 3] | YES | `1/10` |
| `[1/2,3/5)` | 0 | 1 | 2 | 2 | 3 | [0, 1, 2, 3, 6, 7] | [4, 5] | YES | `1/10` |
| `[3/5,2/3)` | 0 | 1 | 2 | 3 | 3 | [0, 1, 2, 3, 4, 6, 7] | [5] | YES | `1/15` |
| `[2/3,3/4)` | 0 | 1 | 2 | 3 | 4 | [0, 1, 2, 3, 4, 6, 7] | [5] | YES | `1/12` |
| `[3/4,4/5)` | 0 | 1 | 3 | 3 | 4 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/20` |
| `[4/5,5/6)` | 0 | 1 | 3 | 4 | 4 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/30` |
| `[5/6,1)` | 0 | 1 | 3 | 4 | 5 | [0, 1, 3, 4, 5, 7] | [2, 6] | YES | `1/6` |

**8 of 12 cells safe; |S| = 5/6 = 0.833333 > 1/2; surplus 1/3.**

### absent (4, 5)   E_non = [1, 2, 3, 6, 7]
| cell | t_1 | t_2 | t_3 | t_6 | t_7 | covered | U | safe | length |
|---|---|---|---|---|---|---|---|---|---|
| `[0,1/7)` | 0 | 0 | 0 | 0 | 0 | [0, 1, 4, 5, 7] | [2, 3, 6] | YES | `1/7` |
| `[1/7,1/6)` | 0 | 0 | 0 | 0 | 1 | [0, 1, 2, 4, 5, 7] | [3, 6] | YES | `1/42` |
| `[1/6,2/7)` | 0 | 0 | 0 | 1 | 1 | [0, 1, 2, 4, 5, 7] | [3, 6] | YES | `5/42` |
| `[2/7,1/3)` | 0 | 0 | 0 | 1 | 2 | [0, 1, 2, 3, 4, 5, 7] | [6] | YES | `1/21` |
| `[1/3,3/7)` | 0 | 0 | 1 | 2 | 2 | [0, 1, 2, 3, 4, 5, 7] | [6] | YES | `2/21` |
| `[3/7,1/2)` | 0 | 0 | 1 | 2 | 3 | [0, 1, 2, 3, 4, 5, 7] | [6] | YES | `1/14` |
| `[1/2,4/7)` | 0 | 1 | 1 | 3 | 3 | [0, 2, 3, 4, 5, 6, 7] | [1] | YES | `1/14` |
| `[4/7,2/3)` | 0 | 1 | 1 | 3 | 4 | [0, 2, 3, 4, 5, 6, 7] | [1] | YES | `2/21` |
| `[2/3,5/7)` | 0 | 1 | 2 | 4 | 4 | [0, 2, 3, 4, 5, 6, 7] | [1] | YES | `1/21` |
| `[5/7,5/6)` | 0 | 1 | 2 | 4 | 5 | [0, 2, 3, 5, 6, 7] | [1, 4] | YES | `5/42` |
| `[5/6,6/7)` | 0 | 1 | 2 | 5 | 5 | [0, 2, 3, 5, 6, 7] | [1, 4] | YES | `1/42` |
| `[6/7,1)` | 0 | 1 | 2 | 5 | 6 | [0, 2, 3, 6, 7] | [1, 4, 5] | YES | `1/7` |

**12 of 12 cells safe; |S| = 1 = 1.000000 > 1/2; surplus 1/2.**

### absent (4, 7)   E_non = [1, 2, 3, 5, 6]
| cell | t_1 | t_2 | t_3 | t_5 | t_6 | covered | U | safe | length |
|---|---|---|---|---|---|---|---|---|---|
| `[0,1/6)` | 0 | 0 | 0 | 0 | 0 | [0, 3, 4, 5, 7] | [1, 2, 6] | YES | `1/6` |
| `[1/6,1/5)` | 0 | 0 | 0 | 0 | 1 | [0, 1, 3, 4, 5, 7] | [2, 6] | YES | `1/30` |
| `[1/5,1/3)` | 0 | 0 | 0 | 1 | 1 | [0, 1, 3, 4, 5, 6, 7] | [2] | YES | `2/15` |
| `[1/3,2/5)` | 0 | 0 | 1 | 1 | 2 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/15` |
| `[2/5,1/2)` | 0 | 0 | 1 | 2 | 2 | [0, 1, 2, 4, 5, 6, 7] | [3] | YES | `1/10` |
| `[1/2,3/5)` | 0 | 1 | 1 | 2 | 3 | [0, 1, 2, 3, 5, 6, 7] | [4] | YES | `1/10` |
| `[3/5,2/3)` | 0 | 1 | 1 | 3 | 3 | [0, 1, 2, 3, 4, 5, 6, 7] | - | no | `1/15` |
| `[2/3,4/5)` | 0 | 1 | 2 | 3 | 4 | [0, 1, 2, 3, 4, 6, 7] | [5] | YES | `2/15` |
| `[4/5,5/6)` | 0 | 1 | 2 | 4 | 4 | [0, 2, 3, 4, 6, 7] | [1, 5] | YES | `1/30` |
| `[5/6,1)` | 0 | 1 | 2 | 4 | 5 | [0, 2, 3, 4, 7] | [1, 5, 6] | YES | `1/6` |

**8 of 10 cells safe; |S| = 13/15 = 0.866667 > 1/2; surplus 11/30.**

### absent (5, 6)   E_non = [1, 2, 3, 4, 7]
| cell | t_1 | t_2 | t_3 | t_4 | t_7 | covered | U | safe | length |
|---|---|---|---|---|---|---|---|---|---|
| `[0,1/7)` | 0 | 0 | 0 | 0 | 0 | [0, 1, 2, 4, 5, 6, 7] | [3] | YES | `1/7` |
| `[1/7,1/4)` | 0 | 0 | 0 | 0 | 1 | [0, 1, 2, 4, 5, 6, 7] | [3] | YES | `3/28` |
| `[1/4,2/7)` | 0 | 0 | 0 | 1 | 1 | [0, 1, 2, 4, 5, 7] | [3, 6] | YES | `1/28` |
| `[2/7,1/3)` | 0 | 0 | 0 | 1 | 2 | [0, 2, 3, 4, 5, 7] | [1, 6] | YES | `1/21` |
| `[1/3,3/7)` | 0 | 0 | 1 | 1 | 2 | [0, 2, 3, 4, 5, 7] | [1, 6] | YES | `2/21` |
| `[3/7,1/2)` | 0 | 0 | 1 | 1 | 3 | [0, 2, 3, 4, 5, 7] | [1, 6] | YES | `1/14` |
| `[1/2,4/7)` | 0 | 1 | 1 | 2 | 3 | [0, 2, 3, 4, 5, 7] | [1, 6] | YES | `1/14` |
| `[4/7,2/3)` | 0 | 1 | 1 | 2 | 4 | [0, 2, 3, 4, 5, 7] | [1, 6] | YES | `2/21` |
| `[2/3,5/7)` | 0 | 1 | 2 | 2 | 4 | [0, 2, 3, 4, 5, 7] | [1, 6] | YES | `1/21` |
| `[5/7,3/4)` | 0 | 1 | 2 | 2 | 5 | [0, 2, 3, 5, 6, 7] | [1, 4] | YES | `1/28` |
| `[3/4,6/7)` | 0 | 1 | 2 | 3 | 5 | [0, 1, 2, 3, 5, 6, 7] | [4] | YES | `3/28` |
| `[6/7,1)` | 0 | 1 | 2 | 3 | 6 | [0, 1, 2, 3, 5, 6, 7] | [4] | YES | `1/7` |

**12 of 12 cells safe; |S| = 1 = 1.000000 > 1/2; surplus 1/2.**

### absent (5, 7)   E_non = [1, 2, 3, 4, 6]
| cell | t_1 | t_2 | t_3 | t_4 | t_6 | covered | U | safe | length |
|---|---|---|---|---|---|---|---|---|---|
| `[0,1/6)` | 0 | 0 | 0 | 0 | 0 | [0, 2, 4, 5, 6, 7] | [1, 3] | YES | `1/6` |
| `[1/6,1/4)` | 0 | 0 | 0 | 0 | 1 | [0, 1, 2, 4, 5, 6, 7] | [3] | YES | `1/12` |
| `[1/4,1/3)` | 0 | 0 | 0 | 1 | 1 | [0, 1, 4, 5, 7] | [2, 3, 6] | YES | `1/12` |
| `[1/3,1/2)` | 0 | 0 | 1 | 1 | 2 | [0, 1, 2, 4, 5, 7] | [3, 6] | YES | `1/6` |
| `[1/2,2/3)` | 0 | 1 | 1 | 2 | 3 | [0, 2, 3, 5, 6, 7] | [1, 4] | YES | `1/6` |
| `[2/3,3/4)` | 0 | 1 | 2 | 2 | 4 | [0, 2, 3, 6, 7] | [1, 4, 5] | YES | `1/12` |
| `[3/4,5/6)` | 0 | 1 | 2 | 3 | 4 | [0, 1, 2, 3, 5, 6, 7] | [4] | YES | `1/12` |
| `[5/6,1)` | 0 | 1 | 2 | 3 | 5 | [0, 1, 2, 3, 5, 7] | [4, 6] | YES | `1/6` |

**8 of 8 cells safe; |S| = 1 = 1.000000 > 1/2; surplus 1/2.**

### absent (6, 7)   E_non = [1, 2, 3, 4, 5]
| cell | t_1 | t_2 | t_3 | t_4 | t_5 | covered | U | safe | length |
|---|---|---|---|---|---|---|---|---|---|
| `[0,1/5)` | 0 | 0 | 0 | 0 | 0 | [0, 2, 3, 4, 5, 6, 7] | [1] | YES | `1/5` |
| `[1/5,1/4)` | 0 | 0 | 0 | 0 | 1 | [0, 2, 3, 4, 5, 6, 7] | [1] | YES | `1/20` |
| `[1/4,1/3)` | 0 | 0 | 0 | 1 | 1 | [0, 3, 4, 5, 6, 7] | [1, 2] | YES | `1/12` |
| `[1/3,2/5)` | 0 | 0 | 1 | 1 | 1 | [0, 2, 3, 4, 5, 6, 7] | [1] | YES | `1/15` |
| `[2/5,1/2)` | 0 | 0 | 1 | 1 | 2 | [0, 1, 2, 4, 5, 6, 7] | [3] | YES | `1/10` |
| `[1/2,3/5)` | 0 | 1 | 1 | 2 | 2 | [0, 1, 2, 3, 5, 6, 7] | [4] | YES | `1/10` |
| `[3/5,2/3)` | 0 | 1 | 1 | 2 | 3 | [0, 1, 2, 3, 4, 5, 7] | [6] | YES | `1/15` |
| `[2/3,3/4)` | 0 | 1 | 2 | 2 | 3 | [0, 1, 2, 3, 4, 7] | [5, 6] | YES | `1/12` |
| `[3/4,4/5)` | 0 | 1 | 2 | 3 | 3 | [0, 1, 2, 3, 4, 5, 7] | [6] | YES | `1/20` |
| `[4/5,1)` | 0 | 1 | 2 | 3 | 4 | [0, 1, 2, 3, 4, 5, 7] | [6] | YES | `1/5` |

**10 of 10 cells safe; |S| = 1 = 1.000000 > 1/2; surplus 1/2.**
