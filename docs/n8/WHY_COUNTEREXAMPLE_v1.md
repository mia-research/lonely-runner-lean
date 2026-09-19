# Why the largest-flank counterexample exists

**Status of this document.** Every numbered claim carries a grade.
Lean witness: `experiments/n8/LastClass_v1.lean` (8 theorems, 0 errors, all
`[propext, Classical.choice, Quot.sound]`); output `experiments/n8/LastClass_v1.out`.
Scripts: `experiments/n8/why_counterexample_v1.py`, `second_class_v2.py`,
`lcm_minus_one_v1.py`.

---

## 0. The object

The counterexample refuting hypothesis `H` (commit `2b253c5`) is the mover multiset

```
((1,2), (1,2), (1,8), (3,8), (5,8), (7,8))
```

realised as the arrangement `[-4, 0, 1, 3, 4, 5, 7, 8]`, subject `0`, largest flank
`e = 8`. It is live and shadowed: no clear opening for `k < 200,000`.

The question is why such a thing exists at all, given that an exhaustive sweep found
**0 shadowing multisets among 74,613 with every denominator `q ≤ 7`** and the first
**21 of 230,230** at `q = 8`.

---

## 1. The residue has a closed form

**[PROVED — `LastClass.residue_form`]** For `0 < p < n` and `0 < q`,

```
(p * (n*k + 1)) mod (n*q)  =  n * u + p ,      u = (p*k) mod q .
```

The blocking test `min(r, n*q - r) < q` therefore reads off `u` alone. Two branches:

* low: `n*u + p < q`
* high: `n*u + p > (n-1)*q`

## 2. A mover blocks one class, or two, and the threshold is `p + q > n`

**[PROVED — `LastClass.only_zero_class`]** If `p + q ≤ n`, the low branch forces `u = 0`
and the high branch is unreachable. The mover blocks **only** `q ∣ p*k`.

**[PROVED — `LastClass.second_class_blocks`]** If `n < p + q` (with `q ≤ n`), the class
`u = q - 1` is blocked.

**[VERIFIED — `second_class_v2.py` [A], 1560 cases, `n = 3..24`, `q ≤ n`]** For `q ≤ n`
the blocked set is exactly

```
{0}  ∪  ( {-p⁻¹ mod q}  iff  p + q > n ).
```

Scope note: this two-class form is claimed **only for `q ≤ n`**. For `q > n` both branches
admit several `u` and the set is larger; an earlier statement of the law without the
`q ≤ n` restriction was false and is withdrawn (6,423 mismatches over `q < 4n`).

## 3. The last class belongs to `1/n` alone

**[PROVED — `LastClass.last_class_forces`]** For `0 < p < q ≤ n` and `2 ≤ n`: if the mover
`p/q` blocks an index with `k ≡ -1 (mod q)`, then `p = 1` **and** `q = n`.

The proof needs no inverses. With `k ≡ -1` the residue is `n*(q-p) + p`, whose distance to
`n*q` is `p*(n-1)`. The low side exceeds `q`, so blocking forces `p*(n-1) < q ≤ n`, which
forces `p = 1`, and then `n - 1 < q ≤ n` forces `q = n`.

**[VERIFIED — `second_class_v2.py` [B'], 1560 cases]** The `iff` direction also holds:
within `q ≤ n`, `1/n` is the *only* mover blocking the last class.

## 4. This makes the `q ≤ n-1` table a theorem

**[PROVED — `LastClass.lcm_minus_one_clear`]** If every mover's denominator divides `L`
and is at most `n - 1`, then the index `k = L - 1` is clear for all of them at once.

Each mover has `k ≡ -1 (mod q_i)` at `k = L - 1`, so §3 applies and would force
`q_i = n`, contradicting `q_i ≤ n - 1`.

**[PROVED — `LastClass.shadow_needs_full_denom`]** Contrapositive: shadowing the index
`L - 1` forces some mover to have `q ≥ n`.

This holds for **any number of movers and any order `n`** — it is not six-mover,
not order-8, and not exhaustive-table evidence. It supersedes the sweep as the reason.

**[VERIFIED]** `lcm_minus_one_v1.py`: 74,613/74,613 exhaustive (`n = 8`, six movers,
`q ≤ 7`) and 44,000/44,000 random (`n = 3..13`, variable mover count). For the best
`q ≤ 7` set `((1,2),(1,3),(4,5),(5,6),(2,7),(3,7))` with `L = 210`, the uncovered set is
`{29, 47, 53, 83, 89, 113, 137, 167, 173, 179, 197, 209}` and contains `209 = L - 1`.

## 5. What the counterexample then has to look like

At `n = 8` the core must contain `1/8`. It does, and more:

**[VERIFIED — `why_counterexample_v1.py`, `why2.py`]** For `q | 8`, the blocked classes
mod 8 are

| mover | blocked `k` mod 8 |
|---|---|
| `1/2` | `0, 2, 4, 6` |
| `1/8` | `0, 7` |
| `3/8` | `0, 5` |
| `5/8` | `0, 3` |
| `7/8` | `0, 1` |

The four eighths block `k ≡ 0` and `k ≡ 7p⁻¹`. The units mod 8 are the **Klein group**,
self-inverse, so `7p⁻¹ = 7p`, and `p ↦ 7p` permutes `{1,3,5,7}`: the four eighths cover
the four odd residues, one each. The half covers all four evens in a single mover,
because `2 | 8`. Five movers saturate `ℤ/8`.

Consequences, all **[VERIFIED — exhaustive over the `q ≤ 8` pool]**:

1. All 21 shadowing multisets contain all four eighths. Dropping any one frees exactly
   one odd residue (`1/8 → 7`, `3/8 → 5`, `5/8 → 3`, `7/8 → 1`).
2. All 21 are the **same core** `{1/2, 1/8, 3/8, 5/8, 7/8}` plus one entirely free mover.
3. The free mover ranges over the whole 21-element pool — which is why the count is 21.
   The shadowing configuration at `q ≤ 8` is **unique up to that one free slot**.

---

## 6. The answer

The counterexample exists because the index class `k ≡ -1` is reachable only at
denominator exactly `n`, and at `n = 8` the units mod 8 form the Klein group, so the
four movers `1/8, 3/8, 5/8, 7/8` — being self-inverse — partition the odd classes between
them while the single mover `1/2` takes every even class at once. Five movers then leave
nothing.

Neither ingredient is available below `q = n`: §4 proves it.

## 7. The same boundary, now with a reason

Three facts already on record placed the break at `b = 8 = n`:

* `Rescale.small_b_blocks_iff` holds for `b ≤ 7` and fails at `b = 8`.
* Theorem 4.8's `n-1` constant recurs at `b ≤ 7` and breaks at `b = 8`.
* The shadowing tables: 0 at `q ≤ 7`, first instance at `q = 8`.

All three are the `p + q > n` threshold of §2 read at `p = 1`: the mover `1/q` acquires
its second blocked class exactly when `q > n - 1`. That is one mechanism, not three
coincidences.

## 8. What this does not settle

* It does not prove Existence at order 8. It explains one refutation.
* §4 bounds shadowing by denominator, not by flank structure; a live flank may carry
  denominators `≥ n` for reasons unrelated to shadowing.
* The `q ≤ n` restriction in §2–§3 is real. Nothing here constrains `q > n`, and the
  counterexample's own denominators sit at exactly `q = n`.
