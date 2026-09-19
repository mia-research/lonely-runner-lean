# The two open frontiers: what holds, what does not, and what is actually missing

The arithmetization frame is right, and the empirical results hold. Two of the proposed
"why it cannot fail" arguments do not, and both are refuted by configurations already in the
record. Scripts: `subdensity_check_v1.py`, `frontier_tests_v1.py`.

---

## 1. What holds

**[VERIFIED]** Both frontiers clear, in the framework's own candidate set
`C(s) = {(8q+1)/s_k}` with clearing decided by `ArithForm.near_iff_int`:

| frontier | profiles | failures | min clear candidates | median |
|---|---|---|---|---|
| Branch B, mixed scales (integer, some `8 ∣ s`) | 2,254 | **0** | 2 | 14 |
| Rational readings (no unit speed, `s₁ > 1`) | 5,000 | **0** | 8 | 27 |

The reduction they rest on is proved: the covering question is a finite conjunction of integer
inequalities (`GapRule`, `ReachRule`, `ArithForm`), and clearing is
`(sᵢ·A) mod 8s_k ∈ [s_k, 7s_k]` exactly.

**A caution on the margin.** The minimum clear-candidate count is **enumeration-dependent**. In
the enumeration above (`q < s_k` at each reading `s_k`) the minima are **2** and **8**, not
comfortable figures. A margin quoted as "240" or "176" is a property of how the candidate set was
swept, not a structural reserve, and should not be leaned on.

## 2. Sub-density — **REFUTED**, by configurations already on file

The argument: mean active blocker count is `1.19` / `1.47`, well below 6, so total blockade is
impossible.

It does not follow, and the record already contains the counterexamples. Taking the extremal
shadowed set `(2,3,4,5,6,7,16)` and measuring mean blockers per opening:

| flank `e` | mean active blockers | every opening blocked? |
|---|---|---|
| 3 | **1.0000** | **yes** |
| 4 | **1.2500** | **yes** |
| 5 | **1.4000** | **yes** |
| 6 | 2.0000 | yes |
| 7 | 1.5714 | yes |
| **16** | **1.5000** | **no — this is the clear one** |

A mean of exactly `1.0` with total blockade: if every opening carries exactly one blocker, the
mean is 1 and the blockade is complete. **Mean blocker count is anti-correlated with clearance
here** — the single clear flank has the *highest* mean of the seven. The statistic carries no
information about blockade.

The largest-flank counterexample `[-4,1,3,4,5,7,8]`, `e = 8`, is the same: mean `2.0000`, every
opening blocked.

This is the **counting / density route**, already on the do-not-re-attempt list with the reason
*"joint density sits below the product of conditionals; correlation is adverse."* Six blockers at
`1/4` each give exactly `1.5`, and the wall is that `6 × 1/4 > 1` permits total cover while the
mean stays low.

Related: **each disparity does not block exactly `1/4`.** The exact count is proved —
`c·gcd(d,e)` of the `e` openings (`CoverCount.cover_count_gcd`), a fraction of `c/q`. Measured
over 135 `(d,e)` pairs the fraction takes **17 distinct values from 0 to 0.5**, and is exactly
`1/4` in **28 of 135**.

## 3. Integrality forcing — **does not preclude blockade**

The argument: `GapRule` gives gap width `N/(sᵢs_k)` with `N ∈ ℤ`, so gaps cannot be arbitrarily
thin; zones either overlap completely or leave a gap `≥ 1/(sᵢs_k)`.

The `N ≥ 1` branch is sound and proved. But `N ≤ 0` **is** the overlap case, and overlap is
precisely what blockade looks like. **[VERIFIED]** on the shadowed flanks of `(2,3,4,5,6,7,16)`:
**551 of 756** zone pairs have `N ≤ 0`.

`GapRule` bounds the gaps **that exist**; it does not make them exist. It is a lower bound on a
witness's room, not an existence proof.

## 4. The structural reason both frontiers are still open

Of the four tools named, sorted by what they can do:

| tool | what it does | can it establish a witness exists? |
|---|---|---|
| candidate set `C(s)` + `finite_check` | reduces to a finite check | **no** — it makes the question decidable per profile |
| `ArithForm.near_iff_int` | exact integer congruence | **no** — a restatement, exact and division-free |
| `GapRule` | lower-bounds gaps that exist | **no** — §3 |
| `edge_witness_both` | *if* the clear set is non-empty, it contains an edge witness | **no** — conditional on non-emptiness, which is the thing in question |

**None of them can prove non-emptiness**, and non-emptiness is exactly what both frontiers need.
They reduce the problem and constrain the shape of a witness; none produces one.

By contrast, every class that *is* closed was closed by a tool that **produces** a witness:

* `SmallModuli.clear_one` — the explicit candidate `q = 1`, for every modulus `≤ 9`;
* `FirstLap.flank_clear_of_window` — an explicit opening when the differences fit a ratio-7 window;
* `DivisorOrder6.clear_of_order6` — an order-6 real witness, rounded, for moduli `≥ 10`.

## 5. What is actually missing, stated as work

The two frontiers are where no witness-producing tool reaches:

* **Branch B mixed scales.** Order-6 supplies a real witness at the moduli `≥ 10`; rounding it to
  an integer can land on a residue forbidden by a modulus `≤ 9`. For `b = 2` forcing the parity
  needs a margin `> 1/4`, and no order-6 bound supplies it. What is needed is **control of where
  the rounding lands relative to the small moduli** — a joint statement, not a count.
* **Rational readings (no unit speed).** Structurally identical, with the blocker count `n−2`
  instead of `n−3` because `unit_never_blocks` (proved, axiom-clean) cannot be applied.

So the missing input is the same in both, and it is the one named when the counting route was
closed: **control of the correlation between distinct blockers**, in the specific form of where a
rounded witness sits modulo the small moduli. Either that, or a **new explicit candidate** that
covers mixed scales the way `q = 1` covers the small end.

Existence at order 8 remains open, and both remaining frontiers need the same input.
