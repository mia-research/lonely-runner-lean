# Trying again at Existence: what was attempted, what closed, and where it actually stands

Direct answer up front: **I did not prove Existence, and I do not have a route to it.** What this
round produced is one new theorem that *forecloses a class of attacks*, and a precise statement of
the single remaining gap.

---

## 1. The attempt

The region `[1,7] ∪ [9,15]` contains 14 integer points. Each must be blocked by some reading, or it
is clear and `R < 16`. Blocking at integer `R` needs `|R·s − 8m| < 1`, a computable set per point. So:
can six readings block all 14? If not, band 2 is impossible **by a finite check**.

**A single reading `s ≈ 7.93334` blocks all 14.**

## 2. Why — and it is a theorem, not bad luck

Take `s = 8 − η`. Then `R·s = 8R − ηR`, and `8R` is a multiple of `8`, so `s` sits within `1` of a
multiple of `8` at `R` exactly when `ηR < 1`. Choosing `η < 1/B` blocks **every** point of `(0, B]`
at once.

> **`NoFinitePoints.near_eight_blocks`** and **`one_reading_blocks_all`** — `[PROVED]`, axiom-clean.

**Consequence.** Band-2 unreachability cannot be reduced to *"some point of a fixed finite set is
clear"*. Any such condition is satisfiable by one reading, hence vacuous.

That explains both shortcut failures with one mechanism:

```
   candidates R_k = (8k+1)/S   killed by a single v ≈ 0.981     (ANALYTIC_LAST_STEP_v1 §2)
   the 14 integer points       killed by a single s ≈ 7.93334   (this note)
```

**The covering must be tested on intervals**, which is exactly what the chain/LP formulation does.
This is a negative result about *method*, and it forecloses a class rather than one attempt.

## 3. Where Existence actually stands

The chain, with every link's status:

```
  Existence  ⟺  DoorCapped                      [PROVED]  Spec/Doors.lean, an ↔
             ⟸  RCapped B                       [PROVED]  RCapObligation_v1.lean
             ⟸  R < 16 for every profile        [PROVED]  from the band theorem, v11 Thm 11.2
             ⟸  uncovered > 0 whenever S > 7    ← THE GAP
```

and the gap's structure, from this session:

```
  only units bind                        [PROVED]  slot_gcd
  only units guard                       [PROVED]  Guard.klein_self_inverse + guard_blocks_below
  the AP supplies one guard per unit     [PROVED]  Guard.ap_clear_at_odd
  the AP covers up to 8 points           [PROVED — text]  v11 Thm 11.3
  S ≡ 7 guards both right endpoints      [PROVED — text]  the guard table
  S > 7 opens exactly 22ε/(7+ε)          [PROVED]  Guard.unguarded_width, verified to 10 d.p.
  the AP is the UNIQUE coverer           ← searched only: 600 restarts, 5 range caps,
                                            194,768 random profiles, never zero
```

**Every link is proved except the uniqueness of the AP as a coverer.** That one statement, if proved,
gives Existence at order 8 — which is why it is not going to fall to a search, and why I am not
claiming a route to it.

## 4. What would have to be shown

That no profile other than the AP covers `[1,7] ∪ [9,15]`. Three things are known about what such a
proof cannot be:

* **not counting** — six combs at density `1/4` over 12 units give `1.5×`, at every level tried;
* **not a finite point condition** — §2, proved;
* **not a depth ceiling** — band 2 needs depth `≥ 20` and depth 28 exists (`ANALYTIC_LAST_STEP_v1` §4).

What is left is an interval/interlocking argument on six arithmetic-progression families, with the
AP as the known unique solution and a measured linear rate away from it. That is a well-posed
question about one explicit configuration, and it is the whole of what is owed.

## 5. Session tally

**36 theorems across ten files, all axiom-clean, zero `sorry`**, none of which assumes or asserts a
bound on `R` or on the cascade's depth.

```bash
cd LonelyRunner && lake env lean ../experiments/n8/NoFinitePoints_v1.lean
python3 experiments/n8/integer_points_v1.py   # one reading blocks all 14
```
