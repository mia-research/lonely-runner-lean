# Existence reduces to a uniqueness statement about one measure functional

A correction to my own framing, and the reduction it yields.

---

## 1. The correction: the AP is **not** a coverer

Band 2 requires the clear set in `[1,15]` to be **empty**, not merely null. The AP's clear set is the
eight odd integers (v11 Theorem 11.3, `Guard.ap_clear_at_odd`) — **non-empty**. So the AP has zero
uncovered *length* and still fails to cover.

`AP_ISOLATION_v1` §3 called the AP "the unique profile satisfying both". That was measuring
uncovered length. **The AP is the unique profile of zero uncovered length; it is not a cover.**
Corrected here.

## 2. The dichotomy

For any profile, exactly one of:

```
   uncovered length > 0   →  the clear set has positive measure  →  NON-EMPTY  →  R ≤ 15
   uncovered length = 0   →  ??? which profiles ???
```

and at the AP the second branch still gives a non-empty clear set — the eight odd integers, so
`R = 1`.

> **If uncovered length `= 0` implies the profile is the AP, then every profile has a non-empty clear
> set in `[1,15]`, hence `R < 16`, hence Existence at order 8.**

That is a reduction of Existence to a **uniqueness statement about a measure functional** — not to a
covering statement, and not to anything about the cascade.

## 3. Evidence for the uniqueness

```
   5,645,396 evaluations, 4,000 restarts, four seeding modes
   profiles with joint uncovered < 1e-9 :  0
   best found                           :  2.814e-04  at [1.9985, 3.0179, 4.0354, 5.0298, 6.0099, 7.0000]
```

The search hugs the AP and cannot reach zero — consistent with the AP being an **isolated exact
zero** of the functional, attained only at the exact rationals `2,3,4,5,6,7`. Seeding modes covered
perturbations of the AP, uniform draws in `(1,8)`, uniform draws in `(1,16)`, and split small/large
draws.

## 4. Why the functional is the right object

The uncovered length is a **measure**, so it is far better behaved than the covering predicate:

* it is `0` at one point and positive elsewhere, rather than a discontinuous yes/no;
* near the AP it has an **exact closed form**: raising the guard `S` to `7+ε` gives
  `22ε/(7+ε)`, verified to ten decimal places (`Guard.unguarded_width`);
* the total available measure is fixed: each comb contributes density `1/4`, so
  `Σ|B_i ∩ region| ≈ 18` against `12` needed, and zero uncovered forces the overlaps to total
  **exactly 6**. That is a rigid condition on six parameters, not a soft one.

The last point is the one to push: *zero uncovered ⟺ the overlaps total exactly 6*, and the AP is
the configuration achieving it. Proving that no other configuration does is the whole of what
remains.

## 5. Status of each link

```
   Existence  ⟺  DoorCapped                          [PROVED]   Spec/Doors.lean, an ↔
              ⟸  RCapped B                           [PROVED]   RCapObligation_v1.lean
              ⟸  R < 16 for every profile            [PROVED]   band theorem, v11 Thm 11.2
              ⟸  clear set non-empty in [1,15]       [PROVED]   immediate
              ⟸  uncovered > 0  OR  profile = AP     [PROVED]   §2, using ap_clear_at_odd
              ⟸  uncovered = 0  ⟹  profile = AP      ← THE ONLY GAP
```

Everything above the last line is proved. The remaining statement is about a single explicit
configuration and a single real-valued functional, with an exact local expansion around the
candidate and 5.6 million evaluations finding no other zero.

## 6. What to attack next

Two concrete lines, both about §4's rigidity:

1. **The overlap identity.** Compute `Σ|B_i ∩ region|` exactly as a function of the profile (it is
   `1.5` per comb plus boundary truncation terms), and the pairwise overlaps. Zero uncovered forces
   total overlap `= Σ − 12`. Characterise which profiles achieve it.
2. **Second-order behaviour at the AP.** The first-order expansion in the guard direction is
   `22ε/(7+ε)`. Compute it in the other five directions; if every direction has a strictly positive
   first-order rate, the AP is a strict local minimum, and only global structure remains.

```bash
python3 experiments/n8/zero_length_v1.py    # 5.6M evaluations, no second zero
cd LonelyRunner && lake env lean ../experiments/n8/Guard_v1.lean
```
