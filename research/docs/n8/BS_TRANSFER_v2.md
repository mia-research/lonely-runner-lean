# What of Barajas–Serra actually extends to order 8

Supersedes `BS_TRANSFER_v1.md` (retained). v1 established the dictionary and named the break. This
version does the mechanical check the owner asked for — **the n=7 proof is on disk, so "does it
extend" is answered by reading it, not by argument** — and separates what generalises from what
does not, with Lean artefacts for both.

**Owner's ruling on the firewall (2026-09-18):** *"the firewall is there so there is no automatic
carry over or import. The fact there maybe intersection doesn't mean we can't look to see if this
extends anything."* So: inspection is licensed, import is not. Nothing below is imported; §5 records
what remains unruled.

---

## 1. Result

| | status |
|---|---|
| the pigeonhole core generalises off a prime modulus | **`[PROVED]`** `single_level_avoid_general` |
| its `≠ 0` hypothesis is *false* at `ZMod 8`, not merely unproved | **`[PROVED]`** `single_level_avoid_false_at_8` |
| the n=7 lemma is exactly the `N = 7` instance | **`[PROVED]`** `recovers_n7` |
| Corollary 3's counting threshold is the *same number* at order 8 | **`[PROVED]`** arithmetic, §3 |
| the `Λ_j,p` filtration that feeds them | **does not extend** — §4 |

Three theorems, zero `sorry`, no `native_decide`, all axiom-clean
(`[propext, Classical.choice, Quot.sound]`):

```bash
cd LonelyRunner && lake env lean ../experiments/n8/SingleLevelGeneral_v1.lean
```

---

## 2. The break, located in the proof and then repaired

`IntLRC7BS.single_level_avoid` (`PrimeFiltering.lean:35`) is the combinatorial core of Lemma 2. It
takes `r i ≠ 0` and closes with

```lean
rw [add_sub_cancel_left, mul_assoc, mul_inv_cancel₀ hrne, mul_one]
```

`mul_inv_cancel₀` is where `ZMod 7` being a **field** is load-bearing. At `ZMod 8`, `2 ≠ 0` but `2`
is not invertible, so there is no last step — and the statement is not merely unproved there, it is
**false**: with one index, slope `r = 2`, and `F = {0,2,4,6}` of size `4 ≤ 8−1`, every `k` lands in
`F`. That is `single_level_avoid_false_at_8`, proved by `decide`.

The repair is the honest hypothesis: **the slopes must be units, not merely nonzero.** Over a field
those coincide, which is why BS never had to distinguish them.

```lean
theorem single_level_avoid_general {ι} {N : ℕ} [NeZero N] (s : Finset ι)
    (c r : ι → ZMod N) (F : ι → Finset (ZMod N))
    (hr : ∀ i ∈ s, IsUnit (r i))                    -- was: r i ≠ 0
    (hsum : ∑ i ∈ s, (F i).card ≤ N - 1) :
    ∃ k : ZMod N, ∀ i ∈ s, c i + k * r i ∉ F i
```

`recovers_n7` derives the existing n=7 lemma from it in one line via `IsUnit_iff_ne_zero`. So this
is a strict generalisation of a verified component of the n=7 proof, not a parallel construction.

**This is the same fact as the cage, a third time.** `slot_gcd` says a unit multiplier preserves
`gcd(d,n)`; the cage says non-units are stuck; and here the pigeonhole needs unit slopes. One
group-theoretic fact, surfacing in the geometry, the valuation, and the counting.

---

## 3. Corollary 3's threshold is the same number at order 8

`corollary3` (`PrimeFiltering.lean:270`) is the workhorse: *if every valuation level below the top
has at most **3** elements, a multiplier sends every residue into the central band.* That `3` is
not special to 7 — it is `|F_d| = 2` (the two bad arcs `{0, p−1}`) against `∑ ≤ p − 1`:

```
  n = 7 :  2k ≤ 6  →  k ≤ 3
  n = 8 :  2k ≤ 7  →  k ≤ 3        (top level: 2k ≤ 6 → k ≤ 3, where n=7 needs k ≤ 2)
```

**The same threshold, and marginally more room at the top level.** Independently, `BS_TRANSFER_v1`
§3 measured the union bound at order 8 over 1200 subjects and found it closes exactly when **≤ 3
disparities survive the cage** — arrived at empirically, from ratios quantised at `k/4`, before this
arithmetic was checked. Two routes, same number. `[PROVED]` for the arithmetic; the measurement
remains `[EMPIRICAL]` on its sampler.

---

## 4. What does not extend, and it is the part that feeds them

BS's filtration is `Λ_j,p = {1 + p^(m−j)k : 0 ≤ k ≤ p−1}`, and eq. (3) says that within `Λ_j` the
map `k ↦ q(λ·x)` is **affine with slope `r_p(x)`**. That affineness is what lets the pigeonhole
apply at all — `prime_filtering` is a descending induction over levels, feeding each one to
`single_level_avoid`.

Two things block it at order 8, and they are different from each other:

1. **`Λ_j,p` needs `p` prime** to have `p` elements all behaving as multipliers, per v1 §2.
2. **At `p = 2` the digit is degenerate.** `r_p(x)` is the least nonzero coefficient of the `p`-ary
   expansion; at `p = 2` it is always `1`. So a 2-adic filtration gives `∑|F| ≤ p − 1 = 1` per
   level — at most one forbidden arc across an entire level. Near-vacuous.

So the general pigeonhole of §2 is real but currently **unfed**: nothing at order 8 plays the role
of `Λ_j`. `BS_TRANSFER_v1` §3's empirical success used the *whole* unit group mod `8M`, with no
filtration and no affine structure — which is why it could only be measured, not proved.

**This is the concrete open sub-problem, and it is well-posed:** exhibit an affine family of
multipliers at order 8 — a set `Λ` and a map `q` such that `k ↦ q(λ_k · d)` is affine with unit
slope. Given one, §2 and §3 supply the counting immediately. That is a better position than v1's
"their argument does not transfer", and it is not a claim that the sub-problem is easy or that
solving it would settle Existence.

---

## 5. Firewall: what the ruling covers and what it does not

The owner's ruling licenses inspection and forbids automatic import. Applying it:

- **§2, §3, §4 are inspection and generalisation of a local artefact.** No import. The Lean file
  imports `PrimeFiltering` to state `recovers_n7` — i.e. to prove the *new* lemma subsumes the old
  one — and nothing in the cascade framework depends on it.
- **`BS_TRANSFER_v1` §3 remains unruled.** Its form is "the bad sets do not cover the multiplier
  group", which collides with §6A's ban on covering language, and that question is untouched by
  this note. Nothing should be built on v1 §3 until it is settled.
- **Datum for that ruling, not a ruling:** the verified n=7 tree already contains this move. The
  comment at `PrimeFiltering.lean:46` reads *"the union of bad sets does not cover all of `ZMod 7`"*,
  and `single_level_avoid` is a `card_le_card` contradiction. So finite-group covering is already
  inside accepted work. Whether that licenses it in the cascade framework is the owner's call, not
  mine.

---

## 6. What this does not establish

No proof of anything at order 8. §2 generalises a lemma; §3 matches a constant; §4 says the input
those need does not exist yet. The 23.5% counting shortfall measured in v1 §3 is untouched. And the
prime/composite table in v1 §2 still does not say primality governs tractability — `n = 4` and
`n = 6` are composite and solved.

## 7. Artefacts

```bash
cd LonelyRunner && lake env lean ../experiments/n8/SingleLevelGeneral_v1.lean
sed -n '35,70p'   LonelyRunner/LRC/SmallN/IntLRC_7_BS/PrimeFiltering.lean   # the core, and its field step
sed -n '262,290p' LonelyRunner/LRC/SmallN/IntLRC_7_BS/PrimeFiltering.lean   # corollary3 and its "3"
```
