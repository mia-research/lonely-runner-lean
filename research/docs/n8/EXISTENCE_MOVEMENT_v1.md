# Does any of this move Existence?

Direct answer: **yes in formulation, no in proof** — and one part needs the owner's ruling before it
can be used at all.

---

## 1. What genuinely moves

### 1.1 The cascade drops out of the statement — `[PROVED]` + 10,677/10,677

`Existence ⟺ CascadeCapped` (both directions proved, `Spec/Target.lean`), and `CascadeCapped` is
"the cascade terminates for every `ds`", i.e. `R` is finite. Combined with

> `R_final = min{ R ≥ 1 : ∀i, s_i·R mod 8 ∈ [1,7] }`   (verified 10,677/10,677)

this gives

> **Existence at order 8 ⟺ for every profile `1 = s₁ < s₂ < … < s₇`, some `R ≥ 1` has all
> `s_i·R mod 8 ∈ [1,7]`.**

No cascade, no iteration, no `move` function. That is a real simplification of the *statement*, not
of the difficulty.

### 1.2 A bounded-range sufficient condition — new

The band theorem (`RBand.R_avoids_bad_bands`, axiom-clean) confines `R` to `[1,7] ∪ [9,15] ∪ [17,23]
∪ …`. Hence

> **`R < 16` for every profile ⟹ Existence at order 8**

and `R < 16` says exactly that `[1,7] ∪ [9,15]` contains a clear point. **This is a bounded question
in six real parameters** — a region of total length 12, six conditions — where before it was an
unbounded search over `t`. It is *stronger* than Existence (Existence needs only *some* band), but
it is what every measurement supports, and unlike Existence it is finite-dimensional and
bounded-range, hence in principle amenable to a decision procedure.

### 1.3 The margin is now quantified — and it is thin

Maximising coverage of `[1,7] ∪ [9,15]` by the six non-minimal combs (3,000 restarts):

```
   minimum uncovered length : 0.000211   of 12
   maximum covered fraction : 99.9982%
   best six readings        : 2.0031  2.9737  3.9749  5.0008  5.9332  7.0001
```

The optimiser converges on **the arithmetic progression `2,3,4,5,6,7`** — the AP is the extremal
covering configuration, and its residual clear set is what LRC(8) is about. A band-2 counterexample
needs uncovered `= 0` exactly.

So the statement is **true but tight**: not comfortably true with room to spare, but true by a
margin of 0.0018%.

## 2. What does not move

* **Nothing is proved.** `R < 12` rests on 12.2 million evaluations; `R < 16` on the same plus the
  band theorem. Both are empirical.
* **The union bound is useless here**, as it has been all session: six combs at density `1/4` over
  12 units give 18 units of available bad measure, a factor of **1.5**. Counting cannot decide this.
* **The covering question is the whole difficulty** and is untouched. §1.3 says the searches get to
  99.998% and stop; it does not say they must.
* **`K ≤ 28` remains unestablished** (`CEILING_CLAIM_v1`), and so does `R < 12`.

## 3. ⚠ Firewall — this needs the owner's ruling

**§1.2 and §1.3 are covering arguments**, which §6A bans in the cascade framework. Unlike
`BS_TRANSFER_v1` §3, this one is *derived from the framework's own objects* — the readings, the bad
bands, `R` — rather than imported from Barajas–Serra. But the ban does not distinguish native from
imported, and `BS_TRANSFER_v1` §4's firewall question is still unruled.

**So §1.2 and §1.3 should not be built on until ruled.** §1.1 is independent of it — it is an
equivalence between two statements, with no covering language — and stands either way.

## 4. The honest summary

| | |
|---|---|
| Existence restated without the cascade | ✅ and it is cleaner |
| a bounded sufficient condition (`R < 16`) | ✅ new, but firewall-gated |
| the difficulty localised to one covering question | ✅ |
| the margin quantified (99.998%, extremal at the AP) | ✅ firewall-gated |
| any bound proved | ❌ |
| Existence closer to proof | **no** — the hard part is exactly where it was |

The shape of the gain is: the problem is now **stated in a bounded, finite-dimensional, cascade-free
form**, and we know precisely which configuration is extremal. That is a better target than "does the
cascade terminate", and it is not progress toward a proof.

```bash
python3 experiments/n8/R_direct_v1.py        # the cascade-free form, 10,677/10,677
python3 experiments/n8/coverage_margin_v2.py # 99.9982%, extremal at the AP
```
