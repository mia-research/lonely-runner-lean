# RESULT — the 33.33% cross-class collision is a **forced ideal coincidence** (open item closed)

*2026-07-24. Closes the open item of `RESULT_kummer_family_b_capacity_v1.md` §4.1 and deviation D4.
Scripts: `scratchpad/collision33.py`, `collision_d4_and_ideal.py`. Exact `ℤ[ζ_d]` arithmetic; no float.
No leakage / key-recovery / ECDLP claim.*

---

## 0. The anomaly

`RESULT_kummer_family_b_capacity_v1.md` control C2 fired cleanly at `d = 2, 3, 12` (0.00% cross-class
collision) but returned **exactly 33.33%** at `d = 4` and `d = 6`. D4 flagged it unexplained and killed a
premature "pigeonhole" story. It is now a **derived mechanism**, not a nuisance.

## 1. The characterization `[VERIFIED — exact]`

Among the **3 cubic classes** of `b`, look at whether `S_d(b)` and `S_d(b′)` are **associate** in `ℤ[ζ_d]`
(differ by a root of unity — this is exactly what the C2 "shift by `ζ^k`" test detects).

> **At every prime, exactly ONE of the 3 class-pairs is associate.** `d=6`: **36/36** primes
> (`13 ≤ p ≤ 400`). `d=4`: **12/12** primes (`p ≡ 1 mod 12`, `≤ 300`).

One associate pair out of 3 possible pairs = **1/3 = 33.33%**, exactly. No statistics — an integer count.

## 2. The mechanism, derived (`d = 6`) `[DERIVED + VERIFIED 36/36]`

Generalising the `b = 7` Jacobi reduction of `RESULT_mu6_cover_and_conductor_v2.md` to arbitrary `b`:
```
S_6(b) = χ₆(b) · α₀ · r(b),     α₀ = J(χ₃,χ₆)  (|α₀| = √p, a prime above p in ℤ[ω]),
         r(b) = χ₃(b) + χ̄₃(2)·χ̄₃(b),     |r(b)|² = |1 + χ₃(4b)|² ∈ {1, 4}.
```
`χ₆(b)` is a root of unity (a **unit**). As `b` runs over the 3 cubic classes, `χ₃(4b)` runs over
`{1, ω, ω²}` — so **exactly one class** has `χ₃(4b) = 1` (⇒ `|r| = 2`, norm `4p`), and the **other two**
have `χ₃(4b) ∈ {ω, ω²}` ⇒ `|r(b)| = |1 + ω| = 1` ⇒ **`r(b)` is itself a unit.**

Therefore for both norm-`p` classes the ideal is
```
( S_6(b) )  =  ( α₀ )      — the SAME prime ideal, independent of which class.
```
**They are forced to be associate.** The third class carries the factor `(2)`, norm `4p`, and stands
alone. `⇒` exactly one associate pair, always. ∎

`d = 4` shows the identical "1 of 3" structure `[VERIFIED 12/12]`; the analogous unit factor in `ℤ[i]`
is not separately derived here (the collision pair is consistently the `(1,2)` classes, not `(0,·)`,
matching a `χ₄(b)`-unit factor on two of three classes).

## 3. Why this is the right kind of answer

- **It dissolves the anomaly into structure, and sharpens the capacity result.** At `d = 6` the *ideal*
  `(S_6(b))` takes only **2** values (`(α₀)` or `(2α₀)`), so the order-6 piece carries only **1 bit**
  about the cubic class of `b`, not the full `log₂3`. The full `log₂3` is realised by the **`d = 3`
  piece alone** — the pure cubic character `S_3`, which separated all three classes (C2 = 0.00% at
  `d = 3`). So the family's capacity bound is **tight, and located**: it lives entirely in the μ₃ cover;
  every higher-`d` sum factors through `(α₀)` and adds nothing.
- **It vindicates C2 as a control while explaining its "failure".** C2 did not misfire at `d = 4, 6` —
  it correctly detected that those pieces genuinely fail to separate the classes, *because the separation
  is not there to detect*. The arms are still VOID as pre-committed (the test cannot measure tightness
  where the object is degenerate), but the void is now understood, not a defect.
- **No new secp content.** This is a statement about `ℤ[ω]`/`ℤ[i]` and the family, holding for every
  `b`. It does not distinguish `b = 7` and has no `d`-side consequence.

## 4. Consequence for the standing picture

The Kummer-family investigation is now **complete at the object level**:
`(★)` bounds `b`-capacity at `log₂3`; §2 here shows the bound is **tight and concentrated in the μ₃
piece**; the μ₄ piece (and `k=12`) carries the `p`-dependence (supersingularity), not `b`-dependence.
Nothing in the family carries secp-constant-specific structure beyond `χ₃(7)` — **one of three values,
and that value is `χ₃(7) ≠ 1`, itself forced by `n` being prime.**

**The one direction left un-bounded remains the conductor/volcano family** — it varies the endomorphism
*lattice*, not `b`, and `(★)` says nothing about it. That is the live probe.

---

*Grades: §1 `[VERIFIED — exact integer counts]`; §2 (`d=6`) `[DERIVED + VERIFIED 36/36]`, (`d=4`)
`[VERIFIED 12/12, mechanism analogous but not separately derived]`; §3 capacity-localisation
`[DERIVED]`. Scan scope `p ≤ 400` under frontier §XI.5's banner; the `d=6` mechanism, being a
derivation, is scale-free.*
