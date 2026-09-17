# Scale acceptability: the free test, all-or-nothing, and where the barrier actually sits

2026-09-17, after the owner's correction: *"You are treating it like a search again. That is not how it
works. Individual speeds push what possible scales are mutually acceptable. But AP was always scale
invariant."*

`DEFORMATION_PICTURE_v1` §5 ended in *"does the family of progressions the cascade reaches always present
each runner as a bracketed element"* — enumerate-and-hope in new clothes. This works the two §0 objects
that say it is not a search, neither of which I had used.

Artefacts: `experiments/n8/free_test_v1.py` and the checks below.

---

## 1. The two instruments, verified against the definition

| §0 object | statement | check |
|---|---|---|
| **All-or-nothing** | if `D` divides every difference, every candidate at that gap gives the same verdict | **119/119** |
| **Theorem 4.10** | with integral readings, a spine instant clears reading `s` exactly when `8 ∤ s`, **the same for every `p`** | **105/105** |
| **The free test** | `e` cannot block at gap `D` ⟺ `m = 8D/gcd(e,8D)` is even and `≤ 8` | **4800/4800** |

**This is the scale invariance.** At a scale where every difference passes the free test, there is
nothing to search: one verdict, all candidates. An AP does not consume scales — it answers outright.

**And this is how individual speeds push the scales.** The free test is a condition on `gcd(e, 8D)`
alone: each difference names, by divisibility, the gaps at which it cannot block. Acceptability is a
property each difference *has* at each scale, not something found by looking.

## 2. Mutual acceptability is decided once  `[EMPIRICAL — 2550/2550]`

Searching every `D` up to `4·d_max`, not only divisors:

> **Some scale is acceptable to all seven differences ⟺ the gcd scale is.** 2550 of 2550.

So there is no family to sift. The scale-invariant answer either exists, and the gcd scale is one, or it
does not exist at all.

**Measured split:** 950 of 2550 arrangements (**37%**) have a fully-free scale. **63% have none.**

## 3. Therefore the barrier

For 63% of arrangements **no scale is acceptable to all seven differences at once.** Loneliness there is
not a matter of locating an acceptable scale — there is none to locate. It comes from a scale at which
the differences *disagree across candidates*, so that the subject is clear at one candidate though not
at all of them.

> **The barrier is the disagreement regime: when no scale is mutually acceptable, must some candidate
> still be clear of everything?**

That is where all-or-nothing has failed and the candidates stop agreeing — and it is exactly the stratum
the `U`/`K` calculus addresses: `U_e` is the set of candidates on which the fixed differences agree on
"clear", and the killer lattice asks whether the remaining difference can take all of them. The calculus
formalised today is pointed at the right stratum, which was not obvious before this.

## 4. Three things I got wrong in reaching this, recorded

- **The search framing.** `DEFORMATION_PICTURE_v1` §5. Corrected by the owner; the correction is §1
  above — acceptability is a property, not a find.
- **An algebraic unwinding of the free test that is false.** I claimed `e` free at `D` ⟺ `D | e` and
  `8 ∤ e/D`. **57 counterexamples**, all the `m = 6` branch, where `D ∤ e` and the runner is free anyway
  (`e = 4, D = 3`: `gcd = 4`, `m = 6`). So fully-free scales are **not** confined to divisors of the
  differences, though non-divisor ones are rare (2 of 2550).
- **The dichotomy's status.** §2 is `[EMPIRICAL]`. I derived it from the false unwinding; the derivation
  is refuted and the statement happens to survive the measurement. It is not proved.

## 5. What is not established

§2 is measured over integer difference sets to 120, scales to `4·d_max`. Nothing here proves Existence
or narrows it; it locates the open stratum and shows the formalised calculus is aimed at it. The `m = 6`
branch is unexplained — why a non-dividing scale can be fully free at all is a fact about `gcd(e, 8D)`
that I have not accounted for, and it is the one loose thread in §1.
