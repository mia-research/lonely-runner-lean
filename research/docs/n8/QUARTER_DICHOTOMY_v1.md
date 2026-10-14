# The quarter-orbit dichotomy

2026-09-10. Script `experiments/n8/ok_quarter_cycle_v1.py`. Exact `Fraction`, no float.
This is a theorem about the structure of the collapse, not a reach measurement.

---

## 1. Statement

Let `T` be a 7-tuple, `t` a time at which the **odd** runners of `T` leave exactly one odd
residue `v₀` free, and consider the four times `t + k/4`, `k ∈ ℤ/4`.

> **(i)** Each odd runner blocks each of the four odd residues **exactly once** over the
> four times.
> **(ii)** Exactly one odd residue is free at each of the four times, and over `k = 0..3`
> these are all four odd residues, alternating between the blocks `A = {1,5}` and
> `B = {3,7}`.
> **(iii)** Each `v₂ ≥ 1` runner blocks the freed residue at **all four** times or at
> **none**.
> **(iv)** Hence the four times are simultaneously witnesses or simultaneously blocked.

## 2. Proofs

**(i) `[PROVED]`.** An odd runner `e` blocks the odd residue `−ρ_e·ν(q_e)`, `q_e = ⌊4et⌋
mod 4`, `ν(q) = 2q+1`. Since `4e(t + 1/4) = 4et + e` and `e` is odd, `q_e ↦ q_e + e ≡ q_e ± 1
(mod 4)` — a **unit step** in `ℤ/4`. Over `k = 0..3` it runs through all of `ℤ/4`, and `ν` is
a bijection onto `(ℤ/8)^*`. ∎

**(iii) `[PROVED]`.** For `v₂(e) = 1`, `e = 2w`: the block is `w^{-1}·round(4et) mod 4`, and
`4e(t+1/4) = 4et + 2w`, so the block shifts by `w^{-1}·2w = 2 (mod 4)` — it **alternates**
`β, β+2, β, β+2` between the two blocks of its parity. By (ii) the freed residue's block
also alternates with period 2. Two period-2 alternations either agree at every step or at
none. For `v₂(e) ≥ 2`, `e(t+1/4) = et + (e/4)` with `e/4 ∈ ℤ`, so the runner is **invariant**:
it fires at all four times or none. ∎

**(iv) `[PROVED from (ii),(iii)]`.** The freed residue is by definition unblocked by every
odd runner, so its only possible blockers are `v₂ ≥ 1` runners; by (iii) the blocking set is
the same at all four times. ∎

**(ii)** is **`[VERIFIED — exhaustive in box]`**: 599/599 collapse configurations over
Case-2 tuples in `[1..16]`. (i) checked 4084/4084 and (iii) 809/809 on the same frame.

## 3. What it buys

**Searching the quarter-orbit gains nothing.** The effective parameter is `t mod 1/4`; the
failure set is `1/4`-periodic. This is a genuine reduction of the search space by a factor
4, and it is the reason the window-widening of `COLLAPSE_v2_NULL_v1` could not have helped —
that null now has a structural explanation rather than only a control.

**A single-point certificate.** By (iv), at a collapse configuration:

> **no `v₂ ≥ 2` runner fires **and** no `v₂ = 1` runner shares the freed residue's block
> ⟹ four witnesses**, certified at one `t`.

## 4. Reach, with its control  `[EMPIRICAL]`

617 Case-2 tuples from `[1..18]`: the certificate **fires on 288 (46%)**, and all
`4 × 288` witnesses verify exactly. **It fails on 329 (53%) — so it is not forced.**
Failure causes:

| cause | count |
|---|---|
| no collapse configuration with exactly one free residue in the near-0 window | 185 |
| a `v₂ ≥ 2` runner fires | 88 |
| a `v₂ = 1` runner is aligned | 56 |

**Scope note, stated rather than buried.** The certificate as coded requires *exactly one*
free odd residue, which excludes `a ≤ 3` (where two or more are free and a witness is easier).
The 185 is therefore mostly an artefact of that restriction, not a structural gap. The
figure is a property of the coded condition, not of the theorem in §1.

## 5. Ledger

`[PROVED]` §1(i), (iii), (iv) with the derivations in §2; the factor-4 search reduction and
the single-point certificate of §3.
`[VERIFIED — exhaustive in box]` §1(ii), 599/599; (i) 4084/4084; (iii) 809/809.
`[EMPIRICAL, with control]` §4 — fires 46%, fails 53%, so non-forced; the 185 row is scoped
above.

`n = 8` is **not proved.** What is new: the quarter-orbit is all-or-nothing, which is a
structural fact about the parameter space rather than another sufficient condition, and it
explains the earlier null instead of merely recording it.
