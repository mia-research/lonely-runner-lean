# Resonance in Lean, and what it does to the proof attempts

2026-09-21, version 1. Formalises `RESONANCE_AND_PARITY_v1.md`; then the pause the owner asked
for — what the mechanism means for where proof effort should go.

Artefacts: `LonelyRunner/LRC/Spec/ResonanceN.lean` (7 declarations, axiom-clean, no `sorry`) ·
`experiments/n8/resonance_axioms_v1.{lean,out}`

---

## 1. What is proved  `[PROVED — axiom-clean]`

```lean
def Resonant (n m : ℕ) : Prop := 1 < Nat.gcd m n
```

| declaration | statement |
|---|---|
| `not_resonant_iff` | non-resonance is coprimality |
| `not_dvd_of_not_resonant` | non-resonance rules out `n ∣ m` |
| **`resonant_iff_dvd_of_prime`** | **at prime `n`, resonance and `n ∣ m` are the same condition** |
| `lonelyAt_inv_of_no_resonance` | no resonant disparity ⟹ lonely at `1/n`, **at every order** |
| `lonelyForSubject_of_no_resonance` | the subject's obligation, discharged |
| `doors_of_no_resonance` | all four doors, via `doors_agree` |

Machine-checked at the instances that matter: `Resonant 5 m ↔ 5 ∣ m` and `Resonant 7 m ↔ 7 ∣ m`,
while `Resonant 8 2 ∧ ¬(8 ∣ 2)`, `Resonant 8 4 ∧ ¬(8 ∣ 4)`, `Resonant 8 6 ∧ ¬(8 ∣ 6)` and
`Resonant 9 3 ∧ ¬(9 ∣ 3)` all hold by `decide`. The divergence at composite orders is not a
measurement; it is a theorem.

**What is not proved.** `CoprimeLargestFlank` — that under non-resonance the witness can be
taken at the *largest* disparity rather than at `1/n`. It is a `Prop`, used only as a hypothesis.
`[EMPIRICAL]`.

---

## 2. The one thing to take from §1

Non-resonance already suffices for the obligation, at every order. So

> **the whole difficulty, at every `n`, is the resonant subjects** — and how large that class is
> depends entirely on the divisor structure of `n`.

| order | resonant condition | share of card-7 sets on `[1,15]` |
|---|---|---|
| 7, 11, 13 (prime) | `n ∣ d` for some `d` | ~47% |
| 9 (`3²`) | `3 ∣ d` for some `d` | 98% |
| 8 (`2³`), 10, 12, 14 | `2 ∣ d` for some `d` | ~100% |

At an even order essentially every subject is resonant, so the proved criterion protects nothing.
At a prime order it protects about half outright.

---

## 3. What this means for proof attempts

**(a) At `n = 8`, widening the named-instant criterion is work on a vanishing set.**
`lonelyAt_inv_of_not_dvd` settles subjects with no disparity divisible by 8 — but 6,426 of 6,434
card-7 sets contain an even disparity, and 89 of the failures pass the divisibility test and fail
anyway. Effort spent generalising *that* criterion at order 8 buys almost nothing; the same
effort at order 7 or 11 would be decisive.

**(b) The order-8 frontier has a three-class structure it was not being given.**
Not "seven differences at `n = 8`" but `gcd(d, 8) ∈ {1, 2, 4, 8}`: class 1 is **proved**
(§1), and classes 2, 4, 8 are the frontier, with the cage (Thm 4.13) already saying how far each
is confined — `1/4`, `1/2`, `0`. A class-by-class attack is available where an undifferentiated
one was not.

**(c) Results proved at `n = 5` may not transfer, and for a stateable reason.**
Five is prime. Its resonance class is thin, and several things that hold there hold *because* of
that: `sup R < n − 1` (`R_ROUTE_IS_ORDER_FIVE_ONLY_v1.md`) and `DoorLargestFlank`
(`SMALL_ORDER_DOORS_v3.md`) both survive at 5 and at no order above. Before porting any order-5
argument upward, check whether it used primality.

**(d) A caution about my own earlier measurements.** The clearance law I reported was
`f(3)=5, f(4)=8, f(5)=11, f(6)=13` — three of those four thresholds are **prime**, and the one
that is not is `8 = 2³`. That may be the resonance mechanism showing through rather than a
clearance law in `k`. It is an observation, not a claim; it should be re-measured with the
divisor structure of `n` recorded, before anything is built on `f`.

**(e) What is unaffected.** The general-`n` port (`DoorsN.lean`, 105/105 axiom-clean) is
structural — `doors_agree`, the target forms, the arrangement layer — and carries no arithmetic
hypothesis. Nothing in §1–§3 touches it.

---

## 4. Grades

| claim | grade |
|---|---|
| the six theorems of §1 | `[PROVED — resonance_axioms_v1.out, axiom-clean, no `sorry`]` |
| resonance ⟺ divisibility at prime `n` | `[PROVED]` |
| the two conditions differ at 8 and 9 | `[PROVED — by `decide` on explicit witnesses]` |
| non-resonance settles the obligation at every order | `[PROVED]` |
| resonant share ~100% at even orders | `[VERIFIED — exhaustive counts]` |
| `CoprimeLargestFlank` | **not proved** |
| `f(k)` reflects primality rather than `k` | **conjecture** — flagged for re-measurement, nothing built on it |
