# Induction on the scale, attempted on the middle of the trichotomy — refuted shape

*2026-09-22. Artefacts `experiments/nN/descent_v1..v6.py`. Order 8, `c = 7`, middle `1 ≤ M ≤ 5`,
`A = {d : 8 ∣ d}`, `B = {d : 8 ∤ d}`. **Not coverage**: every statement below is a structural
claim with a decidable hypothesis, tested for exceptions rather than scored for reach.*

## What was tried

§12 says the middle is a self-similar copy one scale down, constrained by the non-resonant part,
and that the recursion stalls because the non-resonant part does not descend. The attempt was to
find a **decidable rule for which flank to take**, so that the descent has somewhere to go.

**Confirmed (CRT):** at a flank with `gcd(e, n) = 1`, `ρ = a mod e` determines `a mod ne`
bijectively, since `a ≡ 1 (mod n)`. 0 failures. So at such a flank the whole condition — resonant
and non-resonant alike — is a condition on `ρ` alone. This is the mechanism that would let a
descent work.

## The regularity, and its exceptions

**Observed:** a clear flank can nearly always be taken from `B`. Exhaustively over `[1,28]`,
161,414 middle sets, **3** exceptions; randomly over ranges to 80, 200,000 middle sets, **2** more.

**Candidate rule H1** — *if `A/n` does not satisfy the ratio condition, some flank in `B` is clear.*
Suggested by the first five exceptions, whose `A/8` were `{1,2,3}`, `{1,3,4}`, `{1,3,4,5}` — all
ratio-easy.

**H1 is `[REFUTED]`.** 24,000 in-regime sets across ranges 100–400: **5 violations**, e.g.

```
    (1, 4, 8, 18, 48, 64, 88)      A/8 = (1, 6, 8, 11),  max/min = 11 > 7
    (1, 8, 15, 24, 40, 120, 160)   A/8 = (1, 3, 5, 15, 20),  max/min = 20 > 7
    (1, 24, 36, 56, 120, 192, 216) A/8 = (3, 7, 15, 24, 27),  max/min = 9 > 7
```

In each, no flank in `B` is clear although `A/8` is far from ratio-easy.

## What survives, and what does not

**Does not survive:** any decidable characterisation of the `B`-exceptions. H1 was the only one
tried and it is refuted.

**Survives only trivially:** in all ten exceptions found, some flank in `A` is clear — which is
just "some flank is clear", i.e. the conjecture for that subject. It carries no information.

**Survives as an observation, ungraded as a route:** the `B`-flank regularity is strong (order
`10⁻⁴`–`10⁻⁵` exception rate on these samples) and its exceptions are not understood. Per the
project's standing note, understanding those exceptions — not sharpening the rule — is the next
move if this direction is resumed.

## Status

**The induction was attempted and the shape tried does not work.** No theorem was obtained. The
`[1,28]` exhaustive figure and the CRT fact are the only durable outputs.

*Method note: the first five exceptions all had ratio-easy `A/8`, which is exactly the kind of
pattern this project has repeatedly generalised from too early. H1 was written down as a candidate
and tested against 24,000 in-regime sets before being believed, and it failed.*
