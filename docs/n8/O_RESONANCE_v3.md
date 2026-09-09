# `o` by resonance — v3: `65/256` resolved against me, and where (H3u)'s content actually sits

2026-09-09. **Supersedes `O_RESONANCE_v2.md`.** Working: `reports/n8_o_rate.md` and
`reports/n8_tail_bound.md`; scripts `experiments/n8/{ob_*,hp_*,rt_*,tb_*}.py`.

## 1. `65/256` — resolved, against me  `[PROVED]`

v1 listed `65/256` as the limit of "the next height class" and v2 downgraded it to
`[UNRESOLVED]`. It is now settled. Line 45 of `hp_resonance_limit_v1.py` reads

```python
print("65/256 =", float(F(65,256)))
```

a **bare print of a hard-coded literal**. Lines 40, 43 and 44 print values that were
computed (`F(24,256)`, and `a`, `b` from `limit(...)` calls); line 45 has no computation
behind it at all. I read it off the output and supplied the label myself.

Independently: every rank-1 class limit lies in `[1/48, 1/6]` at **every** height
(Theorem R1 below), and `65/256 = 0.2539 > 1/6`, so no rank-1 class can have that limit.
**`65/256` was never a class limit.** Struck from the record.

This is the third instance of one failure mode — a number taken from output and given a
meaning it did not have (`o = 1/4` for the translates; "speeds ≤ 295"; now this).

## 2. Class counts corrected  `[agent-reported, NOT re-verified here]`

`n8_o_rate.md` Theorem 5 gave **107** rank-1 and **1795** rank-2 realisable classes at
height `≤ 3`; those figures are quoted in `O_RESONANCE_v2` §3. Its realisability filter
was an `α`-parameter box — the same parameter-box-for-population failure as §1's "speeds
≤ 295" — and the corrected counts are **108** and **1964**, with an explicit witness for
each. **Both maxima (`1/6`, `1/4`) survive**, so every conclusion drawn from them stands.
I have not recounted these myself; flagged accordingly.

## 3. What is proved  `[PROVED]`

- **Exact identity.** `o` is a finite character sum over resonances; `3/32` is the `w=0`
  term, not a limit under a hypothesis, and there is no first-order term.
- **Vanishing rule.** `A(n) = (1 − (−i)^n)/(2πin)`, so `A(n) = 0` exactly when `4 | n`.
  Hence a resonance with **any** support coordinate divisible by 4 contributes nothing.
  *(Verified here by inspection.)*
- **Parity admissibility.** `Σ n_ρ e_ρ = 0` with every `e_ρ` odd forces `Σ n_ρ` even
  (reduce mod 2). *(Verified here.)*
- **Per-ray closed form.** `Ray(p)` is a **rational** number,
  `|Ray(p)| ≤ CAP/Π(p)` with `Π(p) = ∏_{ρ ∈ supp} |p_ρ|` and `CAP = 5/32`.
- **Theorem R1**, unconditional in the height: `|Ray(n₀)| ≤ 7/96`, so every rank-1 class
  limit lies in `[1/48, 1/6]`, with `1/6` attained exactly at the two `±1` relations.
  *Cross-check performed here:* `3/32 + 7/96 = 9/96 + 7/96 = 1/6` — matching the `±1`
  class limit computed by the wholly separate subtorus route. Two routes, same constant.
- **Theorem A:** `ht(n₀) ≥ 4 ⟹ |Ray(n₀)| ≤ 1/32`. By-height maxima:
  `ht 1: 7/96, 2: 1/32, 3: 5/96, 4: 0, 5: 1/32, 6: 1/96, 7: 3/224, 8: 0, 9: 7/864`
  (the zeros at 4 and 8 are the vanishing rule).

## 4. Where the `1/12` comes from, and why (H3u) is sharp  `[PROVED — arithmetic]`

`Δ(M′) = o_∞(M′) − o_∞(M₃(M′))` is a **sum of `Ray(p)` over the primitive rays of `M′`
that are not in `M₃`** — every one of height `≥ 4`.

    1/4 − 1/6 = 1/12.

The budget in (H3u) is *exactly* the gap between the rank-2 maximum limit and the rank-1
maximum limit. So (H3u) says precisely: **the height-`≥4` part cannot add more than the
full distance from the best rank-1 class to the best rank-2 class.** As an abstract
inequality it is therefore **sharp** — equality would be attained by a rank-2 class of
limit `1/4` whose height-`≤3` part is a `±1` relation. What prevents it is
**realisability**: over 10 120 realisable rank-2 classes generated at height `≤ 4` the
largest gap is `47/1056 = 0.0445`, 53.4% of budget.

## 5. Where the content sits  `[PROVED]`

> If the height-`≥4` part contributes a **single** primitive ray, then
> `Δ = |Ray(n₀)| ≤ 1/32 < 1/12` by Theorem A, so (H3u) holds automatically.

Hence **the entire content of (H3u) is the multi-ray case**, and it is one lattice sum:

    |Δ|  ≤  CAP · Σ  1/Π(p) ,

over primitive rays `p` of a rank-`≤2` lattice with `ht(p) ≥ 4`, no support coordinate
divisible by 4, and `Σ p_ρ` even.

Two features decide whether that sum is small. `Π(p) ≥ ht(p)` alone is **too weak** — for
a rank-2 lattice the ray count at height `≤ H` grows like `H²`, so `Σ 1/ht` diverges. What
saves it is the **support**: a ray with full support has `Π ~ ht⁴`, giving a convergent
`Σ ht/ht⁴`. So the sum is controlled exactly to the extent that the lattice avoids
**low-support** rays — and a low-support ray is a resonance among *fewer than four* of the
speeds, e.g. `n_i e_i + n_j e_j = 0`, which forces `e_i/e_j` to be a ratio of small
integers. **That is the object to bound.**

## 6. Grades

§1: **PROVED** (inspection of the source line, plus R1's ceiling). §2:
**agent-reported, unverified here**. §3: **PROVED**, with the vanishing and parity rules
re-derived here and R1's constant cross-checked against an independent route. §4:
**PROVED** (arithmetic) for the identity `1/4 − 1/6 = 1/12` and the sharpness reading;
the `47/1056` figure is **EMPIRICAL**, exhaustive over the stated class range. §5:
**PROVED** for the single-ray case; the multi-ray lattice sum is **OPEN** and is now the
whole of (H3u).
