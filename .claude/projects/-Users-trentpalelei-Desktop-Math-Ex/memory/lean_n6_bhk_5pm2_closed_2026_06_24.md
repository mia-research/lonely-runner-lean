---
name: lean-n6-bhk-5pm2-closed-2026-06-24
description: n6 BHK Prop11 — (5,±2) transversals both CLOSED via new half-slope 5/2 readoffs
metadata:
  type: project
---

**n6 BHK Prop11 — (5,±2) transversals CLOSED 2026-06-24** (commit de7882f, all
axiom-clean propext/Classical.choice/Quot.sound, build 2703). `exc_open`
transversal frontier **13 → 11**: removed (5,2) and (5,-2). Remaining 11:
(2,-3)(2,1)(2,3)(3,-4)(3,4)(4,-3)(4,2)(4,3)(5,-4)(5,-3)(5,3) + core_q_lt_18 +
core2_q_lt_18.

**Convention reminder:** `exc_relation p q r .. i j k` ⟹ `q ∣ (j·r − i·p)`. For
(i,j) the half-slope c-split comes from `j·r − i·p = cq`.

**(5,2)** `2r − 5p = cq`, bounds (q<r, 3p<q, 2r<3q) ⟹ **c∈{1,2}**. c=2 was done
(`exc_5_2_c2`, p even). **c=1** new `exc_5_2_c1` (`2r=q+5p` ⟹ p,q odd):
- new atom `readoff_q5p` — `2r=q+5p`, on `(2m+1)/(2q)` with `m−⌊pt⌋` **odd**
  (`=2s+1`), `X={rt}=5/2·A − 1/4` for `A={pt}∈[1/6,3/10]` (lands [1/6,1/2]).
- parity selector: p,q odd ⟹ `m−d ≡ (p·m)%q (mod 2)`; pick `kk` **odd** via
  `fract_odd_mul_mod`, `kk := 2*((q−3p+5)/12)+1`, window `2kk+p∈[q/3,3q/5]`.
- p-coord `=A∈[1/6,1/3]` directly (slope-1 base).

**(5,-2)** `2r + 5p = cq` ⟹ **c∈{3,4}** (h1: q*2<q*c, h2: q*c<q*5). Two branches:
- **c=3** `2r=3q−5p` (p,q odd) new `exc_5_neg2_c3` + atom `readoff_3q5p`:
  `X=3/4 − 5/2·A` for `A∈[1/6,7/30]`, parity `m−d` **even** (kk even). **Reuses
  (3,-2)'s `kk:=2*((2q−6p+23)/24)`** — lands `2kk+p∈[q/3,7q/15]` for q≥30
  (upper needs q≥29: q/3+23/6 ≤ 7q/15). p-coord `=A`.
- **c=4** `2r+5p=4q` ⟹ **p even**, `p=2pp`, `r=2q−5pp` ⟹ new `exc_5_neg2_c4`
  **reuses `readoff_even`(γ=5)+`readoff_zero`(γ=2)** exactly like `exc_5_2_c2`:
  `A'={pp·t}∈[1/10,1/6]` (kk:=(q−5pp+9)/10, no parity, `fract_odd_mul`),
  `X=1−5A'∈[1/6,1/2]`, p-coord `=2A'∈[1/5,1/3]`.

**GOTCHA:** `readoff_q5p`/`readoff_3q5p` key step — `field_simp` **alone** closes
the `(r:ℝ)/q*(m+1/2) = …` reduction; adding `ring` errors "No goals to be
solved" (unlike `readoff_3q4p` which needs `field_simp; ring`).

**Half-slope 5/2 engine now complete for i=5,|j|=2.** Pattern for the |j|≥2
transversal readoffs: relation pins `2r=αq±5p` → reparam → readoff X=linear(A) on
a parity-selected line (odd/even kk) when base p is odd, OR halve to base pp +
integer-slope readoff_even/odd/zero when p forced even. Same template should hit
(5,±3)(5,-4)(4,±3)(2,±3) — vary slope/coeffs. [[lean-n6-bhk-1-2-closed-2026-06-21]]
