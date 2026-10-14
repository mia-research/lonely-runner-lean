# Whittling the n = 5 residue: the self-similar core, closed

2026-09-21, version 1. Continues `N5_RESIDUE_MECHANISM_v1.md` by the owner's method — reduce the
unproven portion in steps rather than seek one proof.

Artefacts: `experiments/nN/n5_triples_v1.{py,out}` · `n5_whittle_v1.{py,out}` ·
`n5_hard_triples_v2.{py,out}` · `n5_close_selfsimilar_v1.{py,out}`

**`intLRC_four` is NOT used.** An earlier draft reached for it; the owner ruled that a dead end
and it is dropped. Everything below uses an exact finite computation of `S` plus the framework's
own `exists_lonely_flankOpening_of_gap`.

---

## 1. Why `1/4` appeared next to a `1/5` threshold

Worth stating because it reads like an error. `1/5` is the threshold the problem *needs*. The
**reduced** problem has **three** runners, and the lonely-runner value for three speeds is
`1/4`. Since `1/4 > 1/5`, the guarantee **exceeds** the requirement, and the surplus is the
slack that converts a real witness into a rational one. With no surplus there is no window.

But the guarantee is not what is used below: `S` is computed **exactly, per triple**, on the
vertex set `{k/(2mᵢ)} ∪ {k/(mᵢ±mⱼ)}` — a finite decidable calculation.

---

## 2. The criterion

The window has width `2(S − 1/5)/m₃` and must exceed `1/e`, so the route needs
`e > m₃/(2(S − 1/5))`. A difference set gives `5·m₃ < e` for free. Those coincide exactly when

> **`S ≥ 3/10`** — and then the route closes with nothing extra.

---

## 3. The obstruction is five triples  `[VERIFIED — stable]`

`S(λ·m) = S(m)` (substituting `t ↦ t/λ`), so only **primitive** triples matter. Scanning all
primitive triples exactly:

| entries ≤ | 12 | 20 | 30 | 40 |
|---|---|---|---|---|
| with `S < 3/10` | **5** | **5** | **5** | **5** |

and the list never changes:

| triple | `S` |
|---|---|
| `(1,2,3)` | `1/4` |
| `(1,2,6)`, `(1,3,4)`, `(1,5,6)`, `(2,3,5)` | `2/7` |

---

## 4. The self-similar family is closed

Two reductions, both checked:

**R1 — scaling.** If `gcd(λ, e) = 1` then `r ↦ λr` is a bijection of `ℤ/e`, so the band problem
for `(λmᵢ)` at modulus `e` **is** the problem for `(mᵢ)`. Difference-set primitivity forces
`gcd(5λ, e) = 1`, so the reduction always applies. *Verified: 1,580 combinations, **0
mismatches**.*

**R2 — window plus finite check.** Each hard triple is closed above an explicit bound, and the
finite range below it is checked directly:

| triple | window closes | finite range left | failures there |
|---|---|---|---|
| `(1,2,3)` | `e > 30` | 16…30 | **none** |
| `(1,2,6)` | `e > 35` | 31…35 | **none** |
| `(1,3,4)` | `e > 23.3` | 21…23 | **none** |
| `(1,5,6)` | `e > 35` | 31…35 | **none** |
| `(2,3,5)` | `e > 29.2` | 26…29 | **none** |

Spot-checked 60 moduli above each bound: no failures.

So **every** set whose non-flank disparities are all multiples of 5 is accounted for.

---

## 5. What that is worth, stated plainly

**By count it is small.** The self-similar family is `0.97%` of the residue.

**By difficulty it is the core.** Those sets are **13.85× over-represented** among the
low-opening sets — 13.41% of them against 0.97% of the residue. The hardest cases are closed.

**What remains unproved in it.** One statement: *`S ≥ 3/10` for every primitive triple outside
the five*. That is a sharpening of the three-speed lonely-runner value from `1/4` to `3/10` with
an explicit exceptional list. It is `[EMPIRICAL]` — scanned exactly to entries `≤ 40`, never
varying — and it is a claim about **three integers**, not about difference sets. That is a much
smaller object than the residue it replaces.

---

## 6. The template, for the rest of the residue

The same three moves should be tried on the larger classes:

| class | share of residue | status |
|---|---|---|
| three inner 5-multiples (self-similar) | 0.97% | **§4** |
| two inner 5-multiples | 17.9% | untried |
| one inner 5-multiple | 81.1% | untried |

For the mixed classes the system has conditions at **both** moduli (`5e` for non-multiples, `e`
for multiples), so R1 applies only to the multiple part. The open question is whether a partial
scaling reduction plus the window still bounds the exceptional set.

---

## 7. Grades

| claim | grade |
|---|---|
| `S` computed exactly per triple, no import | `[VERIFIED — vertex set; matches known values]` |
| the criterion `S ≥ 3/10` | `[PROVED — arithmetic on the window width]` |
| exactly five primitive triples with `S < 3/10` | `[EMPIRICAL — exact scan to entries ≤ 40, stable]` |
| R1, the scaling reduction | `[VERIFIED — 1,580 combinations, 0 mismatches]` |
| the five finite ranges have no failures | `[VERIFIED — exhaustive]` |
| the self-similar family | **closed, modulo the §5 statement** |
| the other 99% of the residue | **untried** |
