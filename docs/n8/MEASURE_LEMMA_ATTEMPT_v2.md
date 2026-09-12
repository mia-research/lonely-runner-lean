# Measure lemma — the P4 route is closed

2026-09-12. Supersedes `MEASURE_LEMMA_ATTEMPT_v1.md`. Closes `PROOF_CANDIDATE_v3.md` §4.

## 1. Result

The lemma cannot close n = 8 via P4, and the reason is not a missing bound — it is that P4's
bound is too weak in the region where count-2 sets live, and gets weaker as the box widens.

P4 (`count ≥ (4 d_max/3)·|G_D|`) excludes count 2 only where its bound exceeds 2. Minimum of
that bound over **non-tight** primitive 7-sets (the three `|G_D| = 0` instances excluded,
since there the bound is identically 0):

| box | non-tight sets | min P4 bound | argmin | actual count there |
|---|---|---|---|---|
| `[1..12]` | 790 | 0.08333 | `(1,3,4,5,6,7,11)` | 6 |
| `[1..14]` | 3,428 | 0.08333 | same | 6 |
| `[1..16]` | 11,429 | 0.08333 | same | 6 |
| `[1..18]` | 31,785 | **0.06667** | `(1,2,3,4,5,7,18)` | 6 |
| `[1..20]` | 77,397 | 0.06667 | same | 6 |
| `[1..22]` | 170,210 | 0.06667 | same | 6 |

The minimum is **0.067, not 2**, and it **decreases** with box size. There is no span
threshold beyond which P4 bites. No lower bound on `|G_D|` repairs this, because the failure
is in the product `d_max·|G_D|`, which is what P4 actually uses.

P4's behaviour is bimodal: near-exact at large `d_max` (bound 117.37 against count 118 at
`d_max = 4096`), and off by two orders of magnitude at small `d_max` (0.067 against 6).
Count-2 sets all have small `d_max`. P4 is loose precisely where it would need to be tight.

## 2. Second retraction — the grid-distance table

`PROOF_CANDIDATE_v3` §3 offered this as the join between regions:

| span | `[0..20]` | `[0..40]` | `[0..80]` | `[0..200]` | `[0..1000]` | `[0..10⁴]` |
|---|---|---|---|---|---|---|
| floor at `k=1` | 2 | 4 | 8 | 16 | 150 | 1628 |

These are minima over **random samples** from each box, not minima over the box. Random draws
from `[0..10⁴]` have large `d_max` and therefore large counts; but `[0..10⁴]` still contains
`(1,4,5,6,7,11,32)`, which has `d_max = 32`, `|G_D| = 0.010045` and **count 2**. The true box
minimum is 2 at every `N ≥ 32`.

The table measures a property of the sampling, not of the box. It was cited as evidence that
floors rise with span; it is not.

## 3. What stands

- **P1** palindrome; **P2** the reference and the φ(8) law; **P3** components `≤ 3/(4 d_max)`;
  **P4** itself. All proved, all stress-tested (`P3_P4_AUDIT_v1`), none affected.
- **The enumeration.** Exact minimum count 2 over 12,569,075 primitive difference sets to
  span 38. Never 0, never 1.
- **The count-2 constraint.** For any count-2 set, P4 forces `d_max ≤ 3/(2|G_D|)`. That is a
  genuine restriction on where such sets sit, and the observed ones respect it
  (`d_max ∈ {8,16,32}` among the span-38 minimisers). It restricts; it does not bound.

## 4. What is closed and what is open

**Closed:** using P4 with a measure lower bound to dispatch large span. §1 shows the bound's
minimum is 0.067 and falling, so this cannot work at any threshold.

**Open, unchanged:** whether any runner can reach count 0. Nothing in this note or in v3
bears on it. The architecture of `PROOF_CANDIDATE_v3` loses its §4 step and therefore does
not close; §§1–3 of that note (coordinates, the reference branch, the proved chain) are
unaffected.

## 5. Status

`[PROVED]` P1–P4, unchanged.
`[VERIFIED — exhaustive]` §1's six boxes; the span-38 enumeration.
`[RETRACTED]` `PROOF_CANDIDATE_v3` §4 as a viable step; §3's floor-versus-span table as
evidence; and (from v1) §3's claim that low counts occur only at small span.
`[NOT PROVED]` n = 8.
