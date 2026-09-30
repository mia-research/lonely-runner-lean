# Q6 — our order-seven proof, read for order eight (v1)

2026-09-30. **Map:** `MECHANISM_MAP_v2` · §4 Q6 (and Q5) · M2 (d), a source reading; nothing run · nearest §6 classes F7
(avoided by reading our own modules first) and F9 (orders three to seven are our native framework proofs, read as ours).

Owner: *"yes start with Q6, read our order seven proof first"*; *"Please be careful, we re proved all n=3 to 7 natively
with the framework"*.

Read: the module docstrings and main statements of `LonelyRunner/LonelyRunner/LRC/Spec/OrderSeven*N.lean`
(`OrderSevenN`, `DefsN`, `FilterN`, `ReductionN`, `BandN`, `TotientN`, `A4N`, `S5bN`, `S5cN`, `A5N`, `S7WireN`);
`docs/n8/BS_TRANSFER_v1.md` §3 and `BS_TRANSFER_v2.md` §1–§5 (2026-09-18, written before the native re-proof). Grades:
`[PROVED]` = a Lean statement read here; `[derived]` = on paper in this note, not in Lean, not run.

---

## 1. The architecture of our order-seven proof

Call **T7** the one arithmetic fact the proof uses: every nonzero residue mod 7 is a unit (`φ(7) = 6`;
`OrderSevenTotientN`). Each step below is marked by whether it uses T7.

1. **The instant.** Every case ends at `t = K/(7P)` with every reading `d·K mod 7P ∈ [P, 6P]`
   (`lonely_seven_of_band`, the residue-band rule at `q = 7P`). `P = 7^m`, except §7 (`P = 14`). *No T7.*
2. **Descent.** All readings multiples of 7: divide by 7; all even: divide by 2 (only §7 needs an odd reading). *No T7.*
3. **Levels and digits.** `m` = the largest 7-adic valuation; `N = 7^{m+1}`; `q(x)` = the top base-7 digit of
   `x mod N` (`qval`). A reading with `q ∉ {0, 6}` is in the band. *No T7.*
4. **The multiplier identity** (`qz_lambda`, equation (3)): for `λ = 1 + k·7^{m−j}` and `7^j ∣ x`,
   `q(λx) = q(x) + k·(x/7^j)` in `ZMod 7`. A reading at a higher level does not move. *No T7: pure algebra.*
5. **One level** (`single_level_avoid`): each reading's map `k ↦ c + k·r` must be a bijection of `ZMod 7`, which T7
   gives for every nonzero slope; then two forbidden digits per reading, at most three readings, `6 < 7`, leave a free
   `k`. *Uses T7.*
6. **The top level** (`band_top`): a top-level reading `7^m·u` times a unit `λ` has digit `λu ≠ 0`, always in the band.
   *Uses T7.*
7. **The level induction** (`unit_filtering`, their Lemma 2): top level first, then downward; the multiplier stays a
   unit; lower steps never move higher levels. *T7 at the top step.*
8. **The easy branch** (`corollary3`): every level below the top has at most three readings.
9. **The hard branch** (`bs_discrete_q`): one level below the top has four or more readings (at most one can, since
   `|D| = 6`).
   - A crowded *interior* level is brought to the bottom by a pre-multiplier (`exists_pre_congr`, BS eq. 8; T7).
   - Four readings at the bottom: `four_band` (§5, `OrderSevenA4N`, `S5bN`): sign-normalise the residues into the
     squares `{1, 2, 4}` (T7: `−1` is not a square mod 7), group readings by residue (ratios lie in `{2, 4}`),
     **compress** the digits into an arc of length at most 5 at a small dilation `j ∈ {1, …, 5}` using the carry lemma
     `q(x + y) ∈ {q(x) + q(y), q(x) + q(y) + 1}`, then **shift** the arc off `{0, 6}`.
   - Five at the bottom, `m ≥ 2`: `five_band` (§6, `OrderSevenA5N`, 6,008 lines; cases on the residue classes).
   - Five at the bottom, `m = 1`: `five_band_m1` (§7), exact tables at modulus 49 or 98.

---

## 2. Each step at order eight

The band at order eight is `[P, 7P]` at modulus `8P`: the top **octal** digit in `{1, …, 6}` (digit 7 only at exactly
`7P`). Two forbidden digits of eight, `{0, 7}`. Levels are 8-adic valuations `ν₈`.

| step | at order eight | status |
|---|---|---|
| 1 instant | the certificate at modulus `8P` (`lonely_eight_of_opening`; `ExistenceAt8_congruence`) | `[PROVED]` |
| 2 descent | common factor (`lonely_eight_of_common_factor`) | `[PROVED]` |
| 3 levels, digits | `N = 8^{m+1}`, `q` = top octal digit | definitions |
| 4 multiplier identity | `λ = 1 + k·8^{m−j}`, `8^j ∣ x` ⇒ `q(λx) = q(x) + k·(x/8^j)` mod 8; higher levels unmoved (`8^{m−j+j′} ≡ 0 mod 8^{m+1}` for `j′ > j`) | `[derived]`: the same algebra, no T7 |
| 5 one level | the slope `r = x/8^j mod 8` may be a non-unit. The number of `k` a reading forbids is its **cost**: `r` odd, 2; `r ≡ 2 mod 4`, 2 (the image is a coset of the even residues and meets exactly one of `{0, 7}`, which differ in parity; preimage size 2); `r ≡ 4 mod 8`, 0 or 4 (the image `{c, c+4}` meets `{0, 7}` in at most one digit; preimage size 4). So cost `≤ max(2, gcd(r, 8))`, and a free `k` exists when the costs sum to at most 7 | `[derived]`; the general single level is `single_level_avoid_general` and its failure with bare `r ≠ 0` at `ZMod 8` is `single_level_avoid_false_at_8` (`BS_TRANSFER_v2`, `[PROVED]` there) |
| 6 top level | `8^m·r` times an **odd** `λ` has digit `λr mod 8 ∈ {1, …, 7}`, always in `[8^m, 7·8^m]` (BS_TRANSFER_v1's "cage") | `[derived]` |
| 7 level induction | every `1 + k·8^{m−j}` with `j < m` is `≡ 1 mod 8`, so the multiplier stays odd | `[derived]` |
| 8 easy branch | every level below the top costs at most 7 ⇒ an odd `λ` puts every reading in band at `8^{m+1}` | `[derived]`; **subsumed by `lonely_eight_of_descent`** (below) |
| 9 hard branch | level 0 (the non-multiples of 8) costs at least 8 | **this is the residual's `cost` field** (below) |

**The case list is already this architecture, one level deep** `[read from the statements]`:
- `lonely_eight_of_descent` is step 5 at level 0: its hypothesis `Σ max 2 (gcd e 8) < 8` over the non-multiples of 8
  is exactly the cost bound of step 5 (with `r = e mod 8`), and the shift `j` of `t = (j + τ)/8` is the digit `k`.
  Instead of further levels, it sends the multiples of 8 to **order seven** through their cofactors (at most six), at
  order seven's instant `τ`.
- R6 (no multiple of 8) is the case `m = 0`; the common factor is step 2.
- So the easy branch at order eight (step 8) is contained in descent: if level 0 costs at most 7, descent applies.

**The residual is the hard branch, and only at the bottom level** `[derived from the field definitions]`: every
`EightResidual` set has level-0 cost at least 8 (its `cost` field). The shapes v21 §17C lists, (multiples of 8,
non-multiples) `∈ {(1,6), (2,5), (3,4), (4,3)}` with one non-multiple `≡ 4 mod 8` in the last, are exactly a crowded
level 0: six, five or four readings at cost 2, or three with one at cost 4 (`4 + 2 + 2 = 8`). A crowded **interior**
level, which order seven's own hard branch has to handle (`exists_pre_congr`), never needs handling at order eight:
the multiples of 8 are settled by order seven through their cofactors, whatever their levels. So at order eight the hard
branch is the bottom level only.

---

## 3. What order seven's hard branch uses, and where each piece stands at eight

| order seven (four or five at the bottom) | at eight (three to six at the bottom) |
|---|---|
| sign normalisation into the squares `{1, 2, 4}` (index 2; `−1` a non-square) | the units are `{±1, ±3}`, not cyclic (`(Z/8)^× ≅ Z/2 × Z/2`); sign normalises odd residues into `{1, 3}`; the non-units `2 ≡ −6`, `4` are separate classes. Four classes `{1, 3, 2, 4}` |
| readings grouped by residue; same-residue readings move rigidly under a level-0 step | the same, with up to six readings in four classes, so classes repeat |
| the carry lemma `q(x + y) ∈ {q(x)+q(y), q(x)+q(y)+1}` | base-free: holds for octal digits `[derived]` |
| compression into an arc of length ≤ 5 of 7 at a dilation `j ≤ 5` | the target arc has length ≤ 6 of 8 |
| a shift off `{0, 6}` | a shift off `{0, 7}`; for a class with slope `≡ 4 mod 8` the step moves its digit by 0 or 4 only |
| freedom used: the full multiplier (dilation and shift) at modulus `7^{m+1}` | descent uses only the eight shifts at one fixed `τ`. Unused so far: **the choice of `τ`** (any lonely instant of the cofactors, of which order seven guarantees one with margin `1/56`) and **dilations** |

---

## 4. Consequences (M7)

**Consequence:**
- **Q6, answered in part** `[derived]`: our order-seven architecture carries to order eight step by step through the
  easy branch, with T7 replaced by the cost bound, and the case list already contains that part (descent, R6, the common
  factor). What does not carry is order seven's hard-branch mechanism, which rests on T7 at every stage (normalisation
  into a cyclic subgroup of squares, bijective level steps).
- **Q5, the interim reduction** `[derived]`: the residual's infinite family is reduced, by the positive-arithmetic
  fields alone, to one shape: **a crowded level of non-multiples of 8 (cost ≥ 8) with the multiples of 8 carried by
  order seven.** The open statement is a statement about that one level.
- **A simplification over order seven** `[derived]`: interior crowding, one of order seven's hard sub-cases, does not
  occur at order eight on this route.
- **Freedom not yet spent** `[reasoned]`: descent fixes `τ` (order seven's instant) and uses eight shifts. The crowded
  level can also use the choice of `τ` among the cofactors' lonely instants, and dilations, which is what order seven's
  hard branch spends (compression at a small dilation).
- **What this does not establish:** that a translated compression-and-shift closes the crowded level at eight; that
  the four classes `{1, 3, 2, 4}` behave as order seven's `{1, 2, 4}` do. Nothing here is run.

## 5. Next, source first

1. Read `four_band`'s argument in full (`OrderSevenA4N`, `OrderSevenS5bN`: the compression phase and the shift), and the
   case structure of `five_band` (§6), since these are the mechanism the crowded level at eight needs a counterpart of.
2. Then a map run (M2 (d)): the residual sets on a window, their level 0 in sign-normalised classes mod 8 with costs,
   and whether the cascade's certificate for each uses the freedom §3 lists (a different `τ`, a dilation). No
   statement is proposed before that.
