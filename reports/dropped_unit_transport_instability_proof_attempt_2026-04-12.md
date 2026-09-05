# Dropped-Unit Transport Instability Proof Attempt

Date: 2026-04-12
Status: partial theorem note

## 1. Objective

The current dropped-unit repair target is no longer the old Sole Cover statement

> missing unit `=>` immediate miss at `r_d = -d^{-1}`.

The stronger surviving idea is:

> if the canonical dropped-unit target is patched at the base fibre, then the resulting patching burden cannot remain globally solvent throughout the divisible band.

This note does **not** prove that theorem in full generality. It does three smaller things:

1. isolates the exact local lemmas already available,
2. proves one nontrivial prototype theorem in the `n=8` outlier family,
3. states the precise transfer theorem that still remains open.

## 2. Exact local ingredients already available

### 2.1 Base-fibre patcher criterion

From [lrc_proof_v10_7.md](/Users/trentpalelei/Desktop/Math%20Ex/lrc_proof_v10_7.md#L313):

If `d` is a missing unit residue class and

`r_d = -d^{-1} mod n`,

then an actual retained speed

`e = nq + rho`

patches `r_d` at `b_0 = L/n` if and only if

- `rho ≡ qd (mod n)`, or
- `rho ≡ (q+1)d (mod n)`.

So the right local object is a **patching runner**, not just an omitted residue class.

### 2.2 Single-runner lifetime bounds

From

- [lrc_master_problem1_sf3_unit_permanent_cover_note_v1.md](/Users/trentpalelei/Desktop/Math%20Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_master_problem1_sf3_unit_permanent_cover_note_v1.md)
- [lrc_master_problem1_sf3_nonunit_permanent_cover_note_v1.md](/Users/trentpalelei/Desktop/Math%20Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_master_problem1_sf3_nonunit_permanent_cover_note_v1.md)

we already know:

- a fixed residue can be carried by a fixed unit runner on at most two consecutive unit floor states;
- a fixed residue or fixed support coset can be carried by a fixed non-unit runner on at most one two-state non-unit block.

Thus no single runner can sustain a fixed burden indefinitely.

### 2.3 `g=2` lag

For the outlier family the decisive non-units have `gcd(e,n)=2`.

By Lemma NPC.1, if `g=2`, then the active support blocks are exactly

`{2q-1, 2q}`,

and both floor states carry the same support coset `C_e(q)`.

So for `g=2` non-units:

- the first reset after entering a support block is inert,
- the effective support change occurs only at every second `e`-event.

This is the exact mathematical source of the lag seen in the `n=8` exceptions.

## 3. Empirical opening invariant

The bounded scan in [dropped_unit_repair_scan_2026-04-12.md](/Users/trentpalelei/Desktop/Math%20Ex/reports/dropped_unit_repair_scan_2026-04-12.md) shows the following:

In all scanned dropped-unit cases with full coverage at `b_0`,

- `n=5` with speeds `<= 3n`,
- `n=6` with speeds `<= 3n`,
- `n=7` with speeds `<= 2n`,
- `n=8` with speeds `<= 2n`,

there is always at least one residue of multiplicity `1` at `b_0`.

So the transport problem appears to start from a genuinely thin residue object, not from a perfectly redundant cover state.

This is still empirical, not yet theorem-grade.

## 4. Prototype theorem: the `n=8` outlier family

### Proposition 4.1 (proved prototype)

Let `n=8`, and let the retained non-divisible speeds be

`E_non = {2,10,11,12,13,14}`.

Then:

1. at the base fibre `alpha = 1/8`, the obstruction set is full;
2. the canonical dropped-unit target `r_d = 7` for `d=1` is uniquely patched by `10`;
3. the first safe fibre occurs at
   `alpha = 3/14`,
   where residue `5` is uncovered.

Equivalently, for any Case-2 tuple whose retained non-divisible set is exactly

`{2,10,11,12,13,14}`,

the first safe integer fibre is

`b = 3L/14`.

### Proof

At `alpha = 1/8`, the floors are:

- `floor(2 alpha)=0`,
- `floor(10 alpha)=1`,
- `floor(11 alpha)=1`,
- `floor(12 alpha)=1`,
- `floor(13 alpha)=1`,
- `floor(14 alpha)=1`.

Hence the bad sets are:

- `2 -> {0,4}`,
- `10 -> {3,7}`,
- `11 -> {2,5}`,
- `12 -> empty`,
- `13 -> {3,6}`,
- `14 -> {1,5}`.

Their union is all of `Z_8`, and residue `7` is covered only by `10`.

Now list the relevant event fractions before `3/14`:

- `2/13`,
- `2/11`,
- `1/5 = 2/10`,
- `3/14`.

These are ordered as

`1/8 < 2/13 < 2/11 < 1/5 < 3/14`.

We examine the obstruction set on the successive intervals.

#### Interval I: `1/8 <= alpha < 2/13`

The bad sets are the base-fibre sets listed above, so coverage is full.

#### Interval II: `2/13 <= alpha < 2/11`

Here only runner `13` has changed floor, from `1` to `2`, so

- `13: {3,6} -> {1,6}`.

All other bad sets are unchanged, so the union becomes

- `2 -> {0,4}`,
- `10 -> {3,7}`,
- `11 -> {2,5}`,
- `12 -> empty`,
- `13 -> {1,6}`,
- `14 -> {1,5}`.

This still covers all residues.

#### Interval III: `2/11 <= alpha < 3/14`

Now runner `11` also changes floor, from `1` to `2`, so

- `11: {2,5} -> {2,7}`.

Runner `10` crosses `1/5`, but because `gcd(10,8)=2`, its states `1` and `2` lie in the same two-state support block, so its bad set remains

- `10: {3,7}`.

Thus on the whole interval `2/11 <= alpha < 3/14`, the bad sets are

- `2 -> {0,4}`,
- `10 -> {3,7}`,
- `11 -> {2,7}`,
- `12 -> empty`,
- `13 -> {1,6}`,
- `14 -> {1,5}`.

Again the union is all of `Z_8`.

#### At `alpha = 3/14`

Runner `14` changes from floor `2` to floor `3`. Since `gcd(14,8)=2`, this is the next support block, so

- `14: {1,5} -> {2,6}`.

The full bad-set list is now

- `2 -> {0,4}`,
- `10 -> {3,7}`,
- `11 -> {2,7}`,
- `12 -> empty`,
- `13 -> {1,6}`,
- `14 -> {2,6}`.

Their union is

`{0,1,2,3,4,6,7}`,

so residue `5` is uncovered.

Therefore the first safe fibre occurs at `alpha=3/14`, with missing residue `5`. ∎

## 5. What this prototype proves conceptually

The proposition proves a genuine theorem instance of **burden migration**:

- the original dropped-unit burden begins at the canonical target `7`,
- the patcher `10` keeps `7` alive,
- unit runners `13` and `11` move first and make `7` redundant,
- the real vulnerability migrates to the companion residue `5`,
- the lagging non-unit `14` releases `5` before `10` reaches its next effective change.

So the exception is not pathological. It is a genuine transport phenomenon.

## 6. Best current general theorem candidate

The proved prototype suggests the following candidate theorem.

### Candidate DTI (Dropped-Unit Transport Instability)

Let `d` be a unit residue class missing from `R_non`, and let `r_d = -d^{-1}`.
If the base fibre `b_0 = L/n` is fully covered, then:

1. `r_d` is patched by one or more actual-speed patching runners,
2. the cover burden created by those patchers propagates along the boundary event path by a finite chain of burden transfers,
3. this chain cannot remain solvent throughout `B_div`,
4. hence some later fibre is safe.

The theorem is meant to allow:

- transfer to a different residue,
- transfer to a different runner,
- and lag before the releasing event.

So it is intentionally broader than a one-runner handoff theorem.

## 7. The exact remaining gap

What is still missing is the transfer theorem between the local single-runner bounds and the global safe-fibre conclusion.

The open statement is something like:

> **Chain-transfer control.**  
> Starting from a thin residue object at `b_0`, repeated successful re-cover can occur only finitely many times before some residue becomes uncovered.

The local pieces are already available:

- exact patcher criterion,
- exact unit and non-unit episode bounds,
- exact `g=2` lag in the hardest bounded outliers.

The unresolved part is the middle layer:

- how uniqueness/near-uniqueness transfers between residues,
- how many such transfers are possible before insolvency,
- and what invariant forces eventual failure.

## 8. Practical next theorem target

The broader strategic framing is recorded in [dropped_unit_overarching_structure_strategy_2026-04-12.md](/Users/trentpalelei/Desktop/Math%20Ex/reports/dropped_unit_overarching_structure_strategy_2026-04-12.md): the point is to extract a shared invariant, not to preserve the `n=8` prototype as a permanent sub-branch.

The cleanest next theorem target now looks like:

### Target CT.1 (thin-residue transfer theorem)

If a dropped-unit base fibre is fully covered and some residue has multiplicity `1` there, then along the monotone event path either:

- a safe fibre appears immediately after finitely many effective changes, or
- the multiplicity-`1` burden transfers to another residue carried by a different runner.

What still must be proved is that this transfer process cannot persist through the whole divisible band.

That is the exact bridge from the current prototype theorem to a full repair of the dropped-unit branch.
