# n=8 Outlier Release Mechanism

Date: 2026-04-12
Status: prototype mechanism note

## 1. Why the two outliers are really one prototype

The two bounded outliers from [dropped_unit_repair_scan_2026-04-12.md](/Users/trentpalelei/Desktop/Math%20Ex/reports/dropped_unit_repair_scan_2026-04-12.md) are

- `E=(2,8,10,11,12,13,14)`,
- `E=(2,10,11,12,13,14,16)`.

For the dropped-unit branch, these are the same non-divisible configuration, because the divisible speeds `8` and `16` do not belong to `E_non`.

So both outliers reduce to the same retained non-divisible set

`E_non = {2,10,11,12,13,14}`.

The missing unit is `d=1`, so the old canonical target is

`r_d = -1 = 7 mod 8`.

The unique base-fibre patcher is

`10 = 8 + 2`,

and it satisfies the exact patcher congruence

`rho = 2 ≡ (q+1)d (mod 8)`

with `q=1`.

## 2. Base-fibre coverage

At the base fibre `b_0 = L/8`, the blocked sets are:

- `2 -> {0,4}`,
- `10 -> {3,7}`,
- `11 -> {2,5}`,
- `12 -> empty`,
- `13 -> {3,6}`,
- `14 -> {1,5}`.

So the full obstruction at `b_0` is achieved by the coverage multiplicities

- `0`: only `2`,
- `1`: only `14`,
- `2`: only `11`,
- `3`: `10,13`,
- `4`: only `2`,
- `5`: `11,14`,
- `6`: only `13`,
- `7`: only `10`.

In particular:

- the canonical missing-unit target `7` is uniquely patched by `10`,
- the complementary residue `5` is shared by `11` and `14`,
- the other potentially vulnerable odd residue `3` is shared by `10` and `13`.

## 3. Effective change timeline

The actual release mechanism appears only after tracking the **effective** changes in bad sets. For the relevant runners, the first changes are:

1. `b = 18480`, runner `13`:
   - `{3,6} -> {1,6}`
   - residue `3` is dropped,
   - residue `1` is added.

2. `b = 21840`, runner `11`:
   - `{2,5} -> {2,7}`
   - residue `5` is dropped,
   - residue `7` is added.

3. `b = 24024`, runner `10`:
   - `{3,7} -> {3,7}`
   - first reset is inert.

4. `b = 25740`, runner `14`:
   - `{1,5} -> {2,6}`
   - residues `1,5` are dropped,
   - residues `2,6` are added.

At this fourth event the residue `5` is uncovered, so the first safe fibre occurs at `b=25740`.

## 4. Why the burden is released at 14 rather than 10

This is the key structural point.

### 4.1 The patcher `10` is a lagging non-unit

The patcher `10` has residue `2 mod 8`, hence `gcd(2,8)=2`. For this kind of non-unit, consecutive floor states can produce the same bad set. In the present case:

- floor `1` gives `{3,7}`,
- floor `2` also gives `{3,7}`,
- floor `3` gives `{2,6}`.

So the first reset of `10` does not move its blocked set at all. The patcher is real, but its first reset is inert.

### 4.2 The unit runners migrate the burden away from the canonical target

Before `10` has any effective change, the unit runners move first:

- `13` changes `{3,6} -> {1,6}`, so residue `1` is no longer unique to `14`;
- `11` changes `{2,5} -> {2,7}`, so residue `7` is no longer unique to `10`.

After these two unit moves, the coverage picture just before `b=25740` is:

- `1`: `13,14`,
- `3`: only `10`,
- `5`: only `14`,
- `7`: `10,11`.

So the original burden at the canonical target `7` has become **redundant**, while a new unique burden has formed at residue `5`.

### 4.3 The faster non-unit runner releases first

Now the vulnerable residues are carried by the non-unit pair:

- `10` uniquely carries `3`,
- `14` uniquely carries `5`.

Both `10` and `14` are `gcd=2` non-units, so both have the same “stalled first reset” phenomenon. The decisive point is therefore timing:

- the next effective change of `14` occurs at `3L/14`,
- the next effective change of `10` occurs at `3L/10`.

Since

`3L/14 < 3L/10`,

runner `14` changes first. When it changes

`{1,5} -> {2,6}`,

the residue `5` is dropped and nothing else covers it. That is the safe fibre.

So the burden is released at `14` not because `10` was irrelevant, but because:

- `10` patched the original target,
- unit runners made that target redundant,
- the vulnerability migrated to a companion residue,
- and the faster lagging non-unit `14` was the first runner forced to release it.

## 5. Best interpretation

These outliers do **not** contradict the patching-runner idea. They refine it.

What fails is the too-strong statement

> the patcher itself must be the runner whose reset creates the first safe fibre.

What survives is the stronger structural picture:

> the missing-unit target creates a patching burden, that burden can migrate through later unit resets, and the eventual release can occur at a different residue and at a different runner's effective reset.

This is better described as **burden migration** or **transport migration**, not as a one-runner shadow theorem.

## 6. A plausible repaired theorem shape

The prototype suggests the dropped-unit repair should look like:

> if a unit residue class is missing, then either a safe chamber appears near the base fibre, or the missing-unit responsibility is carried by a finite transport network of patching runners. That burden can migrate between residues, but it cannot remain globally stable throughout `B_div`.

For the present outlier, the migration chain is:

`7` patched by `10`
`->` duplicated by `11`
`->` vulnerability transferred to `5`
`->` `14` releases `5`.

That is the cleanest current explanation of why the burden is released at `14` rather than at the original patcher `10`.
