# Dropped-Unit Exception Anatomy

Date: 2026-04-11
Status: explanatory note

## 1. What kind of exception this is

This is **not** an exception to the Lonely Runner Conjecture.

It is an exception to the old manuscript-level inference:

> missing unit residue class `d`  
> `=>` canonical target residue `r_d = -d^{-1}` is uncovered on the initial Sole Cover window.

The failure comes from the fact that an actual retained unit speed

`e = nq + rho`

does not block the classical pair `{0, -rho^{-1}}` at the base fibre `b_0 = L/n`. Instead it blocks the affine pair

- `a_low(e) = -q rho^{-1}`,
- `a_high(e) = -(q+1) rho^{-1}`.

So a missing unit responsibility can be **shadowed** by a different retained speed whose quotient `q` shifts its exclusion pair.

## 2. The affine shadow mechanism

Let `d` be a missing unit residue class, with canonical old target

`r_d = -d^{-1} mod n`.

At the base fibre `b_0 = L/n`, an actual retained unit speed `e = nq + rho` covers `r_d` iff

- `a_low(e) = r_d`, or
- `a_high(e) = r_d`.

Equivalently:

- `rho ≡ q d (mod n)`, or
- `rho ≡ (q+1)d (mod n)`.

So the missing unit class `d` can be temporarily substituted by a retained speed whose residue is an affine multiple of `d`.

This is the precise reason the old Sole Cover witness can fail.

## 3. Why this does not destroy the deeper mechanism

The shadower does not cover `r_d` for free.

It must carry a **paired companion residue** with it:

- if `r_d = a_high(e)`, then the companion is `a_low(e)`,
- if `r_d = a_low(e)`, then the companion is `a_high(e)`.

At the next reset of `e`, one of the two residues is dropped and a new one enters.

So the shadow repair is rigid, not flexible:

- the missing target can be patched locally,
- but only by coupling it to another residue,
- and that companion may be the place where the real gap opens.

This fits the broader project picture very well:

> the obstruction is not absent; it has moved from a naive static missing residue to a coupled affine handoff problem.

## 4. Clean examples

### Example A

- `n=5`
- `E=(1,2,5,8)`
- missing unit class: `d=4`
- old target: `r_d = -4^{-1} = 1 mod 5`

At `b_0 = L/n = 8`:

- `1` blocks `{0,4}`,
- `2` blocks `{0,2}`,
- `8 = 5+3` has `q=1`, `rho=3`, so
  - `a_low(8)=3`,
  - `a_high(8)=1`.

Thus `8` shadows the missing target `1`, and the base fibre is fully covered.

But at the next reset of `8`, namely `b=10`:

- the blocked pair changes from `{1,3}` to `{1,4}`,
- so residue `3` is dropped.

The other runners do not cover `3`, so a safe chamber opens there.

### Example B

- `n=7`
- `E=(1,2,3,4,7,12)`
- missing unit class: `d=6`
- old target: `r_d = -6^{-1} = 1 mod 7`

At `b_0 = 12`:

- `12 = 7+5` has `q=1`, `rho=5`, so
  - `a_low(12)=4`,
  - `a_high(12)=1`.

Again the missing target `1` is shadowed at the base fibre.

At the next reset `b=14`:

- the blocked pair changes from `{1,4}` to `{1,5}`,
- so residue `4` is dropped,

and that is the safe residue.

## 5. The key interpretation

The exception is therefore:

**affine shadowing of a missing unit responsibility by a lifted retained unit speed.**

The likely repaired theorem will not say:

> missing unit class `=>` immediate gap at the classical residue `-d^{-1}`.

The first repair guess was:

> missing unit class forces either
> - an actual-speed static miss, or
> - an affine shadow; but every affine shadow is coupled to a companion residue and must eventually face a handoff event.

Subsequent bounded scans in [dropped_unit_repair_scan_2026-04-12.md](/Users/trentpalelei/Desktop/Math%20Ex/reports/dropped_unit_repair_scan_2026-04-12.md) showed that this is directionally right but too narrow as a universal theorem. The repair mechanism is broader than “the shadower’s own next reset.” What survives is the structural point:

> patching a missing-unit target imposes a coupled affine transport burden that cannot be stably maintained forever.

That is why this exception is valuable. It is not random noise. It shows the old witness was too crude, and it points toward a broader transport-instability statement.

## 6. Best current name

I would suggest calling this phenomenon:

**Affine Shadow Exception**  
or more descriptively  
**Affine Shadowing of a Missing Unit**

because that is exactly what is happening:

- the missing unit class is absent in residue support,
- but a lifted speed shadows its responsibility at the base fibre through the affine term `q`.
