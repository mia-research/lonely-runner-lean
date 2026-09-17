# What a proof of Existence is, derived from the framework's own objects

2026-09-17, at the owner's diagnosis: *"When I ask you how do we get to existence, I see you ask yourself
what a proof of existence would look like and it's at that point we end up going down avenues that don't
apply, because you go to reference other frameworks."*

That is correct and the record shows it. Every wrong avenue of this session entered at exactly that
moment: the first window, the covering bound `n > 2k`, the union bound, "the depths cannot all be near
zero", "`j ≥ 4` is the open case". Each is what a proof **of that kind of statement** looks like
elsewhere. None was derived from what this framework is.

So: derived here from §0's objects alone, with nothing imported and no analogy used.

---

## 1. What the framework produces

`OBJECT_REGISTER_v1` §0: **the output is the pair `(D, a)`.** Not a bound, not an estimate, not an
exclusion. The framework's mode is to **compute a point**.

## 2. How the framework decides

§0, the clearing test (Prop 2.1): at `t = a/(nD)` the difference `e` is clear ⟺
`D ≤ (a·e mod nD) ≤ (n−1)D`. **An integer comparison**, one per difference, decidable.

## 3. Therefore, what Existence is

Existence says the output is always defined: for every arrangement there is a valid `(D, a)`.

## 4. Therefore, what a proof is

> **A proof is a rule assigning to each arrangement a pair `(D, a)`, together with the integer
> comparisons showing every difference is clear there.**

A construction and its verification. Nothing else can count, because nothing else is what the framework
emits. This is why every bound-shaped route failed: a bound is not an output of this framework. It was
never going to be a proof of anything here, however tight.

## 5. The admissible shapes of such a rule

Three, and only the third is open:

| shape | status |
|---|---|
| a **closed form** for `(D, a)` from the differences | **refuted** — `RESEARCH.md`, 2026-09-17: *"no class admits a closed-form free-flank prediction"*, 174 prime-modulus families |
| a **finite procedure** that always returns a valid pair | this is the machine's `U`/`K` calculus; its verdicts are computed, not predicted |
| a **case division** into finitely many classes, each with its own rule | the per-`M` census is this, bounded at `M ≤ 60` |

So the framework's own requirement is the second: **the calculus is the theorem.** That is what
`RESEARCH.md` says today — *"the proof route is to formalize THAT mechanism, not to predict the
surviving flank"* — and it follows from §1–§4 rather than being a preference.

## 6. The requirement, stated with nothing outside it

The differences play two roles at once, and this is forced by the objects, not assumed: **each
difference is a flank, and each is also a ratio at every other flank.** There is no third thing in the
framework relating them.

So Existence at order 8 is exactly:

> **There is no seven-element set of positive reals in which every element's flank is shadowed by the
> other six** — where *shadowed* means: at every opening of that flank, some other difference fails the
> clearing test.

That is §6.9's *"not every flank of a runner can be shadowed at once"*, and it is the whole statement.
Nothing about measure, covering, density, windows, laps, or ratios appears in it.

## 7. What a proof of that must look like here  `[reasoning, marked as such]`

§1 says the mode is construction. So the native shape is **not** "derive a contradiction from all seven
being shadowed". It is:

> **Given that six flanks are shadowed, construct the opening of the seventh.**

Shadowing is not an obstacle to be excluded — it is *information*, and the framework's mode is to turn
information into a computed point. This is the inference I had not made, and it inverts the direction
of every attempt in this session.

There is already evidence it is the right shape, from the framework's own work:
`FLANK_OVERDETERMINATION_v1` §1 established that shadowing a flank **forces a divisibility relation**
between that flank and the other differences — large `gcd(d, e)` blocks far more than the generic
quarter. So shadowing six flanks *imposes arithmetic structure on the set*. Structure is exactly what a
construction consumes.

That document's §2 then reports the counting version failing — *"the arrangement of the blocked sets
decides, not their sizes"*. Read under §1 above, that is not a setback: it says the sizes are the wrong
object and the **arrangement** is the right one, which is a statement about residues, which is the
clearing test, which is the framework's own instrument.

## 8. What this changes about the work

- **Stop looking for a reason all-seven-shadowed is impossible.** That is the excluded-bound shape.
- **Start with the six shadowing conditions as given data** and ask what they determine about the
  seventh flank's residues.
- The machine already does this per family and always succeeds. What is unproved is not a bound on
  anything — it is that the construction never fails.

## 9. The test to apply to any future proposal

Before spending a day on a route, one question, answerable in a line:

> **Does it end in a pair `(D, a)`?**

If it ends in an inequality, a density, a count, a measure, or an impossibility, it is not a proof in
this framework, whatever its merits elsewhere. Every avenue this session that had to be withdrawn fails
that question, and it would have caught each of them before the work started rather than after.
