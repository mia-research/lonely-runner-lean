# The framework's conjecture

2026-09-14. Proposed, for the owner's decision. **Nothing in the manuscript is changed.**

Written because the work keeps reverting to LRC's apparatus. The reason is structural, not
carelessness: **LRC asks whether something exists, so every attempt to prove it reaches for
an existence argument** — covering, counting, bounding the obstructions — and those are the
register's banned items. Stating the framework's own conjecture removes the pull, because its
statement cannot be discharged that way.

---

## 1. The statement

> **The Framework's Conjecture.** There is a **finite set of rules**, each of the form
>
> > *if [condition on the differences' gcds and residues] then the pair is `(D, a) = [formula]`*
>
> such that (i) every rule's pair clears — `D ≤ (a·e mod 8D) ≤ 7D` for all seven differences
> — and (ii) the conditions are **exhaustive**: every runner in every arrangement satisfies
> at least one.

That is the construction's contract written as mathematics. It says the isolation instant is
not merely there but **computed**, from gcds and residues, with no search.

## 2. Why this is not LRC, and is not implied by it

LRC(8) is settled — a time exists for every runner. **That does not give the conjecture**,
because existence says nothing about the form. Even the completeness result — every isolation
instant is some `a/(8D)` with `a` odd — does not give it: knowing the instants live in that
family is not a rule for producing one.

So the conjecture is **independent of LRC and strictly stronger**:

| | asks | answer at `n = 8` |
|---|---|---|
| LRC(8) | does a time exist? | yes, Rosenfeld 2025, by exhaustion |
| completeness | is every such time of the form `a/(8D)`? | provable; the interior case is proved |
| **the framework's conjecture** | **is there a closed-form rule that produces one?** | **open** |

And it has the corollary that matters: **the conjecture implies LRC(8)**, since a produced
pair is a produced instant.

## 3. What counts as a proof, and what cannot

A proof is an **exhibition**: the rules, written down, with their conditions shown exhaustive.
Nothing else discharges it.

This is the part that stops the drift. **A covering or counting argument cannot prove this
conjecture**, however strong, because such an argument concludes *"a candidate survives"* and
the conjecture asks *which*. Showing the blocked sets fail to cover the `4D` candidates
leaves every rule unwritten. §6.1 says the same thing about the window — *"Any proof must
therefore be pointwise: it must name an instant"* — and §1.1 says the instant is *"named, not
shown to exist"*. Under the conjecture that is not an exhortation; it is the statement.

The register's banned items become **inapplicable rather than forbidden**, which is a stronger
guard: measure, density, covering, set emptiness and witnesses all conclude existence, and
existence is not what is being asked.

## 4. What is already proved

Three rules, each producing its pair outright.

| condition | pair | covers |
|---|---|---|
| no difference `≡ 0 (mod 8g)` | `(g, 1)` | ≈ 40% |
| `d_max ≤ 7·d_min` (Thm 4.8) | `(d_min, 1)` | ≈ 30% |
| some `r ∈ {1,3,5,7}` clears every reading | `(d_min, r)` | ≈ 71–74% |
| **union** | | **0.71 – 0.83** |

Two closed forms support them, and both name rather than count:

- **dead** (§7c): `Dead` = divisors of `{d/8 : 8 | d}`; `L_0` the first live gap.
- **free** (new): `e` cannot block at gap `D` exactly when `8D/gcd(e,8D)` is even and `≤ 8`.
  In particular when `D | e` and `e/D` is odd.

## 5. What remains

**A rule for the runners the three miss.** For integer differences those are exactly the
runners with at least one difference `≡ 0 (mod 8g)` — the gcd lattice's failure, which is
all-or-nothing and so cannot be repaired by trying another candidate at the same gap.

The shape of what is needed: given the differences, **name** the gap `D` and the numerator
`a`. The `j = 1` case is the largest block and the natural first target, and its arithmetic
is already explicit — at `D = 2` the blocked candidates are exactly `±e⁻¹ (mod 16)` over the
odd differences `e`, which is a **named set**. A rule must produce a residue outside it by
formula, not argue that one is left over.

## 6. What this retracts

`COUNTING_AT_A_GAP_v1.md` reaches 86.8% by bounding the union of the blocked sets. Under this
conjecture **that document is the wrong shape throughout** — it shows candidates survive and
names none. Its two closed forms (free, and the `j = 1` arithmetic) survive because they name;
its bounds do not. Recorded rather than deleted, since the reasoning about where the overlap
concentrates is still true and may help a naming rule.

---

**If this is adopted, the manuscript's §7.4 is its `n = 8` instance, and LRC(8) is a
corollary rather than the target.**
