# Naming versus existence: interrogating the test I ran

2026-09-18. Written because the test was ill-posed and the error is instructive.

## What I tested

```lean
def ExistenceAt8_named : Prop :=
  ∃ f : Finset ℝ → ℝ, ∀ ds, … → 0 < f ds ∧ Lonely 8 ds (f ds)

theorem named_iff_existence : ExistenceAt8_named ↔ ExistenceAt8   -- proved, axiom-clean
```

and concluded "naming is not stronger than existence".

## Why that is not a naming form

**The head symbol is `∃`.** It asserts that a naming function *exists*. That is an existence
claim about a function — I moved the quantifier outward by one type level and removed nothing.

`FRAMEWORK_CONJECTURE_v1` §3 asks for something else: *"A proof is an **exhibition**: the rules,
written down, with their conditions shown exhaustive."* **Written down.** A particular `f`, present
in the file. Not `∃ f`.

## Why Lean cannot state the difference

Exhibition is a property of a **definition**, not of a proposition. The naming form as §3 means it
is not a `Prop` at all — it is a pair:

* a definition `f : Finset ℝ → ℝ`, given by an expression, and
* a theorem `∀ ds, … → Lonely 8 ds (f ds)`.

Only the second is a `Prop`. By proof irrelevance Lean cannot lift "this proof exhibits a rule"
into the statement, so no `Prop` comparison can settle §3's question. **My test compared two
propositions where the requirement is about the artefact.**

## What classical choice actually gives

Sound: yes, `Classical.choice` is standard and the gate permits it.

Useful for §3: no. The extracted `f` has **no expression**. Lean refuses to compile it —

```
failed to compile definition, consider marking it as 'noncomputable'
```

It exists by axiom and names nothing you can read off. So the choice step is *valid* and
*irrelevant*: it converts one existence claim into another.

*(Precise about the reason: Lean's complaint cites `Real.decidableLT`, not `Classical.choice`.
Deciding a real inequality is not computable, so no function on arbitrary reals compiles.
Computability is therefore the wrong criterion — the right one is whether the rule is written.)*

## The point I missed: the framework has already exhibited its rule

```lean
noncomputable def move (n : ℕ) (ds : Finset ℝ) (t : ℝ) : ℝ :=
  ds.fold max t (fun d => if inWay n d t then nextOpening n d t else t)

noncomputable def nextOpening (n : ℕ) (d t : ℝ) : ℝ := ((⌈d * t - (n : ℝ)⁻¹⌉ : ℝ) + (n : ℝ)⁻¹) / d
```

Both are **explicit expressions**. The `open Classical` is only there to decide `inWay`, a real
comparison; it does not make the rule unwritten. This is an exhibition in exactly §3's sense, and
it is the opposite of a choice-extracted `f`, which has no expression at all.

## So there was never a tension

* §3's exhibition requirement is **already met**: the rule is `move`, written down.
* What remains open is `∃ N, move^[N] b = move^[N] b` — an existence statement **about the
  exhibited rule**, equivalently `CascadeCapped`.
* *"Existence is not what is being asked"* bans settling the conjecture by showing some instant
  exists **with no rule producing it**. It does not ban an existence statement about a given rule.

I read it as the second and built a false dilemma on top.

## And the withdrawal of 6.10–6.11 survives, for a sharper reason

Not "they conclude existence" — `CascadeCapped` concludes existence too. The difference is that
`move` is a rule you can *run*, and running it bounds the index; Proposition 6.11's pigeonhole
attaches to **no rule**, so there is nothing to run and no index. That is what the index-bound test
was reaching for, stated properly.
