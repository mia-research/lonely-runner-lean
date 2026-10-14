# Nativeness audit of the 2026-09-17 cap work, corrected

Supersedes `NATIVENESS_AUDIT_2026_09_17_v1.md`, which is kept as the record. **Two of v1's claims are
wrong and are corrected here** (§4), and the audit's main finding is replaced by a sharper one that v1
missed entirely (§3). Prompted by the owner's question of 2026-09-17: *"Are you sure you have the
cascade right. Because all speeds are known at once, all isolations crystalise at once, just because we
may find them one at a time doesn't mean its like a search."*

Artefacts: `experiments/n8/scale_recursion_check_v1.py` / `.out`, `first_window_nativeness_v2.py` / `.out`.

---

## 1. The implementation is the framework's  `[VERIFIED]`

`MANUSCRIPT_v9_1` §6.1 defines it, and the definition is what was implemented:

> *"The **move** sends `t` to the largest next opening among the runners in the way at `t`, and leaves `t`
> fixed if none is. The **cascade** — the determinator — is the sequence of moves from the **bound**
> `1/(8m)`."*

Checked three ways, exact rational arithmetic throughout:

- against `LRC/Cascade/Iteration.lean` transcribed verbatim — agreement on word and instant, no ties
  (`ladder_cap_word_lean_crosscheck_v1.out`);
- against **§6.2's scale recursion**, the framework's own coordinate —
  `D_0 = d_min`, `D_{j+1} = D_j·min{ s/(8N+1) : |s − 8N| < 1 }`, `instant = 1/(8·D_final)` —
  **6000 of 6000 shuffled arrangements agree, with identical step counts**, plus both cap-word readings
  (`scale_recursion_check_v1.out`);
- §6.2's identification is therefore reproduced rather than assumed: the moment iteration and the
  three-tier scale cascade of `OBJECT_REGISTER_v1` §0 are **one object in two coordinates**, not two
  objects sharing a word. A name collision was suspected and is refuted.

## 2. It is not a search, and the artefacts already say so  `[PROVED — Lean]`

`MomentIterationN.first_isolation_of_fixed` (`Iteration.lean:180`) proves of the fixed point:

    Lonely n ds (fix)  ∧  ∀ s, 0 < s → Lonely n ds s → fix ≤ s

The second conjunct quantifies over **every positive instant**, not over the iteration's own path. So
the fixed point is the **minimum of the lonely set** — a static object, determined by the speeds, which
the iteration computes. It is not "the first one the walk happened to find". This is the owner's point,
already formalised and axiom-clean.

Corroborating, in the framework's own words: §6.1 — *"There is no set of candidates: the runners in the
way at `t` fix the move."* §6.2 — *"the cascade is a recursion on the scale, **fixed by the speeds**."*
§1.3 — *"Not picking. Our cascade work shows it is directed by the speeds in the arrangement."*

## 3. Where the search actually entered: the word enumeration  `[the finding v1 missed]`

Not the cascade — the **certificate built on top of it**. `order_n_certificate_v1.py` enumerates
**words**, sequences of `(setter, lap)`, and asks of each which reading vectors would realise it. That
inverts the determination. The speeds fix the path, so the path is an **output**; enumerating paths and
solving back for speeds re-asks the construction's output as its input — `OBJECT_REGISTER_v1` item 22's
exact form, arriving on the word instead of the gap.

This also explains the infeasibility honestly. `LADDER_BOUND_v1` §1 attributes it to a flat ~16% pass
rate and calls the enumeration "the wrong instrument at order 8". The measurement is right and the
diagnosis is incomplete: the word space is 7.25×10²⁶ **because it is not the framework's object**. One
arrangement has one path. The combinatorial explosion is the cost of treating a determined thing as free.

**What survives this, and why.** Everything computed forward — speeds in, instant out — is native and
stands:

- the replay: given these readings, the determinator produces this instant (`ladder_cap_word_replay_v1`);
- the 28 000-arrangement sweep (`first_window_nativeness_v2`), which is the most native instrument used
  all day;
- `sup R = 7` **at the arrangement level** — the replay exhibits real arrangements reaching `R = 6.999992`,
  so it is not merely a statement about words.

**What does not survive as a target:** the complete enumeration, and Lemma A/B/C as posed. See §5.

## 4. Two corrections to v1

**(a) v1 presented the first-window identification as opening a route "that was not on the list". It was
on the list.** The manuscript's own revision table already records it:

> `§8.2 "Order 5 is open. In the cascade's quantity it is R < 4"` → `Existence with four differences at
> n = 5 is open; R < 4 a stronger sufficient statement` | **`R < 4` is the first window (audit R1;
> boundary audit B2)**

`V8_2_ISOLATED_AUDIT_v1` §R1 is titled *"No window, no bound on when"*. §1.3 of the frozen manuscript
states it outright: *"v7 confined its evaluation to the nearest neighbour's first relative lap and made
that confinement the open claim. The framework does not require it, and there is no window here: the
cascade runs over every lap, and no bound on when an instant falls is a requirement of any result."*
§8.2 classes `R < 4` as *"A stronger, sufficient statement … lonely within the nearest runner's first
relative lap."*

So the identity `R = n·u` and the 0-of-28 000 measurement are new; **the classification is not**, and v1
should have found it by reading §1.3 before writing. The correct statement is that the certificate line
re-imported a confinement the manuscript had already removed — a recurrence, not a discovery.

**(b) v1's second wording hit was over-applied.** It filed "terminate" under register item 25
(termination, NOT APPLICABLE). But §6.7 states Existence itself as *"the cascade reaches a fixed
point"*. The framework has the object; item 25 rejects termination as a property of an imported loop
over candidates, not the determinator's fixed point. The correct grade is MISPLACED — substitute
*reaches a fixed point* — not NOT APPLICABLE. The "witness" hit (item 6, 13 uses) stands as v1 had it.

## 5. The native target, and how far the R-programme sits from it

§6.7, verbatim:

> **Existence.** For every arrangement and every runner, the cascade reaches a fixed point — it arrives
> at a scale at which no reading lies within 1 of a multiple of 8. Equivalently, the run of
> lap-completion zones from the bound ends; equivalently, some flank has a lonely opening. `[OPEN]`

The R-programme is stronger than this in **two** independent ways, each documented in the manuscript:

1. **The window.** `R < n−1` demands the fixed point fall in the first lap (§1.3: not required).
2. **The instant.** §6.6: *"Existence needs some lonely instant, not the cascade's, so lonely lattice
   instants settle a runner as well (Corollary 6.4)."* The cascade's own instant is not required either.

So Lemma C's difficulty is not an obstruction to Existence. `RETURN_CORRECTION_v2` §4 concluded that
Lemma C as posed asks for a false statement — that conclusion stands and is now better placed: it asks
for a false statement **about a quantity no result requires**. A route that is both strictly stronger
than the target and provably unavailable should be set down, not repaired.

§6.7's own "What failure would require" names the native line instead, and it is arithmetic: a cascade
that never stops lands every step on an opening strictly inside another runner's zone, for ever, through
infinitely many distinct openings, each step satisfying `|e·a − 8w·d| < d` with `a ≥ d/d_min`. That is a
statement about integer residues, and residue and pigeonhole arguments are admissible tools under the
2026-09-15 ruling.

## 6. Consequent action taken

The exceedance beam search (`ladder_exceedance_beam_d24_v1`, launched earlier today, 12 h budget) was
**stopped at depth 8**. It searched the word space for a word exceeding the cap. Under §1.3 exceeding
the cap is not a defect, so the search was spending compute on an imported object to answer a question
no result requires. Partial output is kept.
