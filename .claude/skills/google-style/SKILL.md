---
name: google-style
description: >
  Rewrite prose for clarity and directness using the Google developer
  documentation style guide, adapted for math-research comms. Use when writing or
  revising anything meant to be read — conclusions, summaries, abstracts,
  handovers, reports, READMEs, memory bodies, or a chat reply — or when invoked
  explicitly (/google-style) on a draft or a named file. This is a READABILITY
  pass only: it never changes the certainty, grade, scope, or meaning of a claim.
  Run it AFTER the content and its grades are fixed, never as the step that
  decides them.
---

# Google style — a readability pass, not a verdict pass

You rewrite prose so it reads clearly and directly, following the Google developer
documentation style guide. You are a **layer over finished content**. The facts,
the grades, and the scope are already decided before you run. You change *how it
reads*, never *what it claims*.

## Rule 0 — the firewall (read before any edit)

This skill governs **style**. It has no authority over **calibration**. On this
project the two are different objects and must never be confused (see
`memory/feedback_suppression_bias_asymmetric_2026_08_02.md`).

You may **not**:

- change a claim's certainty in either direction — never strengthen *empirical*
  into *established*, never soften *proved* into *appears to*;
- delete or alter a **grade token** (`PROVED` / `VERIFIED-INSTANCE` / `EMPIRICAL`
  / `CITED` / `ASSERTED`) or a **scope qualifier** ("on the sampled set", "for
  this floor", "n = 7 only");
- remove a hedge that **carries epistemic content**. "This is an empirical null,
  not a proof" is a grade, not weak writing — keep it verbatim.
- add a conclusion, implication, or "so what" that the source did not state.

The Google guide's advice to cut hedges and weak words (below) applies **only to
rhetorical hedges that carry no epistemic content** — "it seems fairly clear
that", "somewhat", "quite", "rather". A word that fixes *how sure* a claim is
survives untouched. When unsure whether a hedge is rhetorical or epistemic,
**keep it and flag it** — do not cut it.

If applying a style rule would change what a sentence claims, the style rule
loses. Report the tension instead of resolving it silently.

## The pass, in order

1. **Voice — active, present, declarative.** The subject performs the action.
   Present tense for standing facts.
   - *was verified by the script* → *the script verifies*
   - *it was found that the bound holds* → *the bound holds*
   - Math statements are declarative, not addressed to a reader — prefer "The
     sweep found no signal", not "You can see the sweep found no signal". Reserve
     second person ("you") for instructions and chat replies.

2. **Cut filler.** Remove words that carry no information.
   - Delete openers: *it is worth noting that*, *it is important to note*, *as we
     can see*, *interestingly*, *notably*, *of course*, *basically*.
   - *in order to* → *to*; *due to the fact that* → *because*; *at this point in
     time* → *now*; *a number of* → *several* or a count; *is able to* → *can*.
   - Kill weak existentials: *there is a bound that constrains* → *a bound
     constrains*. Avoid *there is / there are* as sentence openers.

3. **De-nominalize.** Turn buried verbs back into verbs.
   - *perform a calculation of* → *calculate*; *make a decision* → *decide*;
     *provides a reduction of* → *reduces*; *is a violation of* → *violates*.

4. **Ban hype and unsupported claims.** This is the ally of the project's
   "no editorializing" rule — the Google guide forbids the same words.
   - Never: *easy, simple, just, trivially, obviously, clearly, of course,
     quickly, painless, powerful, robust, seamless, elegant, deep, striking,
     remarkable, fast, best, secure* — when used as an unsupported adjective.
   - This overlaps the project ban on difficulty verdicts (*research-grade,
     hardest piece, huge, great news*). Both are predictions dressed as facts.
   - A claim of a property needs a witness. *secure* / *closed* / *impossible*
     are not style words — they are grade claims and Rule 0 governs them.

5. **One idea per sentence; short sentences.** Split a sentence that joins two
   facts with a comma and *which*/*and*. Aim under ~25 words. Prefer a list when
   three or more parallel items appear in a sentence.

6. **Condition before instruction.** Put the *when* first.
   - *Run the matched-null control, if you are testing a positive.* → *If you are
     testing a positive, run the matched-null control.*
   - *To reproduce the count, shuffle then apply per-G caps.* (condition first)

7. **Global-audience clarity.**
   - No Latin abbreviations in prose: *e.g.* → *for example*; *i.e.* → *that is*;
     *etc.* → name the items or write *and so on* only when the set is obvious.
   - No idioms or cultural references. No negatives of negatives (*not
     uncommon* → *common*, unless the precise shade matters).

8. **Timeless writing.** Drop words that rot: *currently, now, new, recently,
   soon, as of today* — unless a date is the actual point (then give the date).

9. **No anthropomorphism of code or math.** Code and proofs do not *think, want,
   believe, try, or know*. *the proof believes X* → *the proof assumes X* or
   *X is a hypothesis of the proof*.

10. **Mechanics.**
    - Serial (Oxford) comma: *a, b, and c*.
    - Numerals for measurements, counts, and technical values (*7 runners*,
      *3 sorries*, *p = 7*, *floor 1e-06*). Spell out a number only when it opens
      a sentence, or reword so it does not.
    - Headings in sentence case, parallel in form, descriptive of content.
    - Lists: parallel grammar; capitalize the first word; end with a period only
      if the items are full sentences.
    - Contractions are fine in chat and READMEs; avoid them in formal manuscript
      prose.

## Before / after (shows the firewall working)

**Before** — wordy, flattened, and it lets a grade claim leak in:

> It is worth noting that, after a fairly extensive investigation, the search did
> not appear to uncover any clear evidence of leakage, which perhaps suggests that
> this avenue is likely now closed and that the curve is secure against this class
> of attack.

**After** — direct, and the grade/scope are preserved, not smoothed:

> The matched-null sweep (12k samples, floor 1e-06) found no leakage signal above
> threshold. Grade: EMPIRICAL. Scope: this sampler and floor only. This is an
> empirical null, not an analytical proof — it does not close the avenue, and it
> is not evidence the curve is secure.

What changed: cut *it is worth noting / fairly / appear to / perhaps / likely /
now*; active voice; one idea per clause. What did **not** change: the null stayed
a *scoped empirical null*, and *closed* / *secure* were refused entry, not
polished. Style tightened the sentence; Rule 0 protected the claim.

## How to run it

- **On a draft in the conversation:** rewrite the target text, then add a one-line
  note of what you cut or restructured. Keep the note short.
- **On a file** (invoked as `/google-style path`): read the file, apply the pass,
  and — per project versioning rules — write the result to the **next version**
  of a `.md`/`.tex` paper (never overwrite); edit prose files that are not
  versioned papers in place.
- **Order in the pipeline:** content and grades first, then this pass. If a
  calibration gate (`compile-diff`, the grade tags) has not run yet, style the
  prose but do not treat the pass as sign-off — it cannot certify a claim.

## What a good result looks like

Dry, short, declarative sentences; no hype; every grade and scope word still
present and unaltered. If the "after" reads more *confident* than the "before"
about anything the math did not settle, the pass failed Rule 0 — redo it.
