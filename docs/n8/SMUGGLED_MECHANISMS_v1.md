# What has been smuggled into the manuscript

2026-09-13. Checked against the owner's fallback canvas, *LRC(8) — The Universal BSM
Framework*, §3 "The Firewall". Every finding below quotes the manuscript verbatim with a
line number. **Nothing has been changed.**

---

## 1. THE FIRST-INSTANT DEMAND — and it is in the definition of the procedure

**Firewall:** *"No 'First Instant' Demand: The framework proves that an isolation instant
exists within the window. It strictly avoids the over-demand of proving which instant
happens chronologically first."*

**MANUSCRIPT_v4 line 323, §7.1, the procedure itself:**

> …form the window `u ∈ [1/8, 7/8]`; read the other six inside it; **return the first point
> at which all are clear.**

**Line 335, §7.2:**

> Additionally, **the first instant of loneliness**, when it exists, is always an *opening*
> `(8k+1)/(8d)` for one of the runner's own differences — never a closing.

**Why this is the primary import, not a wording slip.** The canvas's master claim is that
the reading *"always yields a valid isolation coordinate `u*`"* — **existence**. The
manuscript's §7.1 specifies a **search for the earliest such point**, and §7.3's Claim then
inherits it:

> **Claim.** For every arrangement and every runner, the procedure returns **the** moment.
> *(line 341)*

The definite article is the over-demand. "A valid isolation coordinate" and "the first point
at which all are clear" are different statements, and the second is strictly stronger.

**Two consequences, both already visible in this session.**

1. Everything I built downstream searched for an interval's **first** clear point, because
   that is what §7.1 specifies. That is how the false counterexample was produced.
2. **The Lean is cleaner than the prose.** `procedure_sound` takes *any* `u` in the window
   with the readings clear — it has no "first" in it. The formal development already states
   the existence form. Only the manuscript demands the first.

**§1.3 is not the same thing and the manuscript conflates them.** Line 86 defends the
*first window* — *"buys a closed expression for the time — `t* = u*/d_min`"* — which is a
claim about which **window**, not about which **instant inside it**. The closed expression
`t* = u*/d_min` holds for any `u*` in the window. The first-instant demand buys nothing and
is defended nowhere.

---

## 2. THE STATIONARY FRAME — in the paper's headline evidence

**Firewall:** *"No Stationary Frame: No runner is ever pinned to zero."*

**The manuscript states the same rule itself, line 59:**

> The evaluation is local. Each runner is treated independently… and **no runner is held
> stationary at any point.**

**And then, line 351, §7.3, the paper's principal evidence:**

> exhaustively every integer arrangement with **`0 = v_1 < … < v_8 ≤ 40`** and gcd 1 —
> 18,564,316 arrangements, 148,514,528 runner-instances, zero failures

`0 = v_1` **is** a runner pinned to zero. The paper's largest single body of evidence is
computed in the frame its own §1.1 forbids.

**Where it came from is on the page.** Line 524:

> Rosenfeld states the conjecture with **a stationary runner** and `n − 1` non-zero speeds;
> the framework below holds no runner still, and the two formulations agree by the standard
> reduction.

The reduction is sound; the import is that the framework's own evidence was then generated
in the borrowed frame rather than its own. My `EXHAUSTIVE_OTHER_ORDERS_v1` sweep used `n`
distinct **positive** speeds with no pinning — that one is in the framework's frame, and is
the only sweep on record that is.

---

## 3. PINNING AS LOAD-BEARING — §4.4

**Line 224:**

> The normalisation `e₀ = 0` is **doing mathematical work, not bookkeeping. It pins one
> position at 0**; since all positions are non-negative that one is the sorted minimum…

The manuscript flags this itself and calls it load-bearing. It pins a **position** rather
than a speed, which is a weaker thing than §2's violation — but the firewall's wording is
"no runner is ever pinned to zero", and this says it pins one position at 0 and that the
pinning does the work. It is at minimum an unstated exception to §1.1 and should be either
justified as distinct from the speed frame or removed.

`int_of_pairwise_sep` in Lean carries the same hypothesis (`x k₀ = 0`).

---

## 4. THE GLOBAL EVENT — Corollary 4.4

**Firewall:** *"No Global Clock: The proof calculates up to eight different isolation times
for the eight distinct speeds, bypassing the need for a single, global isolation event."*

**Line 200:**

> **Corollary 4.4.** The number of **simultaneously** lonely runners lies in `{0,…,6} ∪ {8}`.
> It is never 7.

This is a statement about a single global instant at which several runners are lonely
together. Nothing in the framework's procedure needs it: the procedure is per-runner and
returns up to eight different times. Theorems 4.2, 4.3 and 4.5 use simultaneity legitimately
— they are about the AP reference, where it is the actual content — but **4.4 is a
free-standing global-clock result**, and it is one of the paper's advertised corollaries.

---

## 5. What was DROPPED: the firewall itself

The canvas's §3 is a **stated discipline**. In the manuscript it survives only as two
fragments — the "no runner held stationary" line in §1.1, and §1.2's boundary rule. There is
no statement anywhere in the paper of:

- no first-instant demand
- no global clock
- no measure, density, zero-measure or stability radius
- the retired vocabulary (witness, carrier, iteration, set emptiness)

**A reader cannot tell the framework's bans from its omissions.** Both §1 and §2 above are
violations a stated firewall would have caught in draft.

---

## 6. The tension the owner named, stated plainly

The canvas's **Resolution Core** is relay termination: Lemma 1 (`s/s' < 9/7`, the break at
`s = 4`) and Lemma 2 (gap migration, `k·b ≡ 0 (mod 8a)`).

In the manuscript that material appears **only as §6.2, a refutation** — *"The relay and
stretch-ratio refutation… Four facts defeat it, and each is exact."* Its fact 2 says the
`9/7` bound *"holds for **first** zones only"*, which is precisely the step Lemma 1 takes;
its fact 3 says a relay is built from *"zones, not runners"*, which is the step Lemma 2
takes; its fact 4 exhibits a single reading blocking both ends, so no relay is needed at all.

**§6.2 is not smuggled — it is the record that the proof attempt failed, and the owner says
as much.** What went wrong is that the refutation was kept while **the construction and the
warnings it was supposed to leave intact were not carried across**. The paper now contains
the negative result without the framework it was a negative result *about*.

---

## 7. Recommendation

1. **§7.1: strike "first".** "return a point at which all are clear" — this is what the Lean
   already states, what the canvas claims, and what §7.3 should claim.
2. **§7.2: strike the opening/closing sentence**, or move it to a remark explicitly flagged
   as an observation outside the claim.
3. **§7.3: regenerate or re-label the evidence.** Either rerun the sweep over `n` distinct
   positive speeds, or state plainly that the figure is in Rosenfeld's pinned frame and
   transfers by the reduction.
4. **§4.4: drop, or mark as an aside outside the procedure.**
5. **Add the firewall as a numbered section.** It is the part of the framework that stops
   exactly these imports, and it is the part that was lost.

**Nothing above has been applied.**
