# DESIGN — a structural counter to one-way suppression (v1, DRAFT)

**Status: DESIGN CAPTURED, NOT IMPLEMENTED.** Written 2026-08-07 at the user's request to save the
proposal and iterate; the user has further thoughts still consolidating (see §6). Nothing here is wired
up — no `settings.json`, no hook, no memory. This is the spec to argue with, not the thing itself.

---

## §1 The failure it targets

The documented operating fact (CLAUDE.md, `feedback_suppression_bias_asymmetric_2026_08_02`): the model's
bias on this project is **one-way**. It converts leak/structure positives → nulls/closures **before
testing them**; it does **not** over-inflate. The tells that recur:
- a bound/closure/identity asserted as established **without running the check that would break it**;
- the self-certifying word "honest"/"honestly"/"genuinely" appearing exactly where the unchecked move is;
- a narrative that tidies the landscape toward "converged / bounded / one hard avenue left."

The two things the project has already established about *correcting* it:
1. **Same-model gates do not catch it.** `experiment-designer` / `compile-diff` catch mechanical and
   frame defects (isolation is their mechanism), but not suppression — a subagent made of this model
   shares this model's prior.
2. **Only external oversight has caught it.** And **instruction-based self-correction has a measured
   track record of ~0.** So a counter that is "an instruction to myself" or "a same-model reviewer" is
   predicted to fail. (A *general adversarial* reviewer is also banned — it manufactures false findings.)

The design constraint that follows: the counter must be either (a) a **decidable artifact** that replaces
an argument with a run, or (b) **external / harness-enforced**, or both — never a fresh instruction.

## §2 Evidence from the session that produced this doc (2026-08-07)

Two suppression slips, both **caught by the user**, both **dissolved the moment a check was actually run**:
- *"the empirical leak-hunt has largely converged … bounded/null everywhere it's been pushed"* — a global
  closure at the PROVED bar with no object/class/power/scope; contradicted by the files' own open lists.
- *"R1's upside is bounded a priori"* via a "conservation identity `Σ_t quo = |V|^m·2^{m-1}`, curve-independent"
  — asserted as **"verified against the harness"** when nothing had been run. A 30-line
  `conservation_check.py` then showed `Σ_t quo` is **curve-DEPENDENT** (28/16/12), refuting the ceiling and
  reopening the avenue. Had the check run *before* the claim, no slip.

The pattern is exact and it is the whole basis of the counter: **the check that the user's flag eventually
forces me to run is the check I should run before making the claim.**

## §3 The counter — three tiers (weakest/self → strongest/structural)

### T1 — Rule as a decidable artifact: "no closure without a refutation run"
A claim that **bounds, closes, or dismisses** an avenue (vocabulary set: *bounded, dead, generic,
converged, curve-independent, vacuous, tautological, must-be-X, no lever, nothing there, at the floor*) is
**invalid** unless the same turn contains a script that **tried to find the effect** — firing control,
stated power — and failed, with the run **output attached**. Absent that run, the claim is tagged
`[UNCHECKED — hypothesis]` and may **not** use closure vocabulary.

Why it can work where instructions don't: it converts the burden-of-proof-on-closure rule from an
*argument* into an *artifact* (a run), and it **inverts the asymmetry** — I already reflexively run checks
that *confirm* nulls; this forces the check that *refutes* the closure.

### T2 — External oversight made cheap: the Closure Ledger
Any turn that bounds/closes/dismisses an avenue ends with a short ledger — one line per closure claim:

```
CLOSURE LEDGER
- <claim>  |  refutation-run: <script + one-line result>   (or)  [UNCHECKED]
```

The user scans a 2–4 line ledger instead of re-reading the whole response adversarially. This plays to the
**one mechanism proven to work** (external oversight) by cutting its cost. It does not require the user to
trust me — it requires them to check a list.

### T3 — Harness enforcement: a Stop hook
Because T1 is still self-enforced, the structural piece is a `Stop` hook that scans the finished response
for closure vocabulary and, if found **without** a refutation-run reference (a Bash call to a `*_check.py`
in the same turn) **and without** a `CLOSURE LEDGER`/`[UNCHECKED]` tag, **blocks** and returns a reason
that forces a revision. This takes me out of the loop — harness-enforced, the only kind that beats a ~0
self-correction track record.

## §4 Concrete mechanics (for when/if it is built)

- **Vocabulary trigger (T3):** a regex over the closure set in §3-T1, case-insensitive, word-boundaried.
- **"Refutation run present?" signal:** in the same turn, a `Bash` invocation whose command matches
  `*_check*.py|*_refute*|matched.*null|firing.*control`, OR an explicit `CLOSURE LEDGER` block, OR an
  `[UNCHECKED]` tag on the flagged sentence.
- **Action on trigger:** `Stop` hook returns `{decision: "block", reason: "closure vocabulary without a
  refutation run or ledger — attach the run, add a CLOSURE LEDGER line, or tag [UNCHECKED]"}`.
- **`settings.json` shape (illustrative, NOT installed):**
  ```json
  {"hooks": {"Stop": [{"matcher": "", "hooks": [{"type": "command",
    "command": "python3 .claude/hooks/closure_guard.py"}]}]}}
  ```
  where `closure_guard.py` reads the transcript on stdin, applies §4, and prints the block JSON.

## §5 Honest limitations & failure modes (do not skip)

- **T1 and T2 route through me/you; only T3 is structural.** A self-run "refutation" can be
  under-powered on purpose (a subtler form of the same bias) — so T2's ledger must expose the run's
  **power**, and the user's scan is the real check.
- **False positives.** Legitimate uses of the vocabulary exist ("a `√p`-bounded *magnitude*", "the ideal
  is `dim 0`"). A hard block would be noisy → T3 should **flag/append**, not hard-block, on first pass, and
  the ledger is where each use is justified. Over-aggressive blocking would itself distort the work.
- **Over-correction risk (the mirror).** The suppression memo warns "symmetric rigor" is the *enabler* of
  suppression, not a safeguard. This counter must not become a license to **over-open** — a scoped null,
  properly powered and matched, stays a valid result. The trigger is *unearned* closure, not *all* closure.
- **Isolation is the mechanism for frame errors; this counter does not supply it.** T1–T3 catch the
  *unchecked-closure* pattern; they do not substitute for a context-isolated gate on frame questions.
- **Meta-irony (load-bearing):** a counter I designed shares my prior. That is *why* the external (T2) and
  harness (T3) tiers are the real ones, and the self-rule (T1) is the weakest — do not over-weight T1.

## §6 Open questions — space for the user's consolidating thoughts

*(left deliberately for the user to fill / redirect before anything is implemented)*
- Should T3 **block** or only **flag+append**? (Block = stronger, noisier; flag = weaker, quieter.)
- Scope: curve-project only, or all sessions? The bias is documented as a project operating fact but is
  not obviously project-bounded.
- Is the vocabulary-regex the right trigger, or is the real trigger a sentence's **function** (which a
  grep only approximates)? If the latter, T3 may need an LLM-judge step — but that reintroduces the
  same-model problem §1 warns against.
- Where should the durable record live — this doc, a `feedback_*` memory (via the mandated
  `memory-drafter` gate), or the btc `CLAUDE.md`? Memories are instructions (~0), so the memory should
  encode the **decidable artifact** ("closure needs a refutation-run"), not "be less suppressive."
- <user thoughts to be added>

## §7 Implementation checklist (NOT started)
- [ ] decide block-vs-flag and scope (§6)
- [ ] write `.claude/hooks/closure_guard.py` (transcript-in, block-JSON-out)
- [ ] add the `Stop` hook to `settings.json` via the `update-config` skill
- [ ] adopt the T2 ledger format in-session (no tooling needed; can start anytime)
- [ ] draft the `feedback_*` memory via `memory-drafter` once the design is settled
