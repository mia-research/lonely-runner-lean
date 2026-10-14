# Working prompt — analytic proof of LRC at n = 8

Written 2026-09-08 after a full session that produced no advance on the goal, to encode what
the goal is and the specific ways this project fails at it. Use verbatim as a session brief.

---

## The goal

**Prove the Lonely Runner Conjecture for n = 8 analytically — establish WHY it is true.**

Rosenfeld (arXiv:2509.14111) settles it computationally: 27 primes, 32 hours of pruned C++.
That is **ground truth that the answer is yes, and nothing more.** It supplies no reason.
His architecture — MSS bound, then force enough primes to divide `∏v` — is *his* route, not
a definition of the problem. Do not adopt his yardstick; measuring our progress against his
54-orders-of-magnitude budget silently converts "understand why" into "decide his cells".

## Read before producing anything

The answer is more likely already written down than to be invented. Unread as of this brief,
and directly relevant:

- `docs/CORPUS_EXTRACT_allN_v11_8.md` (1063 lines), `..._n11_methods.md` (498),
  `..._n8_index.md` (781) — built as searchable indexes and never opened.
- `eleven_lonely_runners_v33.md` — the n=11 paper itself, second method. Only ever read via
  an agent summary.
- `lrc_n11_incompatibility_v1.md`, `docs/GENERAL_N_LINEAGE_AUDIT_v1.md`.
- `memory/MEMORY.md` §"Methodology (READ AT PROOF SESSION START)" — read it at proof session
  start, which is what it says.

## The mechanism, as the corpus already has it

`lrc_ap_worst_case_v1.md` (2026-03-27) is the closest thing to a "why" on file.

- **Overlap Principle.** Every runner blocks exactly `2/(k+1)` of the time regardless of
  speed, so the total blocked measure is decided *entirely by the overlaps* `B_i ∩ B_j`. At
  `n = 8`: seven bad sets of measure `1/4` on a circle of measure `1`; LRC(8) is the claim
  that at least `3/4` of overlap is forced.
- **Two extremes.** Every configuration is a deformation of one of: (1) the AP, uniform grid;
  (2) clumped-at-one-end plus an outlier. The AP is the minimum of bad-set spread; any
  movement makes the configuration looser.
- **The open step, named in that file:** *"'increasing free measure' needs to be proved, not
  just argued."* Two routes given — direct monotonicity (moving a runner toward another
  strictly increases free measure; obstacle: rational resonances along the path), and **MPP**:
  `{L > 0}` is open and path-connected in speed space. **Neither has ever been run**, and
  both are directly computable with the exact Boundary Set Method tooling now in
  `experiments/n8/`.

**The invariant is EQUIDISTANCE, not the value of `M`.** At `n = 8` there are three tight
instances (`M = 1/8`) up to speed 34: the AP and two others. The AP puts all 8 runners on the
uniform 8-grid at each of the four witness times; the other two have a *collision* (`12 ≡ 4`,
`13 ≡ 5` mod 8), only 7 distinct positions, never the grid. They are Extreme 2, not
counterexamples to AP-minimality. Comparing `M`-values instead of configurations is a
proxy-for-object error and was made in the session that produced this brief.

## Prohibitions — each of these happened in one session

1. **No sharpen-and-narrow.** `memory/methodology_understand_exceptions_2026_05_28.md`: when
   you draft v(n+1) of a theorem excluding what v(n) could not handle, **stop**. Ask instead
   what *forces* the witness to exist on the exception. Six such documents were written in
   one day.
2. **No replicating Rosenfeld.** Deciding sectors of the 27-prime × 5-sector ledger, or
   porting his search to C or Lean, is off-task by the project's own §0. A plan whose next
   step is "speed up the search" is the tell.
3. **A reformulation is not a reduction.** Four proposed reductions turned out to be logical
   *equivalences* to LRC(n) — Conjecture 5.2-H, `B ∩ I_A ≠ ∅`, the witness ladder,
   D7-for-large-`p`. Before claiming a reduction, ask what external input it consumes. If
   none, it proves nothing.
4. **Track the object, never a proxy.** Failures this session: `M = 1/8` for equidistance;
   `ps -p <parent>` for a live computation (the job had 2.3 s CPU in 59 minutes and no
   workers); coverage of a sufficient condition for a proof.
5. **No floats on any decision path**, reporting included. Run `experiments/n8/float_audit_v1.py`
   over every script *before* the run, not after; state the result with the claim.
6. **Read before writing.** Do not add to a corpus you have not read. Check `git log` at
   session start — another session may have superseded your position while you worked.
7. Pre-register sweeps (`experiment-designer`); verify citations (`citation-verifier`);
   controls must fire in both directions, and a planted positive is what distinguishes "no
   result" from "broken search".

## What counts as progress

A statement that is **proved** and **consumes something**: an external theorem, an induction
hypothesis we own (LRC(3)–LRC(7) are machine-verified and axiom-clean), or an explicit
construction. Theorem P (halving) qualifies — it consumes LRC(4)–LRC(7) and settles ~10% of
the residual class. Everything else produced this session was reformulation or Rosenfeld's
computation.

Understanding *why* also counts, and is the actual goal: a mechanism that explains the
extremal cases rather than excluding them.

## State

`n = 8` not proved. Rosenfeld's ledger: 2 of 135 cells — **irrelevant to this goal, recorded
only so it is not mistaken for progress.**

Proved and ours: the witness ladder (`q ≤ 8` divides some speed, else `t = a/q` wins — this is
exactly Lemma 7 where it is trivial, and it is maximal); the 2-adic cap table uniform in `p`;
Theorem P and P″; `U_min(1)`, `U_min(2)` closed forms; the tight-instance mechanism (odd
speeds in all four unit classes mod 8 pin the four witnesses, evens only cover the residue).

Verified: MSS Theorem A (`SUPPORTED-WITH-DELTA`), no tight instance carrying a multiple of 8
at speeds ≤ 34 (exact, 966 714 candidates).

**Start here:** run the two routes `lrc_ap_worst_case_v1.md` names and has never had run —
monotonicity of `L` along a deformation from a tight instance, and path-connectivity of
`{L > 0}` — using exact rational arithmetic. The two collision-type tight instances at `n = 8`
are the candidate obstructions to MPP and are the right first test case.
