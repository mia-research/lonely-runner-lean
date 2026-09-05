# AUDIT — honesty flags on this session's own output (2026-09-01, Claude Code block)

*Self-audit of everything I produced today: `RESULT_jacobi_rationality_reduction_v1.md`,
`RESULT_jacobi_sign_law_proved_secp_class_v1.md`, `ROADMAP_REDIRECT_v4.md`, the `RESEARCH.md`
banner + backfills + entries (d)/(e), and three `HANDOFF_LOG` entries. Written because the session
made strong claims — a closure and a corpus-wide staleness verdict — and neither was checked by an
independent eye: **every project gate (`compile-diff`, `citation-verifier`, `experiment-designer`,
`memory-drafter`) was unavailable this session.** Ordered by severity.*

---

## F1 — **"Five of six avenues were stale" was OVERSTATED.** `[my error; corrected here]`

I opened the session by telling the user their open-avenue list was "stale on five of six items."
Re-scored honestly, item by item:

| their item | my verdict | correct verdict |
|---|---|---|
| Brick B (public-ε, CM-lattice, amicable) | stale | **fully stale — correct.** All four parts executed 08-18/20 |
| Brick A (E3) | stale | **stale as of the record I read, then RE-OPENED hours later** by another account (E3 chirality). Their instinct that E3 was live was vindicated |
| Brick C (phase) | stale | **stale, with a frame caveat I flagged but under-weighted**: v3 asked for a *phase measurement*; the artifact returns a *structural no-go*. Whether that answers the question or sidesteps it is a frame judgement no isolated reviewer has made |
| Brick D | stale | **half wrong.** D1 was indeed already proved. **D2 was genuinely open** — I closed it today. D3 (citation sweep) is live and my first v4 draft dropped it entirely |
| L-mono sheaf | open | **open — they were right**, though re-routed by a session hours earlier |
| two preregs | stale | **half.** LBE v2 is genuinely PRE-DATA — they were right. "D2 affine readability never run" is literally true; my "gated out, not neglected" is the useful correction |

> **Fair statement: two of six were fully stale (Brick B; Brick D's D1 half). The rest were partially
> stale, live, or live-but-re-routed.** "Five of six" counted a partially-correct item as wholly
> wrong. The document-layer defect (D-1/D-2/D-3) is real and independently evidenced — that finding
> stands — but I inflated how wrong the *list* was, which is the same deflation-of-someone-else's-work
> failure the project's own feedback memories warn about, pointed outward instead of inward.

## F2 — I claimed the m-law is now a theorem while relying on an unaudited `[PROVED]` grade `[RESOLVED 2026-09-02 — and the flag was RIGHT; see the resolution box at the end of this section]`

`RESULT_jacobi_sign_law_proved_secp_class_v1.md` §4 and my report both say the m-law
`m ∈ {−2,+1}` at `p ≡ 7 mod 12` is now a theorem. What I actually proved is **§2 of
`RESULT_jacobi_closed_form_m_law_v4.md`** — the Jacobi sign law. The step from there to the m-law is
that file's **§1 reduction**, graded `[PROVED]` *there*, which **I did not verify first-hand.**

This matters more than usual: that file opens with its own **SELF-AUDIT confessing v1–v3 defects**,
including an inflated tally (`34/34` → 15 distinct, 19 algebraically forced) and configurations where
"the hypothesis confirmed itself." A file with that history is exactly the wrong one to inherit a
grade from unchecked.

> **Corrected claim:** *the Jacobi sign law is proved at `p ≡ 7 mod 12`; the m-law follows **given**
> `RESULT_jacobi_closed_form_m_law_v4.md` §1, which is graded `[PROVED]` there and is **not
> re-verified here**.* **OWED: first-hand check of that §1 reduction** before the m-law is called a
> theorem anywhere else.

## F3 — I cited a stronger fact than the proof needs `[corrected in the artifact]`

The RESULT wrote `g(χ₂) = −g_p(χ₂')² = −(i√p)² = p`, invoking **Gauss's sign theorem**
(`g_p(χ₂') = i√p` at `p ≡ 3 mod 4`). The proof needs only the **square**, which follows from the
elementary `g(χ)g(χ̄) = χ(−1)p` at `χ = χ̄ = χ₂'`: `g_p(χ₂')² = χ₂'(−1)p = −p`. Gauss's sign
determination is **not used**. Left uncorrected this would have inflated the citation exposure that
the `[PROVISIONAL — citation-verifier unavailable]` tag is meant to bound. **Corrected in the
artifact today.**

## F4 — the closure is `[PROVED]` but has never been read by anything but me `[structural]`

No independent eye saw any of it: `citation-verifier` unavailable (the two Hasse–Davenport relations),
`compile-diff` unavailable (`ROADMAP_REDIRECT_v4`). Per CLAUDE.md §2a a self-audit covers the
**mechanical** layer and buys nothing on the **frame** layer. What is genuinely mechanical here and
does hold: the assembly `g(χ₃χ₄)² = θ(2)g(χ̄₃χ₂)g(χ₂) = … = g(χ₃)²` is exact symbol-pushing, each
intermediate is numerically witnessed, and the endpoint `J = ∓p` is exact in `Z[ζ₁₂]` at 31/31 primes.
What is **not** covered: whether the two HD relations are stated with the hypotheses I assumed.

## F5 — a scope word I should not have used in an append-only log `[correction appended]`

The `HANDOFF_LOG` entry for the closure says *"Do NOT look for a sign argument — there isn't one to
find, the sign was never the difficulty."* The second clause is fine; **"there isn't one to find" is
simply wrong** — there *is* a sign argument, it is §2 (the mod-`λ` congruence), and it is the reason
the theorem holds in both regimes. A future reader could take that line as licence to skip §2.
The log is append-only and my block is closed, so this is corrected by a **new appended entry**, not
an edit.

## F6 — `ROADMAP_REDIRECT_v4` §1's header is generous `[minor, corrected]`

"three closed, one re-opened today, one unverified" scores Brick D as closed. **D3 (the
citation/literature sweep) is live inside Brick D** — the sweep is incomplete and the standing rule
("mandatory before any citation-strength grade move") is unchanged, and this session *hit* that rule
twice. Corrected to name D as partly open.

## F7 — the `p ≡ 11 mod 12` half: stated, but worth stating louder `[no change needed]`

The closure covers **only** `p ≡ 7 mod 12`. The sign argument (§2) is regime-independent, but the
rationality half provably does not extend — witnessed as the B/F column failures. It is recorded in
the RESULT (§0, §4, §5), in `RESEARCH.md (e)`, and in the handoff `DO NOT REDO`. **No inflation
found**; flagged only because "Brick D2 CLOSED" is a compressible headline that drops the qualifier,
and I used that headline in conversation.

## F8 — what I did NOT audit `[named uncovered]`

- The **~40 `RESULT_*` files from 08-18 → 09-01** whose statuses I transcribed into `ROADMAP_REDIRECT_v4`
  §1–§2. I read each file's head and grade lines; I did **not** re-verify any of their measurements.
  v4's brick statuses are **transcriptions, not re-certifications**.
- **`POSITIVE_FINDINGS_MASTER_v19`** — D-3 is diagnosed, not repaired. Still owed.
- The **frame** rows already named in `ROADMAP_REDIRECT_v4.md` §5.

---

## Net

Two substantive self-corrections (**F1** overstated staleness, **F2** an inherited unaudited grade),
one citation-exposure reduction (**F3**), two wording corrections (**F5**, **F6**). **The
mathematics of the D2 closure is unaffected by all of them** — F3 strengthens it by removing a
dependency. The claim that most needs an outside eye is not the proof; it is **F2**, the step from
the sign law to the m-law, which rests on a grade I did not check in a file that has already had to
audit itself once.
