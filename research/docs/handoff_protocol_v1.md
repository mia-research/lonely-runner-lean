# Handoff protocol — proposed CLAUDE.md §12 (draft v1, 2026-08-05)

Draft for review. **Not yet folded into `CLAUDE.md`** — that file currently
carries 83 uncommitted lines from the other account, and mixing edits is the
exact hazard this protocol exists to prevent. Fold in only when the working
tree is clean.

---

## What is actually broken

Measured on 2026-08-05, not assumed:

| layer | shared between accounts? | evidence |
|---|---|---|
| `CLAUDE.md` | **yes** — one file, in-repo | tracked in git, read by both |
| `memory/` (MEMORY.md, indexes, `feedback_*`) | **yes** — one dir on disk | read session 34's index entry 35 min after it was written |
| `.claude/agents/` (the four gates) | **yes** — one dir on disk | present, but **untracked** |
| session transcript | **no** — per-account, cloud | — |
| *which artifacts are finished* | **recorded nowhere** | — |

So there is no sync problem. There is a **ledger** problem, and it predates the
second account — it is equally true between two sessions of the *same* account.

Three failures trace to it, all documented:

1. **Half-landed supersession** (2026-08-03). A memory declared it superseded a
   phrase; the phrase survived in two indexes and in the superseded file's own
   section header. Same disk, same account, one edit pass that stopped.
2. **Session death without summary** (2026-08-05). An account exhausted its
   tokens mid-block. Everything it concluded is in the index; nothing says what
   it left half-written.
3. **Frontier loss on consolidation** — H3 → H4 → master took live frontiers
   5 → 0 (`DEGRADATION_AUDIT_H3_TO_MASTER_v1.md`). Tag-count audits could not
   see it.

## The protocol

### 12.1 The handoff log

`HANDOFF_LOG.md` at repo root. Append-only, entry format defined in the file.
Read the **last three entries** before doing anything else in a session.

Two properties are load-bearing, and the protocol fails if either is dropped:

- **Append-only.** Failure 1 above happened *during a rewrite of a shared
  index*. An entry cannot be lost to a merge or an overwrite if it is never
  rewritten. Corollary: this file is **exempt from the §1 versioning rule** —
  never create `HANDOFF_LOG_v2.md`.
- **Header written before the work, not after.** Failure 2 above cannot be
  fixed by a diligent end-of-session summary, because the session never reaches
  its end. An entry left `STATUS: OPEN` *is* the handoff: it tells the next
  session that this block died mid-flight and its `IN FLIGHT` line is
  unverified.

Fields name objects, never judgments (§2b). `IN FLIGHT: MASTER_v5.md — §7 panel
unwritten` is an entry; `IN FLIGHT: master needs polish` is not.

### 12.2 Supersession is not done until the grep is clean

When a memory, section, or document supersedes another, the supersession is
**not complete** until:

```bash
grep -rn "<the superseded phrase>" . ~/.claude/projects/*/memory/
```

returns only the new text and the explicit tombstones. Declaring supersession
in the new file is the *claim*; the clean grep is the *artifact*.

This is mechanical and object-level, which is why it works — it counts the
phrase itself, not a proxy for it (§2b). A future session reading a stale index
line has no way to know it was superseded.

### 12.3 The instruction channel must be backed up

`CLAUDE.md` and `.claude/agents/` define every mandatory gate in §2. Both
currently exist only on this disk — `CLAUDE.md` with 83 uncommitted lines,
`.claude/agents/` untracked entirely. If the disk fails, both accounts lose the
gates and neither would immediately notice.

**Rule:** a change to `CLAUDE.md` or `.claude/agents/` is committed in the same
work block that makes it. These are not research artifacts; the §1 "never
overwrite a versioned paper" caution does not apply, and there is no reason to
let them sit.

### 12.4 What does *not* need building

Recorded so it is not re-litigated:

- **No MCP for this.** Registry search on memory / shared-context / handoff /
  knowledge-base / sync returned zero connectors (2026-08-05).
- **No new reviewer agent.** §2b already forbids a general adversarial
  reviewer. The gates that apply here exist:
  - `compile-diff` — **already §2-mandatory** before promoting any
    consolidated/handover/master document. This is the gate for failure 3.
  - `memory-drafter` — **already §2-mandatory** for `feedback_*`/`project_*`
    edits. This is the gate for failure 1.
  - `anthropic-skills:consolidate-memory` — merges duplicates and prunes stale
    index lines. Run it when supersessions have accumulated.
- **No locking.** The accounts alternate rather than run concurrently. If that
  changes, revisit; until then a lock is machinery without a failure to prevent.

### 12.5 Git is the ledger, not a prose summary

`git log` reconstructs state with no transcript and no trust in a summary. The
1,732 untracked entries are the current gap: the btc index points at
`POSITIVE_FINDINGS_MASTER_v5.md`; git has no record it exists.

Two cautions learned the hard way on 2026-08-05:

- **Never blanket `git add -A` in this repo.** It swept the `LonelyRunner`
  submodule gitlink (d041205 → 20d03dc) into an unrelated commit. Stage by
  named path, and check `git rev-parse HEAD:LonelyRunner` before and after.
- **Source is tracked; computed data is not.** Measured: source 34 MB,
  generated datasets 2.9 GB (largest single file 2.2 GB). `.gitignore` now
  enforces the split. Committing the raw backlog would have put 2.9 GB into
  history permanently.
