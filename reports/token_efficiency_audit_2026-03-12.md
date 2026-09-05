# Token Efficiency Audit — Math Ex Project
**Date:** 2026-03-12
**Prepared by:** Claude

---

## 1. Hard Numbers

| Metric | Value |
|---|---|
| Total sessions | 71 |
| Total session data | ~96 MB |
| Estimated total tokens consumed | ~25 million |
| Largest single session | 9.4 MB (~2.3M chars) |
| Sessions > 3 MB | 8 |
| Sessions > 1 MB | ~20 |
| v5 draft files created | 17 (from 36KB → 88KB each) |

---

## 2. Root Causes — What Actually Burned Tokens

### Problem A: The "Paste the Proof" Pattern (PRIMARY CAUSE)
The v5 draft grew from 36KB to 88KB through 17 iterations. Each iteration most likely involved:
1. Reading the full draft (~600–900 lines of LaTeX math) into context
2. Generating the next version inline in conversation
3. Writing the full new draft back

At 88KB per file that's ~22K tokens **per read**, and each session that touched the proof was burning 2× that (read + generate). Over 17 drafts that's **750K+ tokens on the v5 file alone**.

### Problem B: Missing Anchor Files
MEMORY.md references `sessions_archive.md` and `lrc_proof_status.md` as the primary context files — **but neither exists on disk**. Without these, every session has to reconstruct state from scratch by loading MEMORY.md + reading proof files, inflating startup cost every session.

### Problem C: No Section-Level Work Protocol
When fixing or extending one section of a proof, the entire file was being read. A 682-line preprint has ~15 sections. Working on §13 shouldn't require loading §§1–12.

### Problem D: In-Chat Proof Generation
Long proof arguments were generated as chat responses rather than written directly to files. Chat responses live in context forever; file writes are free after the turn.

### Problem E: Companion Proofs Not Isolated Enough
The companion proof files (lrc_b3b_transparency_v1.md, lrc_crt_incompatibility_v1.md, etc.) are good — but they were folded back into the monolithic v6 preprint, meaning the big file keeps growing and must be loaded whole.

---

## 3. What Is Working

- **Formalization pipeline** (JSON votes, SHA-256, quorum) — clean and file-based
- **Companion proof files** — correct pattern, should be extended
- **MEMORY.md token rules** — rules are correct, execution didn't follow them
- **v6 → v6.1 transition** — correctly created a new file rather than mutating v6

---

## 4. Recommended Protocol Going Forward

### 4a. Create Missing Anchor Files (do this NOW)
Create `lrc_proof_status.md` and `session_state.md` so each session starts with a 1-file read instead of loading proof bodies.

`session_state.md` (max 30 lines) contains:
- Current canonical file
- Section currently being worked on
- Exact next 3 tasks with file/line targets
- Blockers

### 4b. Section-Level Reads — Use Offset/Limit
Instead of `Read(lrc_proof_v6_1_preprint.md)` (682 lines = ~17K tokens):
- Read: `Read(file, offset=320, limit=80)` for §13 only

### 4c. Edit Tool Over Write Tool
`Edit` sends only the diff. `Write` sends the entire file. For a 55KB file, Edit saves ~13K tokens per change.

### 4d. No More Inline Proof Generation
All proof work goes: Read section → Write to file → Done. Never paste a full proof section into chat.

### 4e. Archive Old Drafts
Move v5_1 through v5_16 to `/archive/v5_drafts/`. They're noise in the directory and cause sessions to scan or accidentally load them.

### 4f. Session Kickoff Protocol (strict)
Every session starts with exactly:
1. `Read session_state.md` (30 lines max)
2. `Read <target section only>` (50–80 lines max)
3. Work. Write output to file.

Never start a session by reading the full proof.

---

## 5. V6 vs V6.1 Delta

| | v6_preprint.md | v6_1_preprint.md |
|---|---|---|
| Size | 49KB (647 lines) | 55KB (682 lines) |
| Added | ~35 lines | hardened lemmas GG-TRANS, PL-KBIJ |
| Status | Superseded | Current canonical |

v6.1 is the current file. v6 should be archived.

---

## 6. Immediate Action Items

1. **Create `session_state.md`** — 30-line current-state file
2. **Create `lrc_proof_status.md`** — section-by-section proof status table
3. **Archive** v5_1..v5_16 and v6_preprint.md
4. **Next session discipline**: 2-file read max at start, all work to files, no inline proof generation
