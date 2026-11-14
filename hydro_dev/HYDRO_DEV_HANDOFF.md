# Hydro Dev Handoff — 2026-11-13

For Vaughan. Everything below was machine-verified on the real toolchain (Lean v4.29.1 / Mathlib, `lake env lean`). Performance stats, endpoint specs, the regression gauntlet, and the complete bug ledger from integration testing. No UI required — this is a headless service; agents (ZCode/Codex) are the primary clients.

---

## 1. What exists now

| File | What it is |
|---|---|
| `blackish.py` (v2) | The hardened compiler bridge, renamed. `GET /` serves the UI, `GET /health` identity, `POST /verify` real verdicts, `POST /tactics` the deterministic ladder, bounded worker pool (`BLACKISH_WORKERS`, default 3), 1 MB request cap. Run from repo root. `bridge_server.py` = v1, kept for reference. |
| `one_shot_verifier_v4.py` | One-shot CLI verifier (v4). Fixed the 3 defects in v3 (see ledger #4). |
| `black_ui_original.html` | Your Black UI, unmodified — kept as the reference client. It passed the full honesty gauntlet (see §4). |
| `tactics_benchmark.json` | Raw benchmark data. |

## 2. Endpoints (all JSON)

- `POST /verify` `{code}` → `{success, verified, elapsed_ms, return_code, errors[], warnings[], axioms[], axiom_profiles[], sorryAx_count, raw_stdout, raw_stderr}`
  - `verified` = exit 0 ∧ no errors ∧ no sorryAx. `axioms` is a **flat string array** (Black-UI pill schema, e.g. `["propext","Classical.choice","Quot.sound"]`); `axiom_profiles` carries per-declaration detail. Both parsed from the kernel's actual `#print axioms` output — never asserted.
  - UI compatibility note: the Black UI renders axiom pills from the flat array; objects in that field render as `[object Object]` (schema mismatch found and fixed 2026-11-13 — the UI's own spec §4 was right).
- `POST /tactics` `{code}` (one `sorry`) → deterministic ladder tries `omega → linarith → ring → norm_num → simp → nlinarith → aesop`, first that compiles wins → `{found, tactic, code, attempts[], total_ms}`
- `GET /` serves the UI. **No CORS headers by design** — serve clients from this server (same origin) or they cannot reach it. This is the drive-by-RCE fix: the earlier `Access-Control-Allow-Origin: *` + Lean `#eval` combination let any webpage run shell commands on the host.
- Deny-list on all verification input: `#eval`, `unsafe`, `IO.`, `initialize`, `implemented_by`, `@[extern]`.

Run: `cd <lonely-runner-lean repo> && python3 -I bridge_server.py` (must run from repo root; elan resolves the pinned toolchain from `lean-toolchain`).

## 3. Performance (measured 2026-11-13, M-series Mac, warm Mathlib)

Tactic ladder benchmark: 10 goals in the corpus's arithmetic shapes (ℕ/ℤ/ℝ linear + one nonlinear pair), each with a ground-truth tactic **established by prior compilation**.

- **Hit-rate: 9/9 well-posed goals** (100%). The 10th was an ill-posed goal (benchmark author error — the ladder correctly exhausted; `omega` refusing a false goal is correct behavior).
- Attribution: omega ×5, linarith ×2, nlinarith ×2.
- Latency: ~4.5 s when the first tactic hits (dominated by the ~4 s `import Mathlib.Tactic` per attempt); up to ~50 s when the goal needs `nlinarith` (5 failed attempts before it). Mean 16.4 s/goal.
- Cheap wins on the roadmap: cache one elaboration process (server-side lake session) to amortize imports; parallelize ladder attempts.

Bridge verify latency: ~5.5–14 s per Mathlib-importing file (import-heavy; the theorem itself is milliseconds).

### Concurrency model (measured 2026-11-13, 24 GB / 4 perf cores)

- One `import Mathlib.Tactic` elaboration peaks at **~6 GB RSS** (lean family); a slim-import file (`import Mathlib.Tactic.Linarith`) peaks at **~2 GB**, 5.2 s wall.
- Binding constraint is RAM, not CPU: safe concurrency ≈ (free RAM − headroom) ÷ peak. Defaults: 3 workers on full `Mathlib.Tactic` imports, ~9 with slim imports.
- `blackish.py` (v2) enforces this with a bounded worker pool (`BLACKISH_WORKERS`, default 3). Any number of subagents may connect; excess requests queue FIFO — agents need no coordination.
- One instance per repo/toolchain. Multiple instances of the same repo just split the same RAM — use the queue instead.
- Scaling levers, in order: (1) agents import only what they need; (2) multi-declaration per call (one import serves N theorems); (3) persistent elaboration session (v3); (4) close wllama brain tabs when compiling (each active in-tab brain holds ~1 GB+).

## 4. Regression gauntlet — run ALL FOUR controls after ANY bridge change

```bash
# 1. positive (must be True)
curl -s -X POST localhost:8088 -H 'Content-Type: application/json' \
  -d '{"code":"import Mathlib.Tactic\ntheorem g : 1 + 1 = 2 := by norm_num"}'
# 2. negative (must be False)
curl -s -X POST localhost:8088 -H 'Content-Type: application/json' \
  -d '{"code":"import Mathlib.Tactic\ntheorem bad : 1 + 1 = 3 := by norm_num"}'
# 3. sorry-injection (must be False, sorryAx_count 1)
curl -s -X POST localhost:8088 -H 'Content-Type: application/json' \
  -d '{"code":"import Mathlib.Tactic\ntheorem s : 2 + 2 = 4 := by sorry"}'
# 4. deny-list (must be rejected)
curl -s -X POST localhost:8088 -H 'Content-Type: application/json' \
  -d '{"code":"#eval IO.println \"hi\""}'
```

## 5. Bug ledger (all found by the gauntlet, all fixed)

1. **Hallucinated lemma** `Nat.gcd_div_gcd_div_gcd` — unknown constant. Fixed → `Nat.coprime_div_gcd_div_gcd`.
2. **`Real.norm_eq_abs` rewrite** — pattern not found (expression already used `|…|`). Dropped.
3. **`mul_comm` gap** — `↑g * |X| ≤ bound` vs required `|X| * ↑g ≤ bound`; `exact` cannot close (multiplication not defeq-commutative). Shipped **three times** (doc paste, doc export, one-shot v3) before being fixed by reordering the factorization (`(X) * g`) or appending `mul_comm`. Lesson: run the compiler before announcing "Errors: 0".
4. **Hardcoded axiom claims** — one-shot v3 printed `Axioms Used: [propext, ...]` without reading it. v4 parses the kernel's `#print axioms` line verbatim. Never assert what the kernel didn't say.
5. **sorry backtick bug** — Lean 4.29 prints `` declaration uses `sorry` `` (backticks); a check for `'sorry'` (straight quotes) silently **passed sorry proofs as verified**. Detection must be backtick-aware.
6. **Missing `re` import** — after patch #5, `re.search` raised NameError inside the handler; the generic `except` returned `verified: false` for *everything*. Caught only because the positive control was re-run. Lesson: after any change, run all four controls (§4), not just the one you touched.
7. **CORS `*` on the original bridge** — with Lean `#eval` this is drive-by RCE. Removed; same-origin topology.
8. **HTML demo theater (pre-council builds)** — canned registries + substring dispatch + fake delays; negative controls hard-coded to pass. Superseded by the council build (real wllama brains + real Pyodide + real GitHub loader) and now by this headless bridge.

## 6. Architecture rules (invariant — everything else may change)

1. **Badge ownership**: only the bridge's verdict may render "verified". Brains/UI may only *propose*; proposals are stamped UNVERIFIED until the kernel speaks.
2. **Fail closed**: no bridge ⇒ "Not Verified", never a fabricated response.
3. **`#print axioms` output is the only axiom source.** Parse, never assert.
4. **Deny-list eval/unsafe/IO constructs** in verification input.
5. **Same-origin topology**; no CORS on the bridge.
6. **Run all four controls after any change** (§4).

## 7. Roadmap (in priority order)

1. ~~`/tactics` deterministic ladder~~ ✅ done (§3).
2. Import-cost amortization: persistent elaboration session server-side (would cut ~4 s/attempt to ~ms).
3. `/loop` (LLM proposer tier): sample N candidates from a local model, compile each, return the winner. **Only build if the ladder's hit-rate shows a gap** — currently it doesn't for one-tactic goals. If built: use a native local model (Ollama/Colibri), *not* in-tab WASM (measured 5.6 tok/s vs ~50 tok/s native; in-tab 2048-token context can't fit real Lean files). The browser brains (Qwen 0.5B / Gemma 1B / GLM-Edge 1.5B) are fine for the shareable demo, not for capacity — "GLM-5.3 Edge" is actually GLM-Edge-1.5B-chat.
4. UI niceties if the Black UI is ever revived: render sorry-debt as "🟡 Proof Debt Detected" (the warning exists but isn't an `: error:` line, so it currently renders as "failed without diagnostic text").
5. If citing project artifacts (e.g. "Obligation #4 of the N8 Proof Debt Ledger"), point at things that exist in the repo.
