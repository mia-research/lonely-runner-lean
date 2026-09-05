## Goal
Collapse the three near-duplicate Ollama wrappers (`qwen_subagent.py`, `gemma4_subagent.py`, `deepseek_subagent.py`, ~250 lines each, ~90% identical) into one importable module that you can call like an internal API, while preserving every piece of per-model tuning and keeping existing subprocess callers working unchanged.

## What's already true (no work needed)
Ollama **is** already a local HTTP API at `http://localhost:11434` with `qwen3.5:4b`, `gemma4:26b`, `deepseek-r1:14b`, `nomic-embed-text` loaded. The job is to put a clean Python façade in front of it.

## Files

### 1. `tools/local_llm.py` (NEW — the internal API)
Single module, no third-party deps beyond `requests`. Structure:

```python
# Config
OLLAMA_URL = "http://localhost:11434/api/chat"
STABLE_THRESHOLD, SENSITIVE_THRESHOLD = 1e-9, 1e-6

# Shared base system prompts (the terse "qwen" versions)
BASE_SYSTEM_PROMPTS = {prescreening, verify, math, draft, dedup}

# Per-model prompt overlays for the tasks that differ (verify/math/dedup get
# the "Think carefully / step by step" prefixes gemma4 & deepseek use)
PROMPT_OVERLAYS = {"gemma4": {...}, "deepseek": {...}}

# Registry — per-model tuning becomes DATA, not code
MODELS = {
    "qwen":     {"tag": "qwen3.5:4b",   "max_tokens":1024, "num_ctx":32768, "timeout":180,
                 "presets":{verify,math only}, "handle_404":False},
    "gemma4":   {"tag": "gemma4",       "max_tokens":1024, "num_ctx":32768, "timeout":240,
                 "presets":{prescreening,verify,math,dedup}, "handle_404":True},
    "deepseek": {"tag": "deepseek-r1:14b","max_tokens":1536,"num_ctx":65536, "timeout":360,
                 "presets":{prescreening,verify,math,dedup w/ 131072 ctx for math}, "handle_404":True},
}

# Core
def ask(prompt, model="qwen", task="verify", thinking=False, max_tokens=None,
        temperature=None, num_ctx=None, keep_alive=None, timeout=None) -> dict
#   - resolves model cfg + task presets + prompt overlays
#   - POSTs /api/chat with native `think` param
#   - thinking-budget fallback (rerun think=false if CoT ate the output) — preserved from existing wrappers
#   - HTTP 404 -> "run ollama pull <tag>" when handle_404 (gemma4/deepseek behavior)
#   - returns {verdict, content, thinking_trace, task, model, done_reason, ...}

# Convenience (model-parametrized, mirror old helpers)
def prescreen(text, model="qwen") -> dict
def verify(text, model="qwen", deep=False) -> dict
def dedup(a, b, model="qwen", deep=False) -> dict
def math(problem, model="qwen", deep=False) -> dict
def draft(instructions, model="qwen") -> dict

# Ops helpers (new, useful for an "internal API")
def list_models() -> list[str]            # keys of MODELS
def health() -> dict                       # pings /api/tags, reports which configured models are loaded

# CLI (same flags as today, plus --model/-M choosing qwen|gemma4|deepseek)
def main(default_model="qwen"): ...
```

Design notes:
- **Native `/api/chat` only** (skill says it's more reliable than OpenAI-compat for `think` control). No `/v1` endpoint.
- **Exact model tags preserved** (`qwen3.5:4b`, bare `gemma4`, `deepseek-r1:14b`) so resolution behavior is identical.
- `nomic-embed-text` intentionally excluded (embedding model, not chat). An `embed()` helper can be added later if wanted.
- Default model = `qwen` (cheapest; matches existing default-task routing).

### 2. `tools/__init__.py` (NEW, empty)
Makes `from tools.local_llm import ask` work from repo root. Safe here because all existing usage is subprocess-based (no script depends on `tools/` *not* being a package).

### 3. Shims — rewrite the 3 wrappers to ~20 lines each
Each keeps its **exact CLI contract** (same flags, same stdout/stderr behavior) so `prescreen_qwen.py` and `qwen_lrc_monitor.py`'s subprocess calls are untouched. Each shim:
- forces its model, re-parses the legacy args, forwards to `local_llm.ask(...)`, prints exactly as before.

```python
# tools/qwen_subagent.py (skeleton — gemma4/deepseek identical modulo model name + thinking-trace echo)
import sys, os, json, argparse
sys.path.insert(0, os.path.dirname(__file__))
import local_llm

def main():
    p = argparse.ArgumentParser()
    p.add_argument("prompt", nargs="?")
    p.add_argument("--task","-t", default="verify")
    p.add_argument("--thinking","-T", action="store_true")
    p.add_argument("--max-tokens","-m", type=int, default=None)
    p.add_argument("--model", default="qwen3.5:4b")   # accepted for back-compat, mapped
    p.add_argument("--num-ctx", type=int, default=None)
    p.add_argument("--keep-alive", default=None)
    p.add_argument("--timeout", type=int, default=None)
    p.add_argument("--json","-j", action="store_true")
    a = p.parse_args()
    prompt = a.prompt if a.prompt is not None else sys.stdin.read().strip()
    # map legacy tag -> registry key, then forward
    r = local_llm.ask(prompt, model="qwen", task=a.task, thinking=a.thinking,
                      max_tokens=a.max_tokens, num_ctx=a.num_ctx,
                      keep_alive=a.keep_alive, timeout=a.timeout)
    ...print exactly as the old wrapper did...
if __name__ == "__main__": main()
```
The gemma4 shim additionally keeps its `--thinking` trace-echo to stderr (the one differentiator). Everything else is `ask()`.

### 4. `CLAUDE.md` §0 update (surgical)
Current text is Claude-Code-oriented and now contradicts reality. New §0 keeps the *spirit* (local models are **advisory**, never verdicts; don't emit fresh `[Qwen] says:` archival checkpoint lines) but reflects ZCode + the unified module:
- Local LLM access is via `tools/local_llm.py` (`ask(prompt, model=..., task=...)`).
- The old per-model scripts are thin shims over it (kept for back-compat with subprocess callers).
- Routing guidance (qwen=fast/cheap, gemma4=medium, deepseek=hard) moves here from the wrapper docstrings.
- The `local-qwen-ollama-subagent` skill remains the workflow doc.
- Existing proof-file / versioning / subagent-routing rules in §1–§2 are **untouched**.

### 5. Smoke test (run, don't write a test file)
- `python3 tools/local_llm.py "Reply with exactly: OK" --model qwen --task prescreening`
- `python3 -c "from tools.local_llm import ask, health; print(health()); print(ask('phi(5)=?', model='qwen', task='math')['content'][:80])"`
- Back-compat: `python3 tools/qwen_subagent.py "Reply with exactly: OK" --task prescreening` (proves the shim path the real callers use).
- Repeat the qwen smoke with `--model gemma4` and `--model deepseek`.

## What does NOT change
- `reports/lrc_n11_verification/scripts/prescreen_qwen.py` and `qwen_lrc_monitor.py` — untouched (shims preserve their subprocess contract; the monitor talks to Ollama directly anyway).
- `tools/codex_subagent.py` — left alone (it's an OpenAI Codex CLI wrapper, not Ollama; out of scope for this pass).
- All proof/paper/memory files, §1–§2 of CLAUDE.md.

## Risk / reversibility
- Shims are backward-compatible by construction; if a shim misbehaves, the old wrapper can be restored from git (`git checkout -- tools/qwen_subagent.py`).
- No external calls, no pushes, no destructive ops. All changes are local files + one smoke test against the already-running Ollama.