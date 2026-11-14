#!/usr/bin/env python3
"""Same-origin Hydro bridge v2: serves the Black UI + runs real Lean 4 kernel checks.

Implements HYDRO_DEV_HANDOFF.md Roadmap #2 & #4 while preserving all 6 invariants:
  - Persistent `lake env lean --server` LSP worker pool keyed by exact `import` header
    (cuts ~4.5s/rung Mathlib import overhead to ~30-150ms/rung on warm hits), with
    automatic fallback to `lake env lean <tempfile>` subprocess execution.
  - Zero CORS headers (strict same-origin topology).
  - Token-aware deny-list blocking `#eval`, `#reduce`, `unsafe`, `IO.`,
    `System.Process`, `initialize`, `implemented_by`, and `@[extern]`.
  - Verbatim `#print axioms` parsing and backtick-aware `sorryAx` detection.
"""

import argparse
import io
import json
import os
import pathlib
import queue
import re
import subprocess
import tempfile
import threading
import time
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer

DEFAULT_UI_DIR = os.environ.get("HYDRO_UI_DIR", "/tmp/hydro_test/f")


def detect_default_lean_cwd() -> str:
    env_cwd = os.environ.get("HYDRO_LEAN_CWD")
    if env_cwd and os.path.isdir(env_cwd):
        return os.path.abspath(env_cwd)
    cwd = os.getcwd()
    if any(
        os.path.isfile(os.path.join(cwd, marker))
        for marker in ("lakefile.lean", "lakefile.toml", "lean-toolchain")
    ):
        return cwd
    for candidate in (
        "/Users/trentpalelei/Desktop/Math Ex/LonelyRunnerFresh",
        "/Users/trentpalelei/Desktop/Math Ex/LonelyRunner",
    ):
        if os.path.isdir(candidate):
            return candidate
    return cwd


UI_DIR = DEFAULT_UI_DIR
LEAN_CWD = detect_default_lean_cwd()

LADDER = [
    "omega",
    "linarith",
    "ring",
    "norm_num",
    "simp",
    "nlinarith",
    "aesop",
]

# Token-aware deny-list: blocks metaprogramming/IO escape hatches without false
# positives on mathematical identifiers like `theorem initialize_cell`.
DENY_PATTERNS = [
    (re.compile(r"(?:^|\s)#eval\b", re.MULTILINE), "#eval"),
    (re.compile(r"(?:^|\s)#reduce\b", re.MULTILINE), "#reduce"),
    (re.compile(r"\bunsafe\b"), "unsafe"),
    (re.compile(r"\bIO\."), "IO."),
    (re.compile(r"\bSystem\.Process\b"), "System.Process"),
    (re.compile(r"(?:^|\n)\s*initialize\b"), "initialize"),
    (re.compile(r"\bimplemented_by\b"), "implemented_by"),
    (re.compile(r"@\[[^\]]*\bextern\b[^\]]*\]"), "@[extern]"),
]


def build_elan_env() -> dict:
    """Ensures ~/.elan/bin is present on PATH even under `python3 -I` or agent shells."""
    env = os.environ.copy()
    elan_bin = os.path.expanduser("~/.elan/bin")
    cur_path = env.get("PATH", "")
    if os.path.isdir(elan_bin) and elan_bin not in cur_path.split(os.pathsep):
        env["PATH"] = elan_bin + os.pathsep + cur_path
    return env


def strip_lean_comments(code: str) -> str:
    """Strips non-nested block comments and line comments prior to deny-list scan."""
    no_block = re.sub(r"/-.*?-/", " ", code, flags=re.DOTALL)
    return re.sub(r"--.*$", " ", no_block, flags=re.MULTILINE)


def check_deny_list(code: str):
    """Returns forbidden construct label if matched, else None."""
    scrubbed = strip_lean_comments(code)
    for pattern, label in DENY_PATTERNS:
        if pattern.search(scrubbed):
            return label
    return None


def split_import_header(code: str):
    """Splits Lean source into `(import_key_tuple, prefix_lines, body_lines)`.

    Preserves exact user imports so warm LSP slots never add or hide imports.
    """
    lines = code.splitlines()
    imports = []
    last_import_idx = -1
    in_block_comment = False

    for idx, raw in enumerate(lines):
        s = raw.strip()
        if in_block_comment:
            if "-/" in s:
                in_block_comment = False
            continue
        if s.startswith("/-") and "-/" not in s[2:]:
            in_block_comment = True
            continue
        if not s or s.startswith("--") or (s.startswith("/-") and s.endswith("-/")):
            continue
        if s.startswith("import "):
            imports.append(re.sub(r"\s+", " ", s))
            last_import_idx = idx
        else:
            break

    if last_import_idx >= 0:
        return tuple(imports), lines[: last_import_idx + 1], lines[last_import_idx + 1 :]
    return (), [], lines


def parse_axioms_from_text(text: str) -> list:
    """Parses `#print axioms` kernel output verbatim; never fabricates axiom lists."""
    axioms = []
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        ax_list = [a.strip() for a in m.group(2).split(",") if a.strip()]
        axioms.append({"decl": m.group(1), "axioms": ax_list})
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", text):
        axioms.append({"decl": m.group(1), "axioms": []})
    return axioms


def detect_sorry_in_output(text: str) -> bool:
    """Detects `sorryAx` and Lean v4.29+ backtick/quote `sorry` warnings."""
    return "sorryAx" in text or bool(
        re.search(r"declaration uses [`']sorry[`']", text)
    )


def replace_first_sorry_tactic(code: str, tactic: str) -> str:
    """Replaces `:= by sorry` (including multiline `:= by\\n  sorry`) with `tactic`."""
    variant, count = re.subn(
        r"(:=\s*by\s+)sorry\b",
        lambda m: m.group(1) + tactic,
        code,
        count=1,
    )
    return variant if count > 0 else code


# =============================================================================
# PERSISTENT `lake env lean --server` LSP WORKER POOL (ROADMAP #2)
# =============================================================================
class PersistentLeanLspServer:
    """Amortizes Mathlib/project `.olean` imports across `/verify` and `/tactics`."""

    def __init__(self, lean_cwd: str, max_warm_slots: int = 4):
        self.lean_cwd = lean_cwd
        self.max_warm_slots = max_warm_slots
        self.lock = threading.Lock()
        self.proc = None
        self.msg_queue = queue.Queue()
        self.reader_thread = None
        self.req_id = 10
        # import_tuple -> {"uri": str, "version": int, "last_used": float}
        self.open_docs = {}
        self.slot_seq = 0

    def _start_locked(self) -> bool:
        if self.proc is not None and self.proc.poll() is None:
            return True
        self._shutdown_locked()
        try:
            self.proc = subprocess.Popen(
                ["lake", "env", "lean", "--server"],
                cwd=self.lean_cwd,
                env=build_elan_env(),
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.DEVNULL,
                bufsize=0,
            )
        except Exception:
            self.proc = None
            return False

        self.msg_queue = queue.Queue()
        self.open_docs.clear()
        buffered_out = io.BufferedReader(self.proc.stdout, buffer_size=65536)
        self.reader_thread = threading.Thread(
            target=self._stdout_reader_loop, args=(buffered_out,), daemon=True
        )
        self.reader_thread.start()

        root_uri = pathlib.Path(self.lean_cwd).resolve().as_uri()
        self._send_rpc_locked({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {
                "processId": os.getpid(),
                "rootUri": root_uri,
                "capabilities": {},
            },
        })

        init_ok = False
        deadline = time.time() + 15.0
        while time.time() < deadline:
            try:
                msg = self.msg_queue.get(timeout=0.5)
            except queue.Empty:
                if self.proc.poll() is not None:
                    break
                continue
            if msg.get("id") == 1:
                init_ok = True
                break

        if not init_ok:
            self._shutdown_locked()
            return False

        self._send_rpc_locked({"jsonrpc": "2.0", "method": "initialized", "params": {}})
        return True

    def _shutdown_locked(self):
        if self.proc is not None:
            try:
                self.proc.kill()
                self.proc.wait(timeout=2.0)
            except Exception:
                pass
        self.proc = None
        self.open_docs.clear()

    def _stdout_reader_loop(self, stream):
        try:
            while True:
                headers = {}
                while True:
                    line = stream.readline()
                    if not line:
                        return
                    s = line.decode("utf-8", errors="replace").strip()
                    if not s:
                        break
                    if ":" in s:
                        k, v = s.split(":", 1)
                        headers[k.strip().lower()] = v.strip()
                length = int(headers.get("content-length", "0"))
                if length <= 0:
                    continue
                chunks = []
                rem = length
                while rem > 0:
                    blk = stream.read(rem)
                    if not blk:
                        return
                    chunks.append(blk)
                    rem -= len(blk)
                raw_json = b"".join(chunks).decode("utf-8", errors="replace")
                try:
                    self.msg_queue.put(json.loads(raw_json))
                except json.JSONDecodeError:
                    continue
        except Exception:
            return

    def _send_rpc_locked(self, obj: dict):
        body = json.dumps(obj).encode("utf-8")
        header = f"Content-Length: {len(body)}\r\n\r\n".encode("ascii")
        self.proc.stdin.write(header + body)
        self.proc.stdin.flush()

    def prewarm_default_imports(self):
        """Warms `import Mathlib.Tactic` once in the background at server boot."""
        try:
            self.elaborate("import Mathlib.Tactic\ntheorem _warm : 1 = 1 := rfl\n", 90.0)
        except Exception:
            pass

    def elaborate(self, code: str, timeout_sec: float = 60.0) -> dict:
        with self.lock:
            if not self._start_locked():
                raise RuntimeError("Lean LSP server unavailable")

            while not self.msg_queue.empty():
                try:
                    self.msg_queue.get_nowait()
                except queue.Empty:
                    break

            imp_key, prefix_lines, body_lines = split_import_header(code)
            slot = self.open_docs.get(imp_key)
            next_ver = 1 if slot is None else (slot["version"] + 1)

            # Inject an alternating-column `#check Prop` sentinel immediately after the
            # unchanged `import` block. Because its column toggles 0 <-> 1 on every
            # version, Lean's FileWorker is guaranteed to invalidate old declarations
            # below imports AND emit a fresh `publishDiagnostics` packet for `next_ver`.
            pad = " " if (next_ver % 2 == 0) else ""
            sentinel_line = f"{pad}#check Prop -- _hydro_sync_{next_ver}"
            sync_line_1based = len(prefix_lines) + 1
            instrumented_code = "\n".join(prefix_lines + [sentinel_line] + body_lines) + "\n"

            if slot is None:
                if len(self.open_docs) >= self.max_warm_slots:
                    oldest_k = min(
                        self.open_docs, key=lambda k: self.open_docs[k]["last_used"]
                    )
                    old_slot = self.open_docs.pop(oldest_k)
                    self._send_rpc_locked({
                        "jsonrpc": "2.0",
                        "method": "textDocument/didClose",
                        "params": {"textDocument": {"uri": old_slot["uri"]}},
                    })

                self.slot_seq += 1
                virt_path = pathlib.Path(
                    self.lean_cwd, f"_HydroWarmSlot_{self.slot_seq}.lean"
                ).resolve()
                uri = virt_path.as_uri()
                self.open_docs[imp_key] = {
                    "uri": uri,
                    "version": 1,
                    "last_used": time.time(),
                }
                self._send_rpc_locked({
                    "jsonrpc": "2.0",
                    "method": "textDocument/didOpen",
                    "params": {
                        "textDocument": {
                            "uri": uri,
                            "languageId": "lean4",
                            "version": 1,
                            "text": instrumented_code,
                        }
                    },
                })
            else:
                uri = slot["uri"]
                slot["version"] = next_ver
                slot["last_used"] = time.time()
                self._send_rpc_locked({
                    "jsonrpc": "2.0",
                    "method": "textDocument/didChange",
                    "params": {
                        "textDocument": {"uri": uri, "version": next_ver},
                        "contentChanges": [{"text": instrumented_code}],
                    },
                })

            raw_diags = []
            got_diags = False
            progress_done = False
            barrier_id = None
            deadline = time.time() + timeout_sec

            while time.time() < deadline:
                if self.proc.poll() is not None:
                    self._shutdown_locked()
                    raise RuntimeError("lean --server terminated unexpectedly")
                try:
                    msg = self.msg_queue.get(timeout=0.4)
                except queue.Empty:
                    continue

                method = msg.get("method")
                params = msg.get("params") or {}

                if method == "textDocument/publishDiagnostics":
                    if params.get("uri") == uri and params.get("version") == next_ver:
                        raw_diags = params.get("diagnostics") or []
                        got_diags = True
                        if progress_done and barrier_id is None:
                            break
                elif method == "$/lean/fileProgress":
                    td = params.get("textDocument") or {}
                    if td.get("uri") == uri and td.get("version") == next_ver:
                        if len(params.get("processing") or []) == 0 and not progress_done:
                            progress_done = True
                            self.req_id += 1
                            barrier_id = self.req_id
                            self._send_rpc_locked({
                                "jsonrpc": "2.0",
                                "id": barrier_id,
                                "method": "textDocument/documentSymbol",
                                "params": {"textDocument": {"uri": uri}},
                            })
                elif barrier_id is not None and msg.get("id") == barrier_id:
                    if got_diags:
                        break
                    # Wait briefly if publishDiagnostics is queued right behind barrier
                    barrier_id = -1

                if barrier_id == -1 and got_diags:
                    break

            if not progress_done:
                self._shutdown_locked()
                raise TimeoutError(f"timeout {int(timeout_sec)}s")

            errors, warnings, info_msgs = [], [], []
            for d in raw_diags:
                rng = (d.get("range") or {}).get("start") or {}
                ln_1based = rng.get("line", 0) + 1
                col = rng.get("character", 0)
                msg_txt = (d.get("message") or "").strip()

                # Filter out our injected `#check Prop` sentinel diagnostic
                if ln_1based == sync_line_1based and msg_txt.startswith("Prop : Type"):
                    continue
                adj_line = ln_1based - 1 if ln_1based > sync_line_1based else ln_1based

                sev = d.get("severity", 3)
                if sev == 1:
                    errors.append(f"{adj_line}:{col}: error: {msg_txt}")
                elif sev == 2:
                    warnings.append(f"{adj_line}:{col}: warning: {msg_txt}")
                else:
                    info_msgs.append(msg_txt)

            combined_text = "\n".join(errors + warnings + info_msgs)
            axioms = parse_axioms_from_text(combined_text)
            has_sorry = detect_sorry_in_output(combined_text)
            if not has_sorry:
                for ax in axioms:
                    if "sorryAx" in ax["axioms"]:
                        has_sorry = True

            stdout_str = "\n".join(info_msgs)
            stderr_str = "\n".join(warnings + errors)
            success = len(errors) == 0

            return {
                "success": success,
                "verified": success and not has_sorry,
                "return_code": 0 if success else 1,
                "errors": errors,
                "warnings": warnings,
                "axioms": axioms,
                "sorryAx_count": 1 if has_sorry else 0,
                "sorryAx": 1 if has_sorry else 0,
                "raw_stdout": stdout_str,
                "raw_stderr": stderr_str,
                "stdout": stdout_str,
                "stderr": stderr_str,
                "engine": "lsp_warm",
            }


LSP_POOL = None


def run_cli_lean(code: str, timeout_sec: float = 120.0) -> dict:
    """Subprocess `lake env lean <tempfile>` fallback (identical semantics to v1)."""
    with tempfile.NamedTemporaryFile(
        "w", suffix=".lean", delete=False, encoding="utf-8"
    ) as tf:
        tf.write(code)
        tmp = tf.name
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", tmp],
            cwd=LEAN_CWD,
            env=build_elan_env(),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=timeout_sec,
        )
        out = proc.stdout + proc.stderr
        errors = [l for l in out.splitlines() if ": error:" in l]
        warnings = [l for l in out.splitlines() if ": warning:" in l]
        axioms = parse_axioms_from_text(out)
        has_sorry = detect_sorry_in_output(out)
        success = proc.returncode == 0 and not errors
        stderr_combined = proc.stderr if proc.stderr.strip() else "\n".join(warnings + errors)
        return {
            "success": success,
            "verified": success and not has_sorry,
            "return_code": proc.returncode,
            "errors": errors,
            "warnings": warnings,
            "axioms": axioms,
            "sorryAx_count": 1 if has_sorry else 0,
            "sorryAx": 1 if has_sorry else 0,
            "raw_stdout": proc.stdout,
            "raw_stderr": proc.stderr,
            "stdout": proc.stdout,
            "stderr": stderr_combined,
            "engine": "cli_cold",
        }
    finally:
        if os.path.exists(tmp):
            os.remove(tmp)


def check_with_kernel(code: str, timeout_sec: float = 120.0) -> dict:
    if LSP_POOL is not None:
        try:
            return LSP_POOL.elaborate(code, timeout_sec=timeout_sec)
        except TimeoutError as te:
            return {
                "success": False,
                "verified": False,
                "return_code": -1,
                "errors": [str(te)],
                "warnings": [],
                "axioms": [],
                "sorryAx_count": 0,
                "sorryAx": 0,
                "raw_stdout": "",
                "raw_stderr": str(te),
                "stdout": "",
                "stderr": str(te),
                "engine": "lsp_timeout",
            }
        except Exception:
            pass
    return run_cli_lean(code, timeout_sec=timeout_sec)


# =============================================================================
# SAME-ORIGIN HTTP SERVER (ZERO CORS HEADERS BY DESIGN)
# =============================================================================
class Handler(SimpleHTTPRequestHandler):
    def __init__(self, *a, **kw):
        serve_dir = UI_DIR if os.path.isdir(UI_DIR) else os.getcwd()
        super().__init__(*a, directory=serve_dir, **kw)

    def log_message(self, *a):
        pass

    def do_GET(self):
        if self.path == "/health":
            warm_count = len(LSP_POOL.open_docs) if LSP_POOL is not None else 0
            self._json(200, {
                "status": "ok",
                "lean_cwd": LEAN_CWD,
                "warm_import_slots": warm_count,
            })
            return
        if self.path in ("/", "/index.html"):
            self.path = "/black_ui.html"
        super().do_GET()

    def do_POST(self):
        if self.path == "/tactics":
            self.do_tactics()
            return
        self.do_verify()

    def do_tactics(self):
        n = int(self.headers.get("Content-Length", 0))
        try:
            req = json.loads(self.rfile.read(n).decode("utf-8"))
        except Exception as e:
            self._json(400, {"error": f"bad json: {e}"})
            return

        code = req.get("code", "")
        if "sorry" not in code:
            self._json(200, {"found": False, "reason": "no sorry in input"})
            return

        forbidden = check_deny_list(code)
        if forbidden:
            self._json(200, {"found": False, "reason": f"forbidden construct ({forbidden})"})
            return

        custom_ladder = req.get("ladder")
        if isinstance(custom_ladder, list) and all(
            isinstance(t, str) and re.match(r"^[A-Za-z0-9_!.?\s]+$", t)
            for t in custom_ladder
        ):
            ladder = custom_ladder
        else:
            ladder = LADDER

        attempts, winner = [], None
        t0 = time.time()

        for tac in ladder:
            variant = replace_first_sorry_tactic(code, tac)
            if variant == code:
                self._json(
                    200,
                    {"found": False, "reason": "could not locate ':= by sorry' pattern"},
                )
                return
            t_rung = time.time()
            try:
                res = check_with_kernel(variant, timeout_sec=35.0)
                ok = bool(res["verified"])
                rung_ms = round((time.time() - t_rung) * 1000.0, 1)
                el = round((time.time() - t0) * 1000.0, 1)
                attempts.append({
                    "tactic": tac,
                    "ok": ok,
                    "rung_ms": rung_ms,
                    "elapsed_ms": el,
                    "return_code": res["return_code"],
                    "engine": res.get("engine", "unknown"),
                })
                if ok and winner is None:
                    winner = {"tactic": tac, "code": variant, "elapsed_ms": el}
                    break
            except subprocess.TimeoutExpired:
                attempts.append({
                    "tactic": tac,
                    "ok": False,
                    "rung_ms": 35000.0,
                    "elapsed_ms": round((time.time() - t0) * 1000.0, 1),
                    "return_code": -1,
                })

        self._json(200, {
            "found": winner is not None,
            "tactic": winner and winner["tactic"],
            "code": winner and winner["code"],
            "attempts": attempts,
            "total_ms": round((time.time() - t0) * 1000.0, 1),
        })

    def do_verify(self):
        n = int(self.headers.get("Content-Length", 0))
        try:
            req = json.loads(self.rfile.read(n).decode("utf-8"))
        except Exception as e:
            self._json(400, {
                "success": False,
                "verified": False,
                "errors": [f"bad json: {e}"],
                "sorryAx": 0,
                "sorryAx_count": 0,
            })
            return

        code = req.get("code", "")
        forbidden = check_deny_list(code)
        if forbidden:
            err_msg = f"rejected: forbidden construct ({forbidden})"
            self._json(200, {
                "success": False,
                "verified": False,
                "errors": [err_msg],
                "warnings": [],
                "axioms": [],
                "sorryAx": 0,
                "sorryAx_count": 0,
                "raw_stdout": "",
                "raw_stderr": err_msg,
                "stdout": "",
                "stderr": err_msg,
            })
            return

        t0 = time.time()
        try:
            res = check_with_kernel(code, timeout_sec=120.0)
            res["elapsed_ms"] = round((time.time() - t0) * 1000.0, 1)
            self._json(200, res)
        except subprocess.TimeoutExpired:
            self._json(200, {
                "success": False,
                "verified": False,
                "errors": ["timeout 120s"],
                "sorryAx": 0,
                "sorryAx_count": 0,
            })
        except Exception as e:
            self._json(200, {
                "success": False,
                "verified": False,
                "errors": [str(e)],
                "sorryAx": 0,
                "sorryAx_count": 0,
            })

    def _json(self, code_: int, obj: dict):
        b = json.dumps(obj).encode("utf-8")
        self.send_response(code_)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(b)))
        self.end_headers()
        self.wfile.write(b)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Same-Origin Hydro Lean 4 Bridge v2")
    parser.add_argument("--port", type=int, default=8088, help="Port on 127.0.0.1")
    parser.add_argument("--cwd", default=None, help="Override Lean Lake project root")
    parser.add_argument("--ui-dir", default=DEFAULT_UI_DIR, help="Static UI directory")
    parser.add_argument("--no-lsp", action="store_true", help="Force cold CLI mode")
    parser.add_argument("--no-prewarm", action="store_true", help="Skip boot prewarm")
    args = parser.parse_args()

    if args.cwd:
        LEAN_CWD = os.path.abspath(args.cwd)
    UI_DIR = args.ui_dir

    if not args.no_lsp:
        LSP_POOL = PersistentLeanLspServer(LEAN_CWD)
        if not args.no_prewarm:
            threading.Thread(
                target=LSP_POOL.prewarm_default_imports, daemon=True
            ).start()

    ThreadingHTTPServer(("127.0.0.1", args.port), Handler).serve_forever()