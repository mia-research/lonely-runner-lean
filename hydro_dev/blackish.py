#!/usr/bin/env python3
"""Blackish v2 — headless Lean 4 verification service for agent delegation.

Endpoints (JSON):
  GET  /          -> serves the bundled UI (same-origin; no CORS by design)
  GET  /health    -> identity + toolchain info
  POST /verify    {code}                        -> real `lake env lean` verdict
  POST /tactics   {code}  (one sorry)           -> deterministic tactic ladder

Architecture invariants (see HYDRO_DEV_HANDOFF.md):
  1. Only this service's verdict may render "verified".
  2. Fail closed: no bridge -> "Not Verified", never fabricated.
  3. Axioms parsed from kernel output, never asserted.
  4. Deny-list eval/unsafe/IO constructs.
  5. Same-origin topology; no CORS headers.
  6. Run the four-control gauntlet after any change.

Concurrency: a bounded worker pool (BLACKISH_WORKERS, default 3) gates the
compile section. Each in-flight elaboration is CPU-bound and imports Mathlib
(~1-2 GB RSS), so the pool is the whole machine's safety valve — any number of
subagents may connect; excess requests queue FIFO.
"""
import os
import re
import json
import time
import tempfile
import subprocess
import threading
from http.server import ThreadingHTTPServer, SimpleHTTPRequestHandler

# --- configuration -----------------------------------------------------------
PORT = int(os.environ.get("BLACKISH_PORT", "8088"))
WORKERS = int(os.environ.get("BLACKISH_WORKERS", "3"))
MAX_BODY = 1_048_576  # 1 MB
UI_DIR = os.environ.get("BLACKISH_UI_DIR", os.path.dirname(os.path.abspath(__file__)))
LEAN_CWD = os.environ.get(
    "BLACKISH_REPO", "/Users/trentpalelei/Desktop/Math Ex/LonelyRunner"
)
VERSION = "2.0.0"

DENY = ("#eval", "unsafe", "IO.", "initialize", "implemented_by", "@[extern]")
LADDER = ["omega", "linarith", "ring", "norm_num", "simp", "nlinarith", "aesop"]

# --- Lean subprocess guard ---------------------------------------------------
_POOL = threading.BoundedSemaphore(WORKERS)


def run_lean(code, timeout=120):
    """Compile `code` under the repo toolchain. Returns the full verdict dict."""
    if len(code) > MAX_BODY:
        return {"success": False, "verified": False,
                "errors": ["rejected: code exceeds %d bytes" % MAX_BODY], "sorryAx_count": 0}
    if any(tok in code for tok in DENY):
        return {"success": False, "verified": False,
                "errors": ["rejected: forbidden construct (eval/unsafe/IO)"], "sorryAx_count": 0}
    t0 = time.time()
    fd, tmp = tempfile.mkstemp(suffix=".lean")
    try:
        with os.fdopen(fd, "w") as tf:
            tf.write(code)
        with _POOL:
            proc = subprocess.run(
                ["lake", "env", "lean", tmp], cwd=LEAN_CWD,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=timeout,
            )
        out = proc.stdout + proc.stderr
        errors = [l for l in out.splitlines() if ": error:" in l]
        warnings = [l for l in out.splitlines() if ": warning:" in l]
        profiles, flat = [], []
        for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out):
            names = [a.strip() for a in m.group(2).split(",") if a.strip()]
            profiles.append({"decl": m.group(1), "axioms": names})
            for a in names:
                if a not in flat:
                    flat.append(a)
        has_sorry = "sorryAx" in out or bool(re.search(r"declaration uses .sorry", out))
        return {
            "success": proc.returncode == 0 and not errors,
            "verified": proc.returncode == 0 and not errors and not has_sorry,
            "elapsed_ms": round((time.time() - t0) * 1000, 1),
            "return_code": proc.returncode,
            "errors": errors, "warnings": warnings,
            "axioms": flat, "axiom_profiles": profiles,
            "sorryAx_count": 1 if has_sorry else 0,
            "raw_stdout": proc.stdout, "raw_stderr": proc.stderr,
        }
    except subprocess.TimeoutExpired:
        return {"success": False, "verified": False,
                "errors": ["timeout %ds" % timeout], "sorryAx_count": 0}
    except Exception as e:
        return {"success": False, "verified": False, "errors": [str(e)], "sorryAx_count": 0}
    finally:
        if os.path.exists(tmp):
            os.remove(tmp)


class Handler(SimpleHTTPRequestHandler):
    def __init__(self, *a, **kw):
        super().__init__(*a, directory=UI_DIR, **kw)

    def log_message(self, *a):
        pass

    def do_GET(self):
        if self.path in ("/", "/index.html"):
            self.path = "/black_ui.html"
        elif self.path == "/health":
            body = json.dumps({
                "service": "blackish", "version": VERSION,
                "repo": LEAN_CWD, "workers": WORKERS,
                "endpoints": ["/verify", "/tactics", "/health"],
            }).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
        super().do_GET()

    def do_POST(self):
        n = int(self.headers.get("Content-Length", 0))
        if n > MAX_BODY + 1024:
            self._json(413, {"success": False, "verified": False,
                             "errors": ["request too large"], "sorryAx_count": 0})
            return
        try:
            req = json.loads(self.rfile.read(n).decode("utf-8"))
        except Exception as e:
            self._json(400, {"success": False, "verified": False,
                             "errors": ["bad json: %s" % e], "sorryAx_count": 0})
            return
        code = req.get("code", "")
        if self.path == "/tactics":
            self._json(200, self._tactics(code))
        else:
            self._json(200, run_lean(code))

    def _tactics(self, code):
        if "sorry" not in code:
            return {"found": False, "reason": "no sorry in input"}
        if any(tok in code for tok in DENY):
            return {"found": False, "reason": "forbidden construct"}
        attempts, winner = [], None
        t0 = time.time()
        for tac in LADDER:
            variant = re.sub(r":=\s*by\s+sorry", ":= by " + tac, code)
            if variant == code:
                return {"found": False,
                        "reason": "could not locate ':= by sorry' pattern"}
            d = run_lean(variant, timeout=90)
            ok = d["success"]
            attempts.append({"tactic": tac, "ok": ok,
                             "elapsed_ms": d["elapsed_ms"],
                             "return_code": d.get("return_code")})
            if ok:
                winner = {"tactic": tac, "code": variant, "elapsed_ms": d["elapsed_ms"]}
                break
        return {"found": winner is not None,
                "tactic": winner and winner["tactic"],
                "code": winner and winner["code"],
                "attempts": attempts,
                "total_ms": round((time.time() - t0) * 1000, 1)}

    def _json(self, code_, obj):
        b = json.dumps(obj).encode()
        self.send_response(code_)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(b)))
        self.end_headers()
        self.wfile.write(b)


if __name__ == "__main__":
    print("[*] Blackish v%s on http://127.0.0.1:%d — repo: %s — workers: %d"
          % (VERSION, PORT, LEAN_CWD, WORKERS), flush=True)
    ThreadingHTTPServer(("127.0.0.1", PORT), Handler).serve_forever()
