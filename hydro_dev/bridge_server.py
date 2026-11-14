#!/usr/bin/env python3
"""Same-origin Hydro bridge: serves the Black UI + runs real `lake env lean` on POST.
No CORS headers (same-origin only, per hardening spec). Deny-lists eval/unsafe/IO."""
import os, re, json, time, tempfile, subprocess
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler, SimpleHTTPRequestHandler

UI_DIR = "/tmp/hydro_test/f"
LEAN_CWD = "/Users/trentpalelei/Desktop/Math Ex/LonelyRunner"
DENY = ("#eval", "unsafe", "IO.", "initialize", "implemented_by", "@[extern]")

class Handler(SimpleHTTPRequestHandler):
    def __init__(self, *a, **kw):
        super().__init__(*a, directory=UI_DIR, **kw)
    def log_message(self, *a): pass
    def do_GET(self):
        if self.path in ("/", "/index.html"):
            self.path = "/black_ui.html"
        super().do_GET()
    def do_POST(self):
        if self.path == "/tactics":
            self.do_tactics(); return
        self.do_verify()

    def do_tactics(self):
        n = int(self.headers.get("Content-Length", 0))
        try:
            req = json.loads(self.rfile.read(n).decode("utf-8"))
        except Exception as e:
            self._json(400, {"error": f"bad json: {e}"}); return
        code = req.get("code", "")
        if "sorry" not in code:
            self._json(200, {"found": False, "reason": "no sorry in input"}); return
        if any(tok in code for tok in DENY):
            self._json(200, {"found": False, "reason": "forbidden construct"}); return
        LADDER = ["omega", "linarith", "ring", "norm_num", "simp", "nlinarith", "aesop"]
        attempts, winner = [], None
        t0 = time.time()
        for tac in LADDER:
            variant = re.sub(r":=\s*by\s+sorry", ":= by " + tac, code)
            if variant == code:
                self._json(200, {"found": False, "reason": "could not locate ':= by sorry' pattern"}); return
            with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as tf:
                tf.write(variant); tmp = tf.name
            try:
                proc = subprocess.run(["lake", "env", "lean", tmp], cwd=LEAN_CWD,
                                      stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=90)
                out = proc.stdout + proc.stderr
                ok = proc.returncode == 0 and ": error:" not in out
                el = round((time.time() - t0) * 1000, 1)
                attempts.append({"tactic": tac, "ok": ok, "elapsed_ms": el, "return_code": proc.returncode})
                if ok and winner is None:
                    winner = {"tactic": tac, "code": variant, "elapsed_ms": el}
                    break
            except subprocess.TimeoutExpired:
                attempts.append({"tactic": tac, "ok": False, "elapsed_ms": 90000, "return_code": -1})
            finally:
                os.path.exists(tmp) and os.remove(tmp)
        self._json(200, {"found": winner is not None, "tactic": winner and winner["tactic"],
                         "code": winner and winner["code"], "attempts": attempts,
                         "total_ms": round((time.time() - t0) * 1000, 1)})

    def do_verify(self):

        n = int(self.headers.get("Content-Length", 0))
        try:
            req = json.loads(self.rfile.read(n).decode("utf-8"))
        except Exception as e:
            self._json(400, {"success": False, "verified": False, "errors": [f"bad json: {e}"], "sorryAx": 0}); return
        code = req.get("code", "")
        if any(tok in code for tok in DENY):
            self._json(200, {"success": False, "verified": False,
                "errors": ["rejected: forbidden construct (eval/unsafe/IO)"], "sorryAx": 0}); return
        t0 = time.time()
        with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as tf:
            tf.write(code); tmp = tf.name
        try:
            proc = subprocess.run(["lake", "env", "lean", tmp], cwd=LEAN_CWD,
                                  stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=120)
            out = proc.stdout + proc.stderr
            errors = [l for l in out.splitlines() if ": error:" in l]
            warnings = [l for l in out.splitlines() if ": warning:" in l]
            import re
            profiles = []
            flat = []
            for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out):
                names = [a.strip() for a in m.group(2).split(",") if a.strip()]
                profiles.append({"decl": m.group(1), "axioms": names})
                for a in names:
                    if a not in flat:
                        flat.append(a)
            axioms = flat  # UI schema: flat string pills; per-decl detail in axiom_profiles
            has_sorry = "sorryAx" in out or bool(re.search(r"declaration uses .sorry", out))
            self._json(200, {
                "success": proc.returncode == 0 and not errors,
                "verified": proc.returncode == 0 and not errors and not has_sorry,
                "elapsed_ms": round((time.time()-t0)*1000, 1),
                "return_code": proc.returncode,
                "errors": errors, "warnings": warnings, "axioms": axioms, "axiom_profiles": profiles,
                "sorryAx_count": 1 if has_sorry else 0,
                "raw_stdout": proc.stdout, "raw_stderr": proc.stderr})
        except subprocess.TimeoutExpired:
            self._json(200, {"success": False, "verified": False, "errors": ["timeout 120s"], "sorryAx": 0})
        except Exception as e:
            self._json(200, {"success": False, "verified": False, "errors": [str(e)], "sorryAx": 0})
        finally:
            os.path.exists(tmp) and os.remove(tmp)
    def _json(self, code_, obj):
        b = json.dumps(obj).encode()
        self.send_response(code_); self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(b))); self.end_headers(); self.wfile.write(b)

if __name__ == "__main__":
    ThreadingHTTPServer(("127.0.0.1", 8088), Handler).serve_forever()
