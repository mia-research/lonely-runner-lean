import json, sys, urllib.request

def post(port, path, body):
    req = urllib.request.Request("http://127.0.0.1:%d%s" % (port, path),
                                 data=json.dumps(body).encode(),
                                 headers={"Content-Type": "application/json"})
    raw = urllib.request.urlopen(req, timeout=180).read()
    return json.loads(raw), len(raw)

IMP = "import Mathlib.Tactic.NormNum\n"
CASES = [
    ("good", IMP + "theorem t : 2 + 2 = 4 := by norm_num", True),
    ("false", IMP + "theorem t (x : Nat) (h : x > 3) : x + 2 = 5 := by norm_num", False),
    ("sorry", IMP + "theorem t : 2 + 2 = 4 := by sorry", False),
    ("deny", "#eval IO.println \"hi\"", False),
    ("axiom_smuggle", IMP + "axiom cheat : False\ntheorem t : 1 = 2 := cheat.elim", False),
    ("native_decide", IMP + "theorem t : 2 + 2 = 4 := by native_decide", False),
    ("namespace_private", IMP + "namespace A.B\nsection\nprivate theorem p : 1 + 1 = 2 := by norm_num\ntheorem q : 2 + 2 = 4 := by norm_num\nend\nend A.B\ntheorem r : 3 = 3 := rfl", True),
    ("no_import", "theorem t : 1 + 1 = 2 := rfl", True),
    ("example_only", IMP + "example : 1 + 1 = 2 := by norm_num", True),
    ("axiom_via_def", IMP + "axiom cheat : False\ndef bad : 1 = 2 := cheat.elim\nexample : 1 = 2 := bad", False),
    ("axiom_in_example", IMP + "axiom cheat : False\nexample : 1 = 2 := cheat.elim", False),
    ("universe_decl", "universe u\ntheorem foo.{v} (a : Type v) : a = a := rfl\ntheorem «odd name» : True := trivial", True),
    ("unused_axiom_decl", IMP + "axiom cheat : False\ntheorem t : 2 + 2 = 4 := by norm_num", False),
    ("no_trailing_newline_comment", IMP + "theorem t : 2 + 2 = 4 := by norm_num -- trailing", True),
]

port = int(sys.argv[1])
bad = 0
for name, code, want in CASES:
    d, n = post(port, "/verify", {"code": code})
    ok = d.get("verified") is want
    bad += not ok
    print("%-28s %s verified=%s want=%s bytes=%d" % (name, "PASS" if ok else "FAIL", d.get("verified"), want, n))
    print("   ", json.dumps(d)[:420])
if len(sys.argv) > 2:
    v2port = int(sys.argv[2])
    print("\n-- same inputs on the v2 bridge (port %d), for comparison --" % v2port)
    for name in ("good", "false", "axiom_smuggle", "native_decide"):
        code = dict((c[0], c[1]) for c in CASES)[name]
        d, n = post(v2port, "/verify", {"code": code})
        print("%-28s verified=%s bytes=%d" % (name, d.get("verified"), n))
    d, n = post(port, "/", {"code": CASES[4][1]})
    print("\nPOST / (full shape) keys:", sorted(d.keys()), "verified=", d["verified"], "bytes=", n)
    d, n = post(port, "/tactics", {"code": IMP + "import Mathlib.Tactic.Linarith\ntheorem t (x : Nat) (h : x > 3) : x + 2 > 5 := by sorry"})
    print("tactics:", json.dumps(d)[:400])
    print("health:", urllib.request.urlopen("http://127.0.0.1:%d/health" % port, timeout=5).read().decode())
print("\nFAILED CONTROLS:", bad)
