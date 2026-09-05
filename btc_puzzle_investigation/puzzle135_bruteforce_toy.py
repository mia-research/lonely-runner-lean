#!/usr/bin/env python3
"""
puzzle135_bruteforce_toy.py  —  traditional brute-force search for Bitcoin Puzzle #135,
                                with a PLUGGABLE compute backend (local / mock / lambda).

#135: the private key is a 256-bit integer in [2^134, 2^135) (121 leading zero bits,
then 134 free bits -> 2^134 candidates). The public key is published, so for each
candidate d we compute d*G on secp256k1 and compare to the target -- no hashing needed.

    target pubkey (compressed): 02145d2611c823a396ef6712ce0f712f09b9b4f3135e3e0aa3230fb9b6d08d1e16
    address:                    16RGFo6hjq9ym6Pj7N5H7L1NR1rVPJyw2v
    range:                      2^134 .. 2^135

NO SHORTCUTS: every candidate is a full, independent scalar multiply d*G from scratch
(double-and-add). Nothing is carried between keys. That is the honest brute force, and
-- because each key is independent -- it lets us hand any range chunk to ANY compute
backend and fan it out.

ARCHITECTURE
  * The DRIVER (your laptop) owns the range and the resume state (last integer checked).
  * It dispatches work in chunks to a BACKEND. Swap the backend to change compute:
      --backend local    scan the chunk here (baseline, slow, pure Python)
      --backend mock     scan via the reference lambda_handler in-process (proves contract)
      --backend lambda --url <FunctionURL>   POST the chunk to your Lambda (built elsewhere)
  * State lives on the laptop, so you can stop/resume and switch backends freely.

CONTRACT (what your Lambda must accept and return) -- this is all it needs to honor:
  request  JSON: {"start": "0x<hex>", "count": <int>, "target": "02..<compressed pubkey hex>"}
  response JSON: {"checked": <int>, "found": <bool>, "key": "0x<hex>" | null}
  (A Function URL that returns {"statusCode":200,"body":"<json string>"} is also accepted.)

Pure-integer secp256k1. Only stdlib.

Usage:
  python3 puzzle135_bruteforce_toy.py                         # hunt #135 locally, resumable
  python3 puzzle135_bruteforce_toy.py --backend mock          # same, via the in-process contract
  python3 puzzle135_bruteforce_toy.py --backend lambda --url https://...lambda-url...aws/
  python3 puzzle135_bruteforce_toy.py --demo                  # solve a small known puzzle
  python3 puzzle135_bruteforce_toy.py --chunk 5000 --max 20000
  python3 puzzle135_bruteforce_toy.py --reset
"""
import argparse, json, os, sys, time, secrets, urllib.request

# ------------------------------- secp256k1 --------------------------------------
P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G  = (Gx, Gy)

def inv(x): return pow(x % P, P - 2, P)

def add(A, B):
    if A is None: return B
    if B is None: return A
    x1, y1 = A; x2, y2 = B
    if x1 == x2 and (y1 + y2) % P == 0: return None
    if A == B: m = (3 * x1 * x1) * inv(2 * y1) % P
    else:      m = (y2 - y1) * inv(x2 - x1) % P
    x3 = (m * m - x1 - x2) % P
    return (x3, (m * (x1 - x3) - y1) % P)

def mul(k, Pt=G):
    """Full scalar multiply k*Pt from scratch -- computed fresh for EVERY key. No reuse."""
    R = None; A = Pt
    while k:
        if k & 1: R = add(R, A)
        A = add(A, A); k >>= 1
    return R

def compressed_hex(pt):
    x, y = pt
    return f"{2 + (y & 1):02x}{x:032x}"

# --------------------------- the unit of work (worker core) ----------------------
def scan_chunk(start, count, target):
    """Check `count` keys from `start`, each a FULL d*G. Returns the contract dict.
    This same function runs locally and inside the reference Lambda handler."""
    tx = int(target[2:], 16); tpar = int(target[:2], 16) & 1
    for i in range(count):
        d = start + i
        Pt = mul(d)                                   # full multiply, no shortcut
        if Pt[0] == tx and (Pt[1] & 1) == tpar:
            return {"checked": i + 1, "found": True, "key": hex(d)}
    return {"checked": count, "found": False, "key": None}

def lambda_handler(event, context=None):
    """Reference AWS Lambda handler. Whatever builds the real Lambda should match this
    request/response shape. Accepts a Function-URL event (body string) or a raw dict."""
    body = event.get("body", event) if isinstance(event, dict) else event
    if isinstance(body, str): body = json.loads(body)
    res = scan_chunk(int(body["start"], 16), int(body["count"]), body["target"])
    return {"statusCode": 200, "body": json.dumps(res)}

# ------------------------------- backends ---------------------------------------
def backend_local(start, count, target):
    return scan_chunk(start, count, target)

def backend_mock(start, count, target):
    ev = {"body": json.dumps({"start": hex(start), "count": count, "target": target})}
    return _unwrap(lambda_handler(ev))

def make_backend_lambda(url):
    def call(start, count, target):
        payload = json.dumps({"start": hex(start), "count": count, "target": target}).encode()
        req = urllib.request.Request(url, data=payload, headers={"Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=300) as r:
            return _unwrap(json.loads(r.read().decode()))
    return call

def _unwrap(resp):
    """Accept either {checked,found,key} or a Function-URL {statusCode,body:'<json>'}."""
    if isinstance(resp, dict) and "checked" not in resp and "body" in resp:
        resp = json.loads(resp["body"])
    return resp

# ------------------------------- state file -------------------------------------
def load_state(path, start):
    if os.path.exists(path):
        with open(path) as f: s = json.load(f)
        return int(s["next"], 16), int(s.get("checked", 0)), float(s.get("elapsed", 0.0))
    return start, 0, 0.0

def save_state(path, nxt, checked, elapsed):
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump({"next": hex(nxt), "checked": checked, "elapsed": elapsed}, f)
    os.replace(tmp, path)

def human_years(seconds):
    y = seconds / (365.25 * 86400)
    return f"{y:.2e} years" if y >= 1 else f"{seconds:.1f} s"

# --------------------------------- driver ---------------------------------------
def hunt(start, end, target, state_path, label, backend, chunk, max_keys=None):
    d, checked, prior = load_state(state_path, start)
    if d >= end:
        print("Range already exhausted. (--reset to start over.)"); return
    total = end - start
    print(f"=== {label} ===")
    print(f"range        : 2^{start.bit_length()-1} .. 2^{end.bit_length()-1}   ({total:.2e} keys)")
    print(f"backend      : {backend.__name__ if hasattr(backend,'__name__') else 'lambda'}   chunk={chunk}")
    print(f"target pubkey: {target}")
    print(f"resuming at  : {hex(d)}   ({checked:,} already checked)\n")

    t0 = time.time(); run = 0
    try:
        while d < end and (max_keys is None or run < max_keys):
            n = min(chunk, end - d, (max_keys - run) if max_keys else chunk)
            res = backend(d, n, target)               # <-- dispatch a chunk to the backend
            got = res["checked"]
            if res["found"]:
                elapsed = prior + (time.time() - t0)
                print(f"\n*** KEY FOUND ***  d = {res['key']}")
                save_state(state_path, d + got, checked + got, elapsed)
                with open(state_path + ".FOUND", "w") as f:
                    f.write(f"{label}\nprivate_key_hex={res['key']}\n")
                return
            d += got; checked += got; run += got
            elapsed = prior + (time.time() - t0)
            rate = run / (time.time() - t0) if time.time() > t0 else 0
            eta = human_years((end - d) / rate) if rate > 0 else "inf"
            sys.stdout.write(f"\r checked {checked:,}  at {hex(d)}  {rate:,.0f} keys/s  "
                             f"{100*(d-start)/total:.1e}% of range  ETA {eta}   ")
            sys.stdout.flush()
            save_state(state_path, d, checked, elapsed)
    except KeyboardInterrupt:
        pass
    save_state(state_path, d, checked, prior + (time.time() - t0))
    print(f"\n\nPaused. next = {hex(d)}, checked = {checked:,}. Re-run to resume.")

# --------------------------------- demo -----------------------------------------
def demo(backend, chunk):
    lo = 1 << 20; hi = lo + 4000
    secret = lo + secrets.randbelow(2500)
    target = compressed_hex(mul(secret))
    print(f"DEMO: hid a key in [2^20, 2^20+2500). full d*G per key (no shortcut).\n")
    sp = os.path.join(os.path.dirname(os.path.abspath(__file__)), "puzzle_demo_state.json")
    if os.path.exists(sp): os.remove(sp)
    t = time.time()
    hunt(lo, hi, target, sp, "DEMO mini-puzzle", backend, chunk)
    print(f"(demo took {time.time()-t:.1f}s; secret was {hex(secret)})")

# --------------------------------- main -----------------------------------------
TARGET_135 = "02145d2611c823a396ef6712ce0f712f09b9b4f3135e3e0aa3230fb9b6d08d1e16"

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--backend", choices=["local", "mock", "lambda"], default="local")
    ap.add_argument("--url", help="Lambda Function URL (required for --backend lambda)")
    ap.add_argument("--chunk", type=int, default=2000, help="keys per dispatched work unit")
    ap.add_argument("--max", type=int, default=None, help="stop after this many keys this run")
    ap.add_argument("--demo", action="store_true")
    ap.add_argument("--reset", action="store_true")
    a = ap.parse_args()
    here = os.path.dirname(os.path.abspath(__file__))
    sp = os.path.join(here, "puzzle135_state.json")
    if a.reset:
        for p in (sp, sp + ".tmp", sp + ".FOUND"):
            if os.path.exists(p): os.remove(p)
        print("Progress reset."); return
    if a.backend == "lambda":
        if not a.url: sys.exit("--backend lambda requires --url")
        backend = make_backend_lambda(a.url)
    else:
        backend = {"local": backend_local, "mock": backend_mock}[a.backend]
    if a.demo:
        demo(backend, a.chunk); return
    hunt(1 << 134, 1 << 135, TARGET_135, sp, "Bitcoin Puzzle #135", backend, a.chunk, max_keys=a.max)

if __name__ == "__main__":
    main()
