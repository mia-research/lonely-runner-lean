#!/usr/bin/env python3
"""
puzzle_kangaroo_distributed.py  —  Pollard kangaroo, fanned out over pluggable workers.

Real distributed kangaroo: a COORDINATOR (your laptop) owns the problem (pubkey,
interval, jump rules) and the shared distinguished-point (DP) table. It hands out
independent WORK UNITS -- "start a herd at <point>, do N jumps, return every DP you
hit" -- to a BACKEND. Because the jump function depends only on the current point,
a tame DP and a wild DP that ever land on the same point reveal the key:
    tame absolute exponent  =  d + wild accumulated distance   ->   d = tame_val - wild_val
N workers cover ~N x more ground, so wall-clock ~ 2*sqrt(W) / N. Same backend model as
the brute-force toy: swap local <-> mock <-> lambda to dial compute up/down.

  --demo                          solve a real interval, fanning batches to a backend
  --backend {local,mock,lambda}   choose compute (lambda needs --url)
  --workers K                     dispatch K batches concurrently (real speedup on lambda)

CONTRACT (what a kangaroo Lambda must honor):
  request  {"pubkey":"02..","a":"0x..","b":"0x..","K":int,"dp_bits":int,
            "herd":"tame"|"wild","start":"0x..","jumps":int}
  response {"dps": [["0x<x>","0x<y>","0x<val>"], ...]}
Deploy this file's lambda_handler as the worker. Pure-int secp256k1, stdlib only.
"""
import argparse, json, os, sys, time, secrets, urllib.request
from concurrent.futures import ThreadPoolExecutor

P     = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N_ORD = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G  = (Gx, Gy)

def inv(x): return pow(x % P, P - 2, P)
def add(A, B):
    if A is None: return B
    if B is None: return A
    x1, y1 = A; x2, y2 = B
    if x1 == x2 and (y1 + y2) % P == 0: return None
    m = (3 * x1 * x1) * inv(2 * y1) % P if A == B else (y2 - y1) * inv(x2 - x1) % P
    x3 = (m * m - x1 - x2) % P
    return (x3, (m * (x1 - x3) - y1) % P)
def mul(k, Pt=G):
    R = None; A = Pt
    while k:
        if k & 1: R = add(R, A)
        A = add(A, A); k >>= 1
    return R
def decompress(h):
    pre = int(h[:2], 16); x = int(h[2:], 16)
    y = pow((x * x * x + 7) % P, (P + 1) // 4, P)
    return (x, y if (y & 1) == (pre & 1) else P - y)

# ------------------------------- worker core ------------------------------------
def scan_herd(pubkey, a, b, K, dp_bits, herd, start, jumps):
    """Walk one herd for `jumps` steps; return the distinguished points hit.
    tame: X = start*G, val = start + dist (absolute exponent).
    wild: X = Q + start*G, val = start + dist (accumulated distance from Q)."""
    jumpG = [mul(1 << i) for i in range(K)]
    dp_mask = (1 << dp_bits) - 1
    if herd == "tame":
        X = mul(start)
    else:
        X = add(decompress(pubkey), mul(start) if start else None)
    val = start; dps = []
    for _ in range(jumps):
        i = X[0] % K
        X = add(X, jumpG[i]); val += (1 << i)
        if (X[0] & dp_mask) == 0:
            dps.append([hex(X[0]), hex(X[1]), hex(val)])
    return dps

def lambda_handler(event, context=None):
    try:
        body = event.get("body", event) if isinstance(event, dict) else event
        if isinstance(body, str): body = json.loads(body)
        dps = scan_herd(body["pubkey"], int(body["a"], 16), int(body["b"], 16),
                        int(body["K"]), int(body["dp_bits"]), body["herd"],
                        int(body["start"], 16), int(body["jumps"]))
        return {"statusCode": 200, "body": json.dumps({"dps": dps})}
    except Exception as e:
        return {"statusCode": 500, "body": json.dumps({"error": str(e)})}

# ------------------------------- backends ---------------------------------------
def backend_local(req):  return json.loads(lambda_handler({"body": json.dumps(req)})["body"])
def backend_mock(req):   return _unwrap(lambda_handler({"body": json.dumps(req)}))
def make_backend_lambda(url):
    def call(req):
        data = json.dumps(req).encode()
        r = urllib.request.Request(url, data=data, headers={"Content-Type": "application/json"})
        with urllib.request.urlopen(r, timeout=300) as resp:
            return _unwrap(json.loads(resp.read().decode()))
    return call
def _unwrap(resp):
    if isinstance(resp, dict) and "dps" not in resp and "body" in resp:
        resp = json.loads(resp["body"])
    return resp

# ------------------------------ coordinator -------------------------------------
def solve(pubkey, a, b, backend, batch=4000, workers=1, max_jumps=None):
    Q = decompress(pubkey); W = b - a; B = W.bit_length()
    K = max(8, B // 2 + 2); dp_bits = max(1, B // 2 - 5)
    if max_jumps is None: max_jumps = 80 * (1 << (B // 2))
    print(f"coordinator: interval 2^{a.bit_length()-1}..2^{b.bit_length()-1}  "
          f"K={K} dp_bits={dp_bits} batch={batch} workers={workers}")
    table = {}; total = 0; dps_seen = 0; t0 = time.time(); pool = ThreadPoolExecutor(workers)
    while total < max_jumps:
        jobs = []
        for _ in range(workers):
            if secrets.randbits(1):                              # tame: random exponent in [a,b]
                herd, start = "tame", a + secrets.randbelow(W)
            else:                                                # wild: random small offset from Q
                herd, start = "wild", secrets.randbelow(1 << (B // 2))
            req = {"pubkey": pubkey, "a": hex(a), "b": hex(b), "K": K, "dp_bits": dp_bits,
                   "herd": herd, "start": hex(start), "jumps": batch}
            jobs.append((herd, backend, req))
        for (herd, _), res in zip([(h, r) for h, _, r in jobs],
                                  pool.map(lambda j: j[1](j[2]), jobs)):
            total += batch
            for xh, yh, vh in res["dps"]:
                pt = (xh, yh); val = int(vh, 16); dps_seen += 1
                prev = table.get(pt)
                if prev and prev[0] != herd:
                    tv, wv = (val, prev[1]) if herd == "tame" else (prev[1], val)
                    d = tv - wv
                    if a <= d <= b and mul(d) == Q:
                        dt = time.time() - t0
                        rate = total * 1000 // max(int(dt * 1000), 1)   # int jumps/s (no float in path)
                        print(f"\n*** SOLVED ***  d = {hex(d)}   ({total:,} jumps, "
                              f"{dps_seen:,} DPs, {dt:.1f}s, {rate:,} jumps/s across {workers} worker(s))")
                        return d
                else:
                    table[pt] = (herd, val)
        el = time.time() - t0
        rate = total * 1000 // max(int(el * 1000), 1)   # int jumps/s (no float in path)
        sys.stdout.write(f"\r  {total:,} jumps  {dps_seen:,} DPs  table {len(table):,}  "
                         f"{rate:,} jumps/s   "); sys.stdout.flush()
    print("\n  (reached jump cap without collision — raise --max or batch)"); return None

TARGET_135 = "02145d2611c823a396ef6712ce0f712f09b9b4f3135e3e0aa3230fb9b6d08d1e16"

def demo(backend, batch, workers):
    wb = 32; a = 1 << 50; b = a + (1 << wb)
    secret = a + secrets.randbelow(b - a)
    pub = f"{2 + (mul(secret)[1] & 1):02x}{mul(secret)[0]:032x}"
    print(f"DEMO: hid a key in width 2^{wb}; distributing kangaroo herds to backend.")
    print(f"  brute force = up to 2^{wb} = {b-a:,} checks; kangaroo ~ 2^{wb//2+1} jumps.\n")
    d = solve(pub, a, b, backend, batch, workers)
    print(f"  match: {d == secret}   (secret was {hex(secret)})")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--backend", choices=["local", "mock", "lambda"], default="local")
    ap.add_argument("--url"); ap.add_argument("--workers", type=int, default=1)
    ap.add_argument("--batch", type=int, default=4000)
    ap.add_argument("--demo", action="store_true")
    a = ap.parse_args()
    backend = make_backend_lambda(a.url) if a.backend == "lambda" else \
        {"local": backend_local, "mock": backend_mock}[a.backend]
    if a.backend == "lambda" and not a.url: sys.exit("--backend lambda requires --url")
    if a.demo: demo(backend, a.batch, a.workers)
    else:
        print("Use --demo to solve a real interval. #135 would fan out identically at 2^67.5 scale.")

if __name__ == "__main__":
    main()
