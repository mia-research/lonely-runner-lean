# Bitcoin Puzzle #135 — Team Kangaroo Pool (single-file bundle)

> **This one file is everything you need to run the pool.** The guide is below,
> followed by the complete source of the three runnable files in the
> [Appendix](#appendix--full-source). To use it: create a folder, save each code
> block at the end to the filename in its heading, then follow **Quick start**.
> Requirement: Python 3.8+ (standard library only — no installs).

---

# Bitcoin Puzzle #135 — Team Kangaroo Pool

*One document to read, run, and share. Supersedes the internal handoff notes.*

We built a **shared, distributed Pollard-kangaroo search** pointed at the real,
unsolved Puzzle #135. Anyone on the team can contribute fallow compute; everyone's
work merges into **one** search instead of N private ones.

**Be honest with yourselves up front:** at any compute the team can realistically
muster, this never actually finds the key. It's a shared *Andromeda shot* — a group
lottery ticket that's genuinely bought and genuinely searching, not a progress bar.
The value is a real, correct, improvable thing we own together. See
[The honest ceiling](#the-honest-ceiling).

---

## The target

| | |
|---|---|
| Puzzle | #135 (unsolved, ~13.5 BTC) |
| Public key | `02145d2611c823a396ef6712ce0f712f09b9b4f3135e3e0aa3230fb9b6d08d1e16` |
| Address | `16RGFo6hjq9ym6Pj7N5H7L1NR1rVPJyw2v` |
| Private key range | `2^134 … 2^135` (verified on-curve) |

The public key is exposed, which is the only reason a √-speedup attack is even possible.

---

## Why this design — the three rungs

**1. Brute force → hopeless at any speed.** The key is one of 2¹³⁴ ≈ 2.2×10⁴⁰ values.
Faster hardware only multiplies the *check rate* by a constant, and no constant beats an
exponent:

| compute | time to search 2¹³⁴ | vs age of universe |
|---|---|---|
| a quadrillion keys/s (10¹⁵) | 6.9×10¹⁷ yr | 50 million × |
| the entire Bitcoin network (10²¹) | 6.9×10¹¹ yr | 50 × |

*(`python3 why_speed_cannot_win.py` prints this.)* This is why a "faster engine" is the
wrong lever — it optimizes the one term that provably can't win.

**2. Kangaroo → the real method.** Pollard's kangaroo uses the exposed public key to find
`d` in a known interval in **~2·√W ≈ 2⁶⁷·⁵ ≈ 3×10²⁰** group operations — a square-root
speedup. That's finite. It's how #120 / #125 / #130 actually fell. On a 1,000-GPU cluster
(~10¹² ops/s) that's on the order of **years**, not never. *(`python3 puzzle_kangaroo.py`
prints the honest cost; `--demo` solves a small interval live to prove the machinery.)*

**3. Pool → everyone's kangaroos combine.** Ten people running kangaroo independently are
ten slow searches. Pointed at one **shared distinguished-point (DP) table**, they are one
~10× search. That's this tool.

The only lever left after this is a *smaller exponent* — a genuine structural leak in the
keys. We hunted that separately and found nothing: the keys behave like uniform-random
integers. So kangaroo-at-scale is the honest state of the art.

---

## Quick start

Pure Python, standard library only. No installs. Python 3.8+.

### 1 — One person hosts the server (a laptop/VM that stays up)

```
python3 puzzle_kangaroo_pool.py serve --puzzle 135 --dp-bits 24 --db pool135.db --port 8080
```

- `--puzzle 135` loads the real on-curve pubkey + interval.
- The DB is persistent and crash-safe (SQLite WAL) — restart any time; the frozen
  problem and every distinguished point survive.
- Note the host's reachable address (e.g. `http://192.168.1.50:8080`) and share it.

### 2 — Everyone else contributes compute

```
python3 puzzle_kangaroo_pool.py work --server http://<host>:8080 --name you
```

Add `--sleep 5` to pause 5 s between batches (gentler on a shared machine). The worker
pulls the problem, walks herds, submits the DPs it finds, and stops automatically if the
pool is ever solved.

### 3 — Anyone checks standings

```
python3 puzzle_kangaroo_pool.py board --server http://<host>:8080
```

…or just open `http://<host>:8080/` in a browser (same scoreboard).

---

## Prove it works before you trust it

```
python3 puzzle_kangaroo_pool.py demo --clients 4 --width-bits 24
```

Hides a key in a small interval, runs 4 clients against one shared table, and recovers it
**exactly** — the same machinery as the real pool, at a size that finishes in seconds.
Verified: it solves and reports the winner.

*(The repo also ships an exact-integer integrity check, `check_no_float.py`, that
verifies the signal path uses no floating point. It's a dev gate — not needed to run
the pool, so it isn't bundled here.)*

---

## How it works (and why it's safe)

Two herds do pseudorandom jumps where **the jump size depends only on the current point**,
so once any two kangaroos land on the same point they merge forever:

```
tame point = val·G          (val = absolute exponent)
wild point = Q + val·G      (val = accumulated distance from the target Q)
same point, opposite herds  ⇒  d = tame_val − wild_val
```

The server keeps a shared table of distinguished points (points whose x-coordinate ends in
`dp_bits` zero bits). When a tame DP and a wild DP collide, it recovers `d`.

**Self-verifying — bad nodes can't hurt it.** A solve is accepted **only when `d·G == Q`**
(the recovered key actually reproduces the target public key). A forged or buggy DP yields a
`d` that fails this check and is dropped. Malformed submissions are skipped, never fatal.
The worst a bad contributor can do is waste table space — it can **never** fake a win or
corrupt a real one.

**Why anyone's worker merges correctly:** every node computes the *identical* jump function
(same `scan_herd`, same curve arithmetic). Any worker built to the contract below will
combine with the pool.

---

## Tuning

- **`--dp-bits`** (rarity of distinguished points; ~1 DP per `2^dp_bits` jumps).
  - Lower → more DPs → bigger table, finer detection. Higher → fewer DPs → tiny table.
  - Rough guide: pick it so *(expected total team jumps) / 2^dp_bits* ≈ 10⁵–10⁶ rows.
  - **`24` is a sane start** (~16M jumps per DP). The interval-derived default (62) is far
    too sparse for a pool — always override it.
  - **Honest caveat:** `dp_bits` governs table size and detection granularity, *not the
    odds*. It is not a lever on "our chances."
- **`--k`** (number of jump sizes; mean jump ~`2^k/k`). Default is fine; leave it unless tuning.

---

## Files

*The three kangaroo files below are included in full in the [Appendix](#appendix--full-source) of this document — save each to its filename. The remaining files live in the full investigation repo.*


| file | what it is |
|---|---|
| `puzzle_kangaroo_pool.py` | **The pool.** `serve` / `work` / `board` / `demo`. http.server + sqlite3 + urllib. |
| `puzzle_kangaroo_distributed.py` | Curve + worker (`scan_herd`) the pool reuses, so every node's jumps merge. Also a `--demo` coordinator with pluggable `local`/`mock`/`lambda` backends. |
| `puzzle_kangaroo.py` | Single-process reference + honest `#135` cost report. `--demo` solves a small interval. |
| `puzzle135_bruteforce_toy.py` | The naive brute-forcer — the "why it's hopeless" teaching piece. `--demo` finds a small key. |
| `why_speed_cannot_win.py` | Prints the compute-vs-universe table. |
| `check_no_float.sh` | Integrity gate (exact-integer signal path). |

### Worker contract (for anyone writing a faster worker)

```
request  {"pubkey":"02..","a":"0x..","b":"0x..","K":int,"dp_bits":int,
          "herd":"tame"|"wild","start":"0x..","jumps":int}
response {"dps": [["0x<x>","0x<y>","0x<val>"], ...]}
```

Match `scan_herd`'s jump function exactly and your worker's DPs will merge with everyone's.

---

## The honest ceiling

#135 is **~2⁶⁷·⁵ group operations no matter how many people plug in.** Everything we can add
— more nodes, a compiled/GPU worker (the real 10⁴–10⁶× lever), continuous herds (~10×),
the negation map (~1.4×) — changes the *constant* and *who can participate*, never the
*exponent*. Expected result: nil — a shared one. That's the point. The ticket is bought,
it's real, and it's ours.

### What's next (optional, "fun page")

- **Faster workers** behind the same contract: a native/GPU kangaroo (libsecp256k1, batched
  inversions). Pure Python is ~8,000 jumps/s and the GIL means one `work` process = one core
  — scale by running many processes/machines, or drop in a fast worker. *This is the only
  change that moves jumps/s.*
- Algorithmic constant-factor wins (van Oorschot–Wiener continuous herds, negation map).
- A cumulative "jumps ever / DPs ever" counter and a polished intranet scoreboard.


---

# Appendix — full source
Save each block to the filename in its heading, all in one folder.

## `puzzle_kangaroo_distributed.py`

Curve + worker (`scan_herd`). The pool imports from this — **required**.

```python
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

```

## `puzzle_kangaroo_pool.py`

The pool server/client. **Required.** Run this.

```python
#!/usr/bin/env python3
"""
puzzle_kangaroo_pool.py  —  a shared distinguished-point POOL for distributed kangaroo.

This is the piece that makes contributed compute ACTUALLY COMBINE. Ten people running
the plain solver independently are ten slow searches; pointed at one pool they are one
10x search, because they share a single distinguished-point (DP) table.

A small always-on SERVER owns the problem (pubkey, interval, jump rules) and a
persistent shared DP table (SQLite). Any number of CLIENTS pull the problem, walk
herds on whatever fallow compute they have, and POST the DPs they hit. The server
dedups, and on a tame/wild collision recovers the key -- but only ACCEPTS a solve when
d*G == Q. That self-verification is the pool's safety net: a bad or buggy contributor
can waste table space but CANNOT fake a win or corrupt a real one.

  serve  --pubkey 02.. --a 0x.. --b 0x.. [--db pool.db] [--port 8080]
  work   --server URL --name alice [--batch 3000] [--sleep S]
  board  --server URL                                 print the live scoreboard
  demo   [--clients 4] [--width-bits 28]              self-hosted end-to-end proof

Reuses the curve + worker (scan_herd) from puzzle_kangaroo_distributed.py, so every
node computes the identical jump function. Stdlib only (http.server, sqlite3, urllib).

Collision math (matches scan_herd):
  tame point = val*G            (val = absolute exponent)
  wild point = Q + val*G        (val = accumulated distance from Q)
  same point, opposite herds => d = tame_val - wild_val   (accepted iff d*G == Q)

Bad-node resistance: a forged DP with a val that does not match its point produces a
d that fails d*G == Q, so it is dropped. Worst case is wasted storage, never a fake win.
The server also keeps ALL (point, herd, val) rows, so a junk DP cannot shadow a real
collision at the same point.
"""
import argparse, json, sqlite3, threading, time, secrets, sys, urllib.request
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from puzzle_kangaroo_distributed import mul, decompress, scan_herd

def derive_params(a, b):
    B = (b - a).bit_length()
    return B, max(8, B // 2 + 2), max(1, B // 2 - 5)      # B, K, dp_bits (matches solve())

# Real, verified-on-curve puzzle targets -- the actual tickets, not demo keys.
TARGET_135 = "02145d2611c823a396ef6712ce0f712f09b9b4f3135e3e0aa3230fb9b6d08d1e16"
PUZZLES = {135: {"pubkey": TARGET_135, "a": 1 << 134, "b": 1 << 135}}

# ------------------------------- shared pool state ------------------------------
class Pool:
    """Owns the problem spec, the DP table, the scoreboard, and the solution."""
    def __init__(self, db, pubkey, a, b, k=None, dp_bits=None):
        self.lock = threading.Lock()
        self.db = sqlite3.connect(db, check_same_thread=False)
        if db != ":memory:":
            self.db.execute("PRAGMA journal_mode=WAL")       # crash-safe, survives restarts
            self.db.execute("PRAGMA synchronous=NORMAL")
        self.db.executescript(
            "CREATE TABLE IF NOT EXISTS dps(x TEXT,y TEXT,herd TEXT,val TEXT,who TEXT,ts REAL,"
            "  PRIMARY KEY(x,y,herd,val));"
            "CREATE INDEX IF NOT EXISTS dp_pt ON dps(x,y);"
            "CREATE TABLE IF NOT EXISTS stats(who TEXT PRIMARY KEY,jumps INTEGER,dps INTEGER,last REAL);"
            "CREATE TABLE IF NOT EXISTS meta(k TEXT PRIMARY KEY,v TEXT);"
            "CREATE TABLE IF NOT EXISTS solution(id INTEGER PRIMARY KEY CHECK(id=1),d TEXT,who TEXT,ts REAL);")
        _, K, DPB = derive_params(a, b)
        if k is not None:
            K = k
        if dp_bits is not None:
            DPB = dp_bits
        spec = {"pubkey": pubkey, "a": hex(a), "b": hex(b), "K": K, "dp_bits": DPB}
        row = self.db.execute("SELECT v FROM meta WHERE k='problem'").fetchone()
        if row is None:                                  # first time: freeze this problem
            self.db.execute("INSERT INTO meta VALUES('problem',?)", (json.dumps(spec),))
            self.db.commit()
        else:                                            # reopened db: keep stored problem
            stored = json.loads(row[0])
            if stored != spec:
                print(f"NOTE: db already holds a different problem; using stored one "
                      f"({stored['pubkey'][:14]}..). Ignoring CLI problem args.")
            spec = stored
        self.spec = spec
        self.a, self.b = int(spec["a"], 16), int(spec["b"], 16)
        self.Q = decompress(spec["pubkey"])

    def submit(self, who, jumps, dps):
        with self.lock:
            done = self.db.execute("SELECT d FROM solution WHERE id=1").fetchone()
            if done:
                return {"solved": True, "d": done[0]}
            accepted = 0
            found = None
            for dp in dps:
                if not (isinstance(dp, (list, tuple)) and len(dp) == 4):
                    continue                                     # malformed row -> skip, never crash
                x, y, val, herd = dp
                if herd not in ("tame", "wild"):
                    continue
                try:
                    iv, _, _ = int(val, 16), int(x, 16), int(y, 16)
                except (TypeError, ValueError):
                    continue                                     # non-hex junk -> skip
                for (oval,) in self.db.execute(
                        "SELECT val FROM dps WHERE x=? AND y=? AND herd!=?", (x, y, herd)):
                    tv, wv = (iv, int(oval, 16)) if herd == "tame" else (int(oval, 16), iv)
                    d = tv - wv
                    if self.a <= d <= self.b and mul(d) == self.Q:   # self-verify: forged DP can't pass
                        found = d
                        break
                cur = self.db.execute("INSERT OR IGNORE INTO dps VALUES(?,?,?,?,?,?)",
                                      (x, y, herd, val, who, time.time()))
                accepted += cur.rowcount
                if found is not None:
                    break
            now = time.time()
            self.db.execute(
                "INSERT INTO stats(who,jumps,dps,last) VALUES(?,?,?,?) "
                "ON CONFLICT(who) DO UPDATE SET jumps=jumps+excluded.jumps, "
                "dps=dps+excluded.dps, last=excluded.last",
                (who, max(0, jumps), accepted, now))
            if found is not None:
                self.db.execute("INSERT OR IGNORE INTO solution VALUES(1,?,?,?)",
                                (hex(found), who, now))
            self.db.commit()
            return {"solved": found is not None,
                    "d": hex(found) if found is not None else None, "accepted": accepted}

    def stats(self):
        with self.lock:
            sol = self.db.execute("SELECT d,who FROM solution WHERE id=1").fetchone()
            board = self.db.execute(
                "SELECT who,jumps,dps,last FROM stats ORDER BY jumps DESC").fetchall()
            ndps = self.db.execute("SELECT COUNT(*) FROM dps").fetchone()[0]
            return {"solved": sol is not None, "d": sol[0] if sol else None,
                    "winner": sol[1] if sol else None,
                    "total_jumps": sum(r[1] for r in board), "table": ndps,
                    "board": [{"who": w, "jumps": j, "dps": d, "last": l} for w, j, d, l in board],
                    "problem": self.spec}

def scoreboard_text(s):
    p = s["problem"]
    a, b = int(p["a"], 16), int(p["b"], 16)
    B = (b - a).bit_length()
    ideal = 2 << (B // 2)                                 # ~2*sqrt(W); real design ~10x more
    tj = s["total_jumps"]
    now = time.time()
    L = [f"=== Kangaroo Pool  [{p['pubkey'][:12]}..]  interval 2^{a.bit_length()-1}..2^{b.bit_length()-1}  (width ~2^{B-1}) ==="]
    if s["solved"]:
        L.append(f"STATUS: *** SOLVED ***  d = {s['d']}   (winner: {s['winner']})")
    else:
        L.append(f"STATUS: searching   {tj:,} jumps  |  {s['table']:,} DPs in table")
        L.append(f"        ideal ~2*sqrt(W) = {ideal:,} jumps (this herd design costs ~10x that); "
                 f"it's a birthday lottery, not a progress bar")
    L.append("--- contributors (by jumps) ---")
    for r in s["board"] or [{"who": "(nobody yet)", "jumps": 0, "dps": 0, "last": now}]:
        ago = int(now - r["last"]) if r["jumps"] else 0
        L.append(f"  {r['who']:<16} {r['jumps']:>15,} jumps  {r['dps']:>6,} DPs   (last {ago}s ago)")
    return "\n".join(L) + "\n"

# ------------------------------- HTTP server ------------------------------------
def make_handler(pool):
    class H(BaseHTTPRequestHandler):
        def log_message(self, *a):
            pass
        def _send(self, obj, code=200, ctype="application/json"):
            body = obj if isinstance(obj, (bytes, bytearray)) else json.dumps(obj).encode()
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        def do_GET(self):
            if self.path.startswith("/problem"):
                self._send(pool.spec)
            elif self.path.startswith("/stats"):
                self._send(pool.stats())
            elif self.path == "/":
                self._send(scoreboard_text(pool.stats()).encode(), ctype="text/plain; charset=utf-8")
            else:
                self._send({"error": "not found"}, 404)
        def do_POST(self):
            n = int(self.headers.get("Content-Length", 0) or 0)
            try:
                body = json.loads(self.rfile.read(n) or b"{}")
            except Exception:
                return self._send({"error": "bad json"}, 400)
            if self.path.startswith("/submit"):
                self._send(pool.submit(body.get("who", "anon"),
                                       int(body.get("jumps", 0)), body.get("dps", [])))
            else:
                self._send({"error": "not found"}, 404)
    return H

def serve(pubkey, a, b, db, port, host="0.0.0.0", k=None, dp_bits=None):
    pool = Pool(db, pubkey, a, b, k, dp_bits)
    httpd = ThreadingHTTPServer((host, port), make_handler(pool))
    p = pool.spec
    print(f"pool server up on http://{host}:{httpd.server_address[1]}   db={db}")
    print(f"  problem: {p['pubkey'][:16]}..  interval [{p['a']}, {p['b']}]  K={p['K']} dp_bits={p['dp_bits']}")
    print(f"  clients: python3 puzzle_kangaroo_pool.py work --server http://<host>:{httpd.server_address[1]} --name you")
    httpd.serve_forever()

# ------------------------------- pool client ------------------------------------
def _get(url):
    with urllib.request.urlopen(url, timeout=30) as r:
        return json.loads(r.read().decode())
def _post(url, obj):
    req = urllib.request.Request(url, data=json.dumps(obj).encode(),
                                 headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=180) as r:
        return json.loads(r.read().decode())

def client(server, name, batch=3000, sleep_s=0, max_rounds=None, quiet=False):
    """Pull the problem, walk herds, submit DPs, until the POOL is solved."""
    spec = _get(server.rstrip("/") + "/problem")
    a, b = int(spec["a"], 16), int(spec["b"], 16)
    B = (b - a).bit_length()
    sent = 0
    rounds = 0
    t0 = time.time()
    while True:
        if secrets.randbits(1):                          # tame: absolute exponent in [a,b)
            herd, start = "tame", a + secrets.randbelow(b - a)
        else:                                            # wild: small offset from Q
            herd, start = "wild", secrets.randbelow(1 << (B // 2))
        raw = scan_herd(spec["pubkey"], a, b, int(spec["K"]), int(spec["dp_bits"]),
                        herd, start, batch)
        dps = [[x, y, v, herd] for x, y, v in raw]
        res = _post(server.rstrip("/") + "/submit",
                    {"who": name, "jumps": batch, "dps": dps})
        rounds += 1
        sent += len(dps)
        if res.get("solved"):
            if not quiet:
                print(f"\n[{name}] *** POOL SOLVED ***  d = {res.get('d')}")
            return res.get("d")
        if not quiet:
            el = time.time() - t0
            rate = rounds * batch * 1000 // max(int(el * 1000), 1)
            sys.stdout.write(f"\r[{name}] {rounds*batch:,} jumps  {sent:,} DPs sent  "
                             f"{rate:,} jumps/s   ")
            sys.stdout.flush()
        if max_rounds and rounds >= max_rounds:
            return None
        if sleep_s:                                      # be a polite fallow-compute citizen
            time.sleep(sleep_s)

def board(server):
    print(scoreboard_text(_get(server.rstrip("/") + "/stats")), end="")

# ------------------------------- demo (self-test) -------------------------------
def demo(clients, width_bits):
    a = 1 << 50
    b = a + (1 << width_bits)
    secret = a + secrets.randbelow(b - a)
    pub = f"{2 + (mul(secret)[1] & 1):02x}{mul(secret)[0]:032x}"
    pool = Pool(":memory:", pub, a, b)
    httpd = ThreadingHTTPServer(("127.0.0.1", 0), make_handler(pool))
    threading.Thread(target=httpd.serve_forever, daemon=True).start()
    url = f"http://127.0.0.1:{httpd.server_address[1]}"
    print(f"DEMO: hid a key in width 2^{width_bits}; pool server on {url}; {clients} clients sharing ONE DP table.")
    print(f"  brute force = up to 2^{width_bits} checks; the herd only combines because the table is shared.\n")
    t0 = time.time()
    errors = []
    def run(name):
        try:
            client(url, name, batch=2000, quiet=True)
        except Exception as e:
            errors.append((name, repr(e)))
    threads = [threading.Thread(target=run, args=(f"node{i}",), daemon=True)
               for i in range(clients)]
    for t in threads:
        t.start()
    while not pool.stats()["solved"]:
        time.sleep(1)
        if errors:
            print(f"\n  client error: {errors[0]}"); httpd.shutdown(); return
        s = pool.stats()
        el = time.time() - t0
        rate = s["total_jumps"] * 1000 // max(int(el * 1000), 1)
        sys.stdout.write(f"\r  pooled {s['total_jumps']:,} jumps  {s['table']:,} DPs  "
                         f"{rate:,} jumps/s across {clients} clients   ")
        sys.stdout.flush()
        if el > 600:
            print("\n  demo cap reached without solve (raise --width-bits patience or lower it)")
            httpd.shutdown(); return
    print("\n\n" + scoreboard_text(pool.stats()))
    d = pool.stats()["d"]
    print(f"  match: {int(d, 16) == secret}   (secret was {hex(secret)})")
    httpd.shutdown()

# ------------------------------- cli --------------------------------------------
def main():
    ap = argparse.ArgumentParser(description="Shared-DP pool for distributed kangaroo.")
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("serve")
    s.add_argument("--puzzle", type=int, help="known on-curve target by number (e.g. 135); the real ticket")
    s.add_argument("--pubkey"); s.add_argument("--a"); s.add_argument("--b")
    s.add_argument("--db", default="pool.db"); s.add_argument("--port", type=int, default=8080)
    s.add_argument("--dp-bits", type=int, dest="dp_bits",
                   help="distinguished-point rarity 2^-dp_bits (detection vs. table size); the interval-derived default is too sparse for a real pool")
    s.add_argument("--k", type=int, help="number of jump sizes; mean jump ~2^k/k")
    w = sub.add_parser("work"); w.add_argument("--server", required=True)
    w.add_argument("--name", default="anon"); w.add_argument("--batch", type=int, default=3000)
    w.add_argument("--sleep", type=int, default=0, help="seconds to pause between batches (fallow-friendly)")
    bd = sub.add_parser("board"); bd.add_argument("--server", required=True)
    d = sub.add_parser("demo"); d.add_argument("--clients", type=int, default=4)
    d.add_argument("--width-bits", type=int, default=28)
    args = ap.parse_args()
    if args.cmd == "serve":
        if args.puzzle is not None:
            t = PUZZLES.get(args.puzzle)
            if not t:
                ap.error(f"unknown puzzle {args.puzzle}; known: {sorted(PUZZLES)}")
            pub, a, b = t["pubkey"], t["a"], t["b"]
        elif args.pubkey and args.a and args.b:
            pub, a, b = args.pubkey, int(args.a, 16), int(args.b, 16)
        else:
            ap.error("serve needs --puzzle N, or all of --pubkey --a --b")
        serve(pub, a, b, args.db, args.port, k=args.k, dp_bits=args.dp_bits)
    elif args.cmd == "work":
        client(args.server, args.name, args.batch, args.sleep)
    elif args.cmd == "board":
        board(args.server)
    elif args.cmd == "demo":
        demo(args.clients, args.width_bits)

if __name__ == "__main__":
    main()

```

## `puzzle_kangaroo.py`

Single-process reference + honest #135 cost report. Optional but handy.

```python
#!/usr/bin/env python3
"""
puzzle_kangaroo.py  —  the REAL technique: Pollard's kangaroo for interval ECDLP.

Brute force (puzzle135_bruteforce_toy.py) needs 2^134 key checks -> hopeless. Kangaroo
uses the exposed public key to find d in a KNOWN interval [a,b] in ~2*sqrt(b-a) group
operations -- a square-root speedup. For #135 that is ~2^67.5 (finite, but still huge).
This is how exposed-pubkey puzzles (#120/#125/#130) actually fell.

  --demo         : hide a key in a real interval and SOLVE it with kangaroo (proves it works,
                   and shows steps ~ sqrt(W) vs brute force's W).
  (no args)      : set up kangaroo on the real #135 pubkey, measure jump rate on a live
                   sample, and report the honest 2^67.5 cost + time. It does NOT finish.

Two tame/wild herds do pseudorandom jumps (jump size depends only on the current point,
so once they collide they merge); distinguished points detect the collision with little
memory. Pure-integer secp256k1, stdlib only.
"""
import argparse, os, sys, time, secrets

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
def decompress(comp_hex):
    pre = int(comp_hex[:2], 16); x = int(comp_hex[2:], 16)
    y = pow((x * x * x + 7) % P, (P + 1) // 4, P)
    if (y & 1) != (pre & 1): y = P - y
    return (x, y)

def make_jumps(W):
    B = W.bit_length()
    K = max(8, B // 2 + 2)
    jumps = [1 << i for i in range(K)]
    return K, jumps, [mul(s) for s in jumps]        # precomputed s*G

def kangaroo(Q, a, b, max_mult=60, report=None):
    """Find d in [a,b] with d*G == Q. Returns (d, steps) or (None, steps)."""
    W = b - a; B = W.bit_length()
    K, jumps, jumpG = make_jumps(W)
    dp_bits = max(1, B // 2 - 5); dp_mask = (1 << dp_bits) - 1
    max_steps = max_mult * (1 << (B // 2)) + 5000
    tame_e0 = (a + b) // 2
    T = mul(tame_e0); td = 0
    Wp = Q; wd = 0
    table = {}; steps = 0; t0 = time.time()
    while steps < max_steps:
        i = T[0] % K; T = add(T, jumpG[i]); td += jumps[i]
        if (T[0] & dp_mask) == 0:
            e = table.get(T)
            if e and e[0] == "W":
                d = tame_e0 + td - e[1]
                if a <= d <= b and mul(d) == Q: return d, steps
            table[T] = ("T", td)
        i = Wp[0] % K; Wp = add(Wp, jumpG[i]); wd += jumps[i]
        if (Wp[0] & dp_mask) == 0:
            e = table.get(Wp)
            if e and e[0] == "T":
                d = tame_e0 + e[1] - wd
                if a <= d <= b and mul(d) == Q: return d, steps
            table[Wp] = ("W", wd)
        steps += 1
        if report and steps % report == 0:
            r = steps / (time.time() - t0)                          # noqa: float (display rate only; never touches keys)
            sys.stdout.write(f"\r  {steps:,} jumps  {r:,.0f} jumps/s  table {len(table):,}   ")
            sys.stdout.flush()
    return None, steps

def demo():
    width_bits = 36
    a = 1 << 50; b = a + (1 << width_bits)
    secret = a + secrets.randbelow(b - a)
    Q = mul(secret)
    print(f"DEMO: hid a key in an interval of width 2^{width_bits} = {b-a:,}")
    print(f"  brute force would need up to {b-a:,} checks (~2^{width_bits}).")
    print(f"  kangaroo expects ~2*sqrt(W) ~ 2^{width_bits//2 + 1} ~ {2*(1<<(width_bits//2)):,} steps.\n")
    t = time.time()
    d, steps = kangaroo(Q, a, b, report=20000)
    dt = time.time() - t
    print(f"\n\n  {'SOLVED' if d == secret else 'FAILED'}: d = {hex(d) if d else None}")
    print(f"  took {steps:,} jumps in {dt:.1f}s  ({steps/dt:,.0f}/s)")   # noqa: float (display only)
    print(f"  speedup vs brute force: ~{(b-a)//max(steps,1):,}x fewer operations")

TARGET_135 = "02145d2611c823a396ef6712ce0f712f09b9b4f3135e3e0aa3230fb9b6d08d1e16"

def hunt135(sample=100000):
    a, b = 1 << 134, 1 << 135; W = b - a
    Q = decompress(TARGET_135)
    assert (Q[1] * Q[1] - Q[0] ** 3 - 7) % P == 0, "pubkey not on curve"
    ops = 2 * (1 << 67)                                   # ~2*sqrt(2^134) = 2^68.5-ish
    print("=== Pollard kangaroo on Bitcoin Puzzle #135 (the real method) ===")
    print(f"interval : 2^134 .. 2^135   (width 2^134 = {W:.3e})")
    print(f"pubkey   : {TARGET_135}  (on curve: yes)")
    print(f"brute    : ~2^134 = {float(1<<134):.2e} key checks")   # noqa: float (display only)
    print(f"kangaroo : ~2*sqrt(W) = ~2^67.5 = {ops:.2e} group ops  ({(1<<134)//ops:,.0f}x fewer)\n")
    print(f"Measuring real jump rate on this machine ({sample:,} jumps)...")
    K, jumps, jumpG = make_jumps(W)
    Xt = mul((a + b) // 2); Xw = Q; t0 = time.time()
    for s in range(1, sample + 1):
        Xt = add(Xt, jumpG[Xt[0] % K]); Xw = add(Xw, jumpG[Xw[0] % K])
        if s % 20000 == 0:
            r = s / (time.time() - t0)                              # noqa: float (display only)
            sys.stdout.write(f"\r  {s:,} jumps  {r:,.0f} jumps/s   "); sys.stdout.flush()
    rate = sample / (time.time() - t0)                             # noqa: float (display/ETA only; never touches keys)
    yrs = ops / rate / (365.25 * 86400)                            # noqa: float (display ETA only)
    print(f"\n\n  this machine: {rate:,.0f} jumps/s (pure Python).")
    print(f"  => ~2^67.5 ops here would take ~{yrs:.2e} years.")
    print(f"  On a 1000-GPU cluster at ~1e12 ops/s: ~{ops/1e12/(365.25*86400):.1f} years -- finite, but real.")   # noqa: float (display only)
    print("  (This is the honest state of the art. It does NOT run to completion here.)")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--demo", action="store_true")
    ap.add_argument("--sample", type=int, default=100000)
    a = ap.parse_args()
    if a.demo: demo()
    else: hunt135(a.sample)

if __name__ == "__main__":
    main()

```
