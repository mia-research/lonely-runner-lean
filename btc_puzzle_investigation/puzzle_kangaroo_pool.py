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
