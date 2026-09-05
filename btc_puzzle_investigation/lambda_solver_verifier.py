#!/usr/bin/env python3
"""
lambda_solver_verifier.py — self-verifying gate for any "instant solver" endpoint.

Purpose
-------
A claimed ECDLP/puzzle "solver" is only real if the private key it returns d'
satisfies  d'*G == Q  for the submitted public key Q. This harness removes all
trust from the loop:

  1. WE generate keypairs (d, Q=d*G) across a range of bit-sizes, so we know the
     ground-truth private key d for every query.
  2. We POST the well-formed public key (on-curve x/y + valid P2PKH address) to
     the endpoint and measure response time.
  3. We check the returned scalar against d*G == Q AND against the true d.

Key point: constant response time across growing search spaces is the signature
of a STUB (does no search, O(1) to format JSON), not a solver. A genuine solver
must take longer as the interval grows (~2^(b/2) for kangaroo). The decisive
column is `dG==Q`, not the clock. A tool that fails a trivially-solvable 20-bit
input is not solving anything, however fast it answers.

Usage:  python3 lambda_solver_verifier.py <endpoint_url> [<endpoint_url> ...]
No external deps (stdlib only). SSL verification is disabled deliberately so the
harness works behind TLS-intercepting egress; it does not rely on cert trust.
"""
import hashlib, json, time, urllib.request, random, ssl, sys

# ---- secp256k1 ----
p  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

def inv(a, m): return pow(a, m - 2, m)
def add(P, Q):
    if P is None: return Q
    if Q is None: return P
    x1, y1 = P; x2, y2 = Q
    if x1 == x2 and (y1 + y2) % p == 0: return None
    m = ((3 * x1 * x1) * inv(2 * y1, p)) if P == Q else ((y2 - y1) * inv(x2 - x1, p)); m %= p
    x3 = (m * m - x1 - x2) % p; y3 = (m * (x1 - x3) - y1) % p
    return (x3, y3)
def mul(k, P):
    R = None
    while k:
        if k & 1: R = add(R, P)
        P = add(P, P); k >>= 1
    return R

_ALPH = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
def _b58c(pl):
    chk = hashlib.sha256(hashlib.sha256(pl).digest()).digest()[:4]; full = pl + chk
    num = int.from_bytes(full, 'big'); s = ""
    while num > 0: num, r = divmod(num, 58); s = _ALPH[r] + s
    for b in full:
        if b == 0: s = "1" + s
        else: break
    return s
def _rip(b):
    h = hashlib.new('ripemd160'); h.update(b); return h.digest()
def addr_comp(X, Y):
    pub = (b'\x02' if Y % 2 == 0 else b'\x03') + X.to_bytes(32, 'big')
    return _b58c(b'\x00' + _rip(hashlib.sha256(pub).digest()))

def make_known_keypair(bits):
    d = random.randrange(2 ** (bits - 1), 2 ** bits)
    X, Y = mul(d, (Gx, Gy))
    return d, X, Y, addr_comp(X, Y)

def extract_hex(obj):
    """Pull any returned scalar/key field, whatever the endpoint's schema."""
    for path in [("recovery", "private_key_hex"), ("collapsed_coordinate",),
                 ("private_key_hex",), ("result", "private_key_hex")]:
        cur = obj; ok = True
        for k in path:
            if isinstance(cur, dict) and k in cur: cur = cur[k]
            else: ok = False; break
        if ok and isinstance(cur, str) and cur.strip().lower().startswith("0x"):
            return path[-1], cur.strip()
    return None, None

_CTX = ssl.create_default_context(); _CTX.check_hostname = False; _CTX.verify_mode = ssl.CERT_NONE
def query(endpoint, X, Y, address, bits):
    body = json.dumps({"pub_x": f"{X:064x}", "pub_y": f"{Y:064x}",
                       "address": address, "puzzle_bits": bits}).encode()
    req = urllib.request.Request(endpoint, data=body,
        headers={"Content-Type": "application/json"}, method="POST")
    t0 = time.perf_counter()
    try:
        with urllib.request.urlopen(req, timeout=30, context=_CTX) as r:
            raw = r.read().decode()
        return (time.perf_counter() - t0) * 1000, json.loads(raw)
    except Exception as e:
        return (time.perf_counter() - t0) * 1000, {"_error": str(e)}

def run(endpoints, bit_sizes=(20, 32, 48, 64, 96, 135), seed=1):
    random.seed(seed)
    tests = [(b,) + make_known_keypair(b) for b in bit_sizes]
    any_pass = False
    for ep in endpoints:
        print("=" * 80); print("ENDPOINT", ep); print("=" * 80)
        print(f"{'bits':>5} {'client_ms':>9} {'self_ms':>9} {'returns':>20} {'dG==Q':>6} {'==true_d':>9}")
        for bits, d_true, X, Y, addr in tests:
            ms, resp = query(ep, X, Y, addr, bits)
            if "_error" in resp:
                print(f"{bits:5d} {ms:9.1f}   ERROR {resp['_error'][:40]}"); time.sleep(1.2); continue
            self_ms = resp.get("elapsed_ms") or resp.get("processing_metrics", {}).get("elapsed_ms")
            field, hx = extract_hex(resp)
            dGok = retd = "n/a"
            if hx:
                dv = int(hx, 16) % n
                RX, _ = mul(dv, (Gx, Gy))
                dGok = "YES" if RX == X else "no"
                retd = "YES" if dv == (d_true % n) else "no"
                if dGok == "YES": any_pass = True
            sm = f"{self_ms:9.1f}" if isinstance(self_ms, (int, float)) else f"{'?':>9}"
            print(f"{bits:5d} {ms:9.1f} {sm} {str(field):>20} {dGok:>6} {retd:>9}")
            time.sleep(1.2)
        print()
    print("VERDICT:", "at least one endpoint returned a verifiable key (dG==Q)"
          if any_pass else "NO endpoint returned a single key satisfying d*G==Q — no solving occurred.")

if __name__ == "__main__":
    eps = sys.argv[1:] or [
        "https://5kxnmih7en2cbfjiisgqqnuvci0jprjj.lambda-url.us-west-2.on.aws/",
        "https://fih4fzdlnxkb4d3gn6csh446im0mmwim.lambda-url.us-west-2.on.aws/",
    ]
    run(eps)
