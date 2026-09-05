"""Analyze the 14 recovered nonces for exploitable structure.
If any RNG structure is found on the known-key nonces, it transfers to the 7
unknown-key inputs (14-20) in the same transaction. Exact integer only."""
import pickle, hashlib, hmac
from sig_lib import P, G, add, mul, N_ORD
n = N_ORD

def inv(x, m): return pow(x, -1, m)

def rfc6979_variants(d, z):
    """standard (raw 32-byte hash) and RFC-strict (z reduced mod n) nonces."""
    def gen(h1):
        x = d.to_bytes(32, 'big')
        v = b'\x01'*32; k = b'\x00'*32
        k = hmac.new(k, v+b'\x00'+x+h1, hashlib.sha256).digest(); v = hmac.new(k, v, hashlib.sha256).digest()
        k = hmac.new(k, v+b'\x01'+x+h1, hashlib.sha256).digest(); v = hmac.new(k, v, hashlib.sha256).digest()
        seq = []
        for _ in range(6):
            v = hmac.new(k, v, hashlib.sha256).digest()
            c = int.from_bytes(v, 'big')
            if 1 <= c < n: seq.append(c)
            else:
                k = hmac.new(k, v+b'\x00', hashlib.sha256).digest(); v = hmac.new(k, v, hashlib.sha256).digest()
        return seq
    raw = gen(z.to_bytes(32, 'big'))
    strict = gen((z % n).to_bytes(32, 'big'))
    return raw, strict

recs = pickle.load(open('sweep2019_recs.pkl', 'rb'))
known = sorted([r for r in recs if 'k' in r], key=lambda r: r['puzzle'])
ks = [r['k'] for r in known]
labels = [r['puzzle'] for r in known]

print("=== 1. RFC6979 variants: does EITHER convention (or a later candidate) explain all? ===")
for r in known:
    raw, strict = rfc6979_variants(r['d'], r['z'])
    hit = None
    if r['k'] in raw: hit = f"raw[{raw.index(r['k'])}]"
    elif r['k'] in strict: hit = f"strict[{strict.index(r['k'])}]"
    print(f"  #{r['puzzle']:<4} match={hit}")

print("\n=== 2. nonce magnitudes (small-k / truncation leak?) ===")
for r in known:
    k = r['k']; top = k >> (256-8)
    print(f"  #{r['puzzle']:<4} bits={k.bit_length():3d} top8={top:3d} low8={k & 0xff:3d}")

print("\n=== 3. shared high/low bits across all 14 (fixed-prefix RNG?) ===")
for w in (4, 8, 16, 32, 64):
    tops = set(k >> (256-w) for k in ks if k.bit_length() >= 256-3)
    lows = set(k & ((1<<w)-1) for k in ks)
    print(f"  top{w}: {len(tops)} distinct / {len(ks)}   low{w}: {len(lows)} distinct / {len(ks)}")

print("\n=== 4. LCG fit in input order: k_{i+1} = a*k_i + c mod n ? ===")
# solve a,c from first two gaps, verify on rest
def lcg_check(seq):
    if len(seq) < 3: return False
    # a = (k2-k1)/(k1-k0)
    d10 = (seq[1]-seq[0]) % n; d21 = (seq[2]-seq[1]) % n
    if d10 == 0: return False
    a = d21 * inv(d10, n) % n
    c = (seq[1] - a*seq[0]) % n
    ok = all((a*seq[i] + c) % n == seq[i+1] % n for i in range(len(seq)-1))
    return ok, a, c
res = lcg_check(ks)
print("  LCG (puzzle/input order):", res if res else "no fit")

print("\n=== 5. pairwise GCD of nonce differences (shared modulus / structure) ===")
import math
g = 0
for i in range(len(ks)):
    for j in range(i+1, len(ks)):
        g = math.gcd(g, abs(ks[i]-ks[j]))
print("  gcd of all pairwise differences:", g, "(1 or small => no shared structure)")

print("\n=== 6. top-bit balance (bias test) ===")
msb = [ (k >> 255) & 1 for k in ks ]
print("  MSB(bit255):", sum(msb), "ones /", len(ks), "  (RNG ~ half; all-0 => <255-bit bias)")
b2 = [ (k >> 254) & 1 for k in ks ]
print("  bit254:", sum(b2), "ones /", len(ks))
