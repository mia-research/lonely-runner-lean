"""Pure-math discovery — the provenance of the secp256k1 generator G.
G's derivation was never publicly documented (unlike Ed25519 etc.). Probe whether
G has any recoverable origin structure: (1) is G a SMALL multiple of the curve's
smallest point P1=(1,sqrt8)? (2) is Gx a simple hash of an obvious seed?
Exact integers; bounded search (finds a deliberate small/structured choice, not chance)."""
import hashlib
p  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
b = 7
def inv(x): return pow(x % p, -1, p)
def add(A, B):
    if A is None: return B
    if B is None: return A
    x1, y1 = A; x2, y2 = B
    if x1 == x2 and (y1+y2) % p == 0: return None
    m = (3*x1*x1)*inv(2*y1) % p if A == B else (y2-y1)*inv(x2-x1) % p
    x3 = (m*m - x1 - x2) % p
    return (x3, (m*(x1-x3)-y1) % p)

def sqrt_p(a):
    r = pow(a % p, (p+1)//4, p); return r if r*r % p == a % p else None

# smallest curve point P1 = (1, sqrt(8))
y1 = sqrt_p(1 + b); P1 = (1, y1)
print(f"smallest point P1 = (1, {hex(y1)[:16]}..),  on curve: {(y1*y1-1-b)%p==0}")

# (1) is G a small multiple of P1?  iterate [k]P1, check x == Gx, up to K
K = 3_000_000
print(f"\n=== is G = [k]*P1 for small k (search k<{K:,})? ===")
cur = None; found = None
for k in range(1, K+1):
    cur = add(cur, P1)
    if cur is None: break
    if cur[0] == Gx:
        found = k; break
print(f"  {'FOUND: G = [%d]*P1' % found if found else 'no small k up to %d -- G is NOT a small multiple of P1' % K}")

# also the reverse: is P1 a small multiple of G? (small dlog of P1 base G)
cur = None; found2 = None
gg = (Gx, Gy)
for k in range(1, 200000):
    cur = add(cur, gg)
    if cur is None: break
    if cur[0] == 1:                       # P1 has x=1
        found2 = k; break
print(f"  reverse: P1 = [{found2}]*G" if found2 else f"  reverse: P1 is not [k]G for k<200000")

# (2) is Gx a hash of an obvious seed?
print(f"\n=== is Gx a simple hash of an obvious seed? ===")
seeds = [b"Bitcoin", b"bitcoin", b"secp256k1", b"Satoshi", b"Satoshi Nakamoto",
         b"Certicom", b"SEC", b"", b"0", b"1", b"G", b"generator"]
hit = False
for s in seeds:
    for algo in ("sha256", "sha512"):
        h = hashlib.new(algo, s).digest()[:32]
        if int.from_bytes(h, "big") % p == Gx: print(f"  HIT: Gx == {algo}({s})"); hit = True
if not hit: print(f"  none of {len(seeds)} obvious seeds x2 hashes give Gx")

print(f"\nverdict: G's origin shows no small-multiple or obvious-hash structure ⇒")
print(f"  consistent with an undocumented/arbitrary choice; no recoverable provenance in this search.")
