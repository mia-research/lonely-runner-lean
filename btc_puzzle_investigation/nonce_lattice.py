"""GAP 1 — ECDSA nonce analysis of the 2019 puzzle consolidation sweep.

tx 17e4e323... (block 578732) spent 21 puzzle addresses in one transaction:
inputs 0-13 = SOLVED #65..#130 (private key known), inputs 14-20 = UNSOLVED.
14 known-key signatures let us recover the actual nonces and test the signer's
RNG. If RFC6979 -> provably safe (null). If structured -> transfers to unknowns.

Exact integer only. Legacy P2PKH SIGHASH_ALL sighash reconstructed from raw tx.
"""
import hashlib, json, pickle, hmac
from sig_lib import P, G, add, mul, N_ORD

n = N_ORD

def dsha(b): return hashlib.sha256(hashlib.sha256(b).digest()).digest()

# ---- raw legacy tx parser ----
class R:
    def __init__(s, b): s.b, s.i = b, 0
    def take(s, k): v = s.b[s.i:s.i+k]; s.i += k; return v
    def u(s, k): return int.from_bytes(s.take(k), 'little')
    def varint(s):
        x = s.u(1)
        if x < 0xfd: return x
        if x == 0xfd: return s.u(2)
        if x == 0xfe: return s.u(4)
        return s.u(8)

def parse_tx(raw_hex):
    r = R(bytes.fromhex(raw_hex))
    version = r.take(4)
    nin = r.varint()
    vin = []
    for _ in range(nin):
        prev = r.take(32); vout = r.take(4)
        sl = r.varint(); script = r.take(sl); seq = r.take(4)
        vin.append([prev, vout, script, seq])
    nout = r.varint()
    vout = []
    for _ in range(nout):
        val = r.take(8); sl = r.varint(); spk = r.take(sl)
        vout.append([val, spk])
    locktime = r.take(4)
    return version, vin, vout, locktime

def ser_varint(x):
    if x < 0xfd: return bytes([x])
    if x <= 0xffff: return b'\xfd' + x.to_bytes(2, 'little')
    if x <= 0xffffffff: return b'\xfe' + x.to_bytes(4, 'little')
    return b'\xff' + x.to_bytes(8, 'little')

def legacy_sighash(version, vin, vout, locktime, in_idx, subscript, hashtype=1):
    out = bytearray()
    out += version
    out += ser_varint(len(vin))
    for j, (prev, vout4, script, seq) in enumerate(vin):
        out += prev + vout4
        sc = subscript if j == in_idx else b''
        out += ser_varint(len(sc)) + sc + seq
    out += ser_varint(len(vout))
    for val, spk in vout:
        out += val + ser_varint(len(spk)) + spk
    out += locktime
    out += hashtype.to_bytes(4, 'little')
    return int.from_bytes(dsha(bytes(out)), 'big')

def inv(x, m): return pow(x, -1, m)

def verify_sig(z, r, s, pub_xy):
    w = inv(s, n); u1 = z * w % n; u2 = r * w % n
    Rp = add(mul(u1), mul(u2, pub_xy))
    return Rp is not None and Rp[0] % n == r

def decompress(h):
    pre = int(h[:2], 16); x = int(h[2:], 16)
    y = pow((x*x*x + 7) % P, (P+1)//4, P)
    return (x, y if (y & 1) == (pre & 1) else P - y)

# ---- RFC6979 deterministic nonce (for comparison) ----
def rfc6979_k(d, z):
    h1 = z.to_bytes(32, 'big')
    x = d.to_bytes(32, 'big')
    v = b'\x01' * 32; k = b'\x00' * 32
    k = hmac.new(k, v + b'\x00' + x + h1, hashlib.sha256).digest()
    v = hmac.new(k, v, hashlib.sha256).digest()
    k = hmac.new(k, v + b'\x01' + x + h1, hashlib.sha256).digest()
    v = hmac.new(k, v, hashlib.sha256).digest()
    while True:
        v = hmac.new(k, v, hashlib.sha256).digest()
        cand = int.from_bytes(v, 'big')
        if 1 <= cand < n:
            return cand
        k = hmac.new(k, v + b'\x00', hashlib.sha256).digest()
        v = hmac.new(k, v, hashlib.sha256).digest()

if __name__ == '__main__':
    import csv
    sigs = pickle.load(open('sweep2019_sigs.pkl', 'rb'))
    txd = pickle.load(open('sweep2019_tx.pkl', 'rb'))
    raw = txd['raw']
    prevspk = [bytes.fromhex(vi['prevout']['scriptpubkey']) for vi in txd['vin']]
    version, vin, vout, locktime = parse_tx(raw)

    solved = {}
    with open('puzzles_verified.csv') as f:
        for row in csv.DictReader(f):
            solved[row['address']] = (int(row['puzzle']), int(row['bits']), int(row['private_key'], 16))

    print(f"tx inputs={len(vin)} outputs={len(vout)}")
    recs = []
    for x in sigs:
        i = x['idx']
        z = legacy_sighash(version, vin, vout, locktime, i, prevspk[i], x['sh'])
        pub = decompress(x['pub'])
        ok = verify_sig(z, x['r'], x['s'], pub)
        rec = dict(idx=i, addr=x['addr'], pub=x['pub'], r=x['r'], s=x['s'], z=z, verify=ok)
        if x['addr'] in solved:
            p, b, d = solved[x['addr']]
            rec['puzzle'] = p; rec['d'] = d
            k = (inv(x['s'], n) * (z + x['r'] * d)) % n
            rec['k'] = k
            rec['k_ok'] = (mul(k)[0] % n == x['r'])
            rec['rfc6979'] = (rfc6979_k(d, z) == k)
        recs.append(rec)
    pickle.dump(recs, open('sweep2019_recs.pkl', 'wb'))

    print("\nsighash verification:", sum(r['verify'] for r in recs), "/", len(recs), "valid ECDSA")
    known = [r for r in recs if 'k' in r]
    print("known-key nonces recovered & checked:", sum(r['k_ok'] for r in known), "/", len(known))
    print("\n--- RFC6979 test (THE pivot) ---")
    print("nonces matching RFC6979:", sum(r['rfc6979'] for r in known), "/", len(known))
    print("\n--- recovered nonces (solved puzzles) ---")
    for r in sorted(known, key=lambda r: r['puzzle']):
        print(f"  #{r['puzzle']:<4} k = {r['k']:064x}  ({r['k'].bit_length()} bits)  rfc6979={r['rfc6979']}")
