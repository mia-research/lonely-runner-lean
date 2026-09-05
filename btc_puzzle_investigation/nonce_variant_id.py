"""Characterize the 14 known nonces: which nonce-derivation scheme produced each?
Goal is IDENTIFICATION of structure in public data, not key recovery.
Try a broad family of deterministic schemes; report which reproduces each k."""
import pickle, hashlib, hmac
from sig_lib import N_ORD
n = N_ORD

def drbg_seq(seed_material, count=8):
    v = b'\x01'*32; k = b'\x00'*32
    k = hmac.new(k, v+b'\x00'+seed_material, hashlib.sha256).digest(); v = hmac.new(k, v, hashlib.sha256).digest()
    k = hmac.new(k, v+b'\x01'+seed_material, hashlib.sha256).digest(); v = hmac.new(k, v, hashlib.sha256).digest()
    out = []
    for _ in range(count):
        v = hmac.new(k, v, hashlib.sha256).digest(); c = int.from_bytes(v, 'big')
        if 1 <= c < n: out.append(c)
        else:
            k = hmac.new(k, v+b'\x00', hashlib.sha256).digest(); v = hmac.new(k, v, hashlib.sha256).digest()
    return out

def identify(d, z, k_obs):
    x = d.to_bytes(32, 'big')
    zr = z.to_bytes(32, 'big'); zmod = (z % n).to_bytes(32, 'big')
    # 1) plain RFC6979 (raw z / reduced z), DRBG index
    for tag, zz in (('rfc6979-rawz', zr), ('rfc6979-modz', zmod)):
        seq = drbg_seq(x + zz)
        if k_obs in seq: return f'{tag}[{seq.index(k_obs)}]'
    # 2) RFC6979 + ndata counter (LE/BE 32B), Bitcoin Core anti-exfil/grind style
    for order in ('little', 'big'):
        for j in range(0, 20):
            nd = j.to_bytes(32, order)
            seq = drbg_seq(x + zr + nd)
            if k_obs in seq: return f'rfc6979+ndata{order[:2].upper()}({j})'
            seq = drbg_seq(x + zmod + nd)
            if k_obs in seq: return f'rfc6979modz+ndata{order[:2].upper()}({j})'
    # 3) naive hash-based nonces
    cands = {
        'sha256(d||z)': int.from_bytes(hashlib.sha256(x+zr).digest(), 'big') % n,
        'sha256(z||d)': int.from_bytes(hashlib.sha256(zr+x).digest(), 'big') % n,
        'hmac(d,z)': int.from_bytes(hmac.new(x, zr, hashlib.sha256).digest(), 'big') % n,
        'sha256(d)': int.from_bytes(hashlib.sha256(x).digest(), 'big') % n,
    }
    for tag, c in cands.items():
        if c == k_obs: return tag
    return None

recs = pickle.load(open('sweep2019_recs.pkl', 'rb'))
known = sorted([r for r in recs if 'k' in r], key=lambda r: r['puzzle'])
print("scheme that reproduces each recovered nonce:")
tally = {}
for r in known:
    tag = identify(r['d'], r['z'], r['k'])
    tally[tag] = tally.get(tag, 0) + 1
    print(f"  #{r['puzzle']:<4} -> {tag}")
print("\ntally:", tally)
