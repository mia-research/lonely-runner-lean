"""On-chain ECDSA signature extraction for the BTC puzzle exposed keys.
Exact integer only. secp256k1 primitives reused from puzzle_kangaroo_distributed."""
import hashlib, json, time
from puzzle_kangaroo_distributed import P, G, add, mul, decompress

N_ORD = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

def sha256(b): return hashlib.sha256(b).digest()
def hash160(b): return hashlib.new('ripemd160', sha256(b)).digest()
_B58 = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
def b58check(payload):
    chk = sha256(sha256(payload))[:4]
    n = int.from_bytes(payload + chk, 'big')
    s = ''
    while n: n, r = divmod(n, 58); s = _B58[r] + s
    return '1' * (len(payload+chk) - len((payload+chk).lstrip(b'\x00'))) + s
def pub_to_addr(pub_hex):
    return b58check(b'\x00' + hash160(bytes.fromhex(pub_hex)))
def compress_pub(X, Y):
    return f"{2 + (Y & 1):02x}{X:064x}"


import subprocess
def api(path, base="https://blockstream.info/api"):
    for attempt in range(4):
        try:
            out = subprocess.run(["curl","-s","--max-time","30", base+path],
                                 capture_output=True, text=True, timeout=40)
            if out.returncode == 0 and out.stdout:
                return out.stdout
        except Exception:
            pass
        time.sleep(2)
    raise RuntimeError("api fail: "+path)
