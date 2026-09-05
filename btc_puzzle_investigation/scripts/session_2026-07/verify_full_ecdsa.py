"""
Remove the last sampled step: run the INDEPENDENT ecdsa-library point-mult and
address derivation on EVERY one of the 100,023 rows (no sampling anywhere).
"""
import csv, hashlib, base58
from ecdsa import SigningKey, SECP256k1

def ecdsa_xy(d):
    p=SigningKey.from_secret_exponent(d,curve=SECP256k1).get_verifying_key().pubkey.point
    return p.x(),p.y()
def addr_indep(X,Y):
    pk=(b'\x02' if Y%2==0 else b'\x03')+X.to_bytes(32,'big')
    h=hashlib.new('ripemd160',hashlib.sha256(pk).digest()).digest()
    v=b'\x00'+h; return base58.b58encode(v+hashlib.sha256(hashlib.sha256(v).digest()).digest()[:4]).decode()

F="/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/constructed_keys_1to160_100k.csv"
xy_ok=addr_ok=T=0; fails=[]
with open(F) as f:
    for r in csv.DictReader(f):
        d=int(r['d']); X=int(r['X'],16); Y=int(r['Y'],16); T+=1
        ex,ey=ecdsa_xy(d)
        if ex==X and ey==Y: xy_ok+=1
        else: fails.append(('xy',d))
        if addr_indep(X,Y)==r['address']: addr_ok+=1
        else: fails.append(('addr',d))
        if T%20000==0: print(f"  ...{T} rows checked")
print(f"\nFULL independent ecdsa check on ALL {T} rows:")
print(f"  ecdsa(d)*G == file (X,Y): {xy_ok}/{T}")
print(f"  independent address == file: {addr_ok}/{T}")
print("  FAILURES:", fails[:10] if fails else "NONE -- every single row independently confirmed")
