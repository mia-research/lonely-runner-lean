import csv, hashlib, urllib.request, json, time, ssl
from math import gcd
from ecdsa.ecdsa import generator_secp256k1
G=generator_secp256k1
ctx=ssl.create_default_context(); ctx.check_hostname=False; ctx.verify_mode=ssl.CERT_NONE
def get(u):
    r=urllib.request.Request(u,headers={"User-Agent":"r"})
    for _ in range(4):
        try: return json.load(urllib.request.urlopen(r,timeout=20,context=ctx))
        except Exception as e: last=e; time.sleep(2)
    return None
B58="123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
def b58c(p):
    c=hashlib.sha256(hashlib.sha256(p).digest()).digest()[:4];n=int.from_bytes(p+c,"big");s=""
    while n>0:n,r=divmod(n,58);s=B58[r]+s
    return "1"*(len(p)-len(p.lstrip(b'\0')))+s
def h160(b):return hashlib.new("ripemd160",hashlib.sha256(b).digest()).digest()
def compaddr(X,Y):
    pre=b"\x02" if Y%2==0 else b"\x03"; return b58c(b"\x00"+h160(pre+X.to_bytes(32,"big")))
# starting private keys (to be re-verified, not trusted)
src={}
with open("/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/solved_puzzles_xy.csv") as f:
    for r in csv.DictReader(f): src[int(r["puzzle_num"])]=int(r["private_key"],16)
def best_nk(u):
    best=None
    for n in range(2,257):
        k=round(u*n)
        if k<0 or k>n or gcd(k,n)!=1: 
            # nearest coprime
            cs=[kk for kk in range(1,n) if gcd(kk,n)==1]
            if not cs: continue
            k=min(cs,key=lambda kk:abs(u-kk/n))
        e=abs(u-k/n)
        if best is None or e<best[0]: best=(e,n,k)
    return best[1],best[2]
out=[]; verified=0; mismatch=0
for pz in sorted(src):
    d=src[pz]; P=d*G; X,Y=P.x(),P.y(); bits=d.bit_length()
    addr=compaddr(X,Y)
    txs=get(f"https://blockstream.info/api/address/{addr}/txs")
    fund=rev=0; onchain_pk_x=None
    if txs:
        for tx in sorted(txs,key=lambda t:t.get("status",{}).get("block_height",0)):
            h=tx.get("status",{}).get("block_height",0)
            if any(o.get("scriptpubkey_address")==addr for o in tx.get("vout",[])) and not fund: fund=h
            for vin in tx.get("vin",[]):
                if (vin.get("prevout") or {}).get("scriptpubkey_address")==addr:
                    if not rev: rev=h
                    for p in (vin.get("scriptsig_asm","") or "").split():
                        if (p.startswith("02") or p.startswith("03")) and len(p)==66:
                            onchain_pk_x=int(p[2:],16)
                        elif p.startswith("04") and len(p)==130:
                            onchain_pk_x=int(p[2:66],16)
    match = (onchain_pk_x==X) if onchain_pk_x is not None else None
    if match is True: verified+=1
    if match is False: mismatch+=1
    u=(d-2**(bits-1))/2**(bits-1)
    n,k=best_nk(u)
    out.append([pz,bits,f"{d:x}",f"{X:x}",f"{Y:x}",addr,fund,rev,
                ("Y" if match else ("N" if match is False else "no_pubkey")),f"{u:.6f}",n,k])
    time.sleep(0.03)
with open("/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv","w",newline="") as f:
    w=csv.writer(f); w.writerow(["puzzle","bits","private_key","X","Y","address","funding_block","reveal_block","onchain_pubkey_matches_our_X","u_position","n","k"]); w.writerows(out)
print(f"wrote {len(out)} rows to puzzles_verified.csv")
print(f"on-chain pubkey verification: {verified} MATCH our computed X, {mismatch} mismatch, {len(out)-verified-mismatch} no revealed pubkey")
print(f"funding blocks seen: {sorted(set(r[6] for r in out))[:6]}... ")
print("sample rows:")
for r in out[:3]+out[-3:]:
    print(f"  pz{r[0]:>3} bits={r[1]:>3} addr={r[5]} fund={r[6]} rev={r[7]} pkmatch={r[8]} u={r[9]} n={r[10]} k={r[11]}")
