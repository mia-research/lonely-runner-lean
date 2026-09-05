import csv, hashlib, urllib.request, json, time, ssl
from ecdsa.ecdsa import generator_secp256k1
G=generator_secp256k1
ctx=ssl.create_default_context(); ctx.check_hostname=False; ctx.verify_mode=ssl.CERT_NONE
def get(url):
    req=urllib.request.Request(url,headers={"User-Agent":"r"})
    for _ in range(3):
        try: return json.load(urllib.request.urlopen(req,timeout=15,context=ctx))
        except Exception as e: last=e; time.sleep(1.5)
    return None
B58="123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
def b58c(p):
    c=hashlib.sha256(hashlib.sha256(p).digest()).digest()[:4]; num=int.from_bytes(p+c,"big"); s=""
    while num>0: num,r=divmod(num,58); s=B58[r]+s
    return "1"*(len(p)-len(p.lstrip(b'\0')))+s
def h160(b): return hashlib.new("ripemd160",hashlib.sha256(b).digest()).digest()
def comp_addr(k):
    P=k*G; comp=(b"\x02" if P.y()%2==0 else b"\x03")+P.x().to_bytes(32,"big")
    return b58c(b"\x00"+h160(comp))
def parse_der(h):
    b=bytes.fromhex(h)
    if b[-1] in (1,2,3,0x81,0x82,0x83): b=b[:-1]
    if not b or b[0]!=0x30: return None
    try:
        i=2; assert b[i]==2; i+=1; rl=b[i]; i+=1; r=int.from_bytes(b[i:i+rl],'big'); i+=rl
        assert b[i]==2; i+=1; sl=b[i]; i+=1; s=int.from_bytes(b[i:i+sl],'big'); return r,s
    except: return None
keys={}
with open("/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/solved_puzzles_xy.csv") as f:
    for r in csv.DictReader(f): keys[int(r["puzzle_num"])]=int(r["private_key"],16)
sigs=[]
for pz,k in sorted(keys.items()):
    if pz<15: continue
    a=comp_addr(k); txs=get(f"https://blockstream.info/api/address/{a}/txs")
    if not txs: continue
    for tx in txs:
        for vin in tx.get("vin",[]):
            po=vin.get("prevout") or {}
            if po.get("scriptpubkey_address")==a:
                for p in (vin.get("scriptsig_asm","") or "").split():
                    if p.startswith("30") and len(p)>=140:
                        pr=parse_der(p)
                        if pr: sigs.append([pz,tx["txid"],hex(pr[0]),hex(pr[1])])
from collections import Counter
rc=Counter(s[2] for s in sigs)
dups=[r for r,c in rc.items() if c>1]
short=[(s[0],int(s[2],16).bit_length()) for s in sigs if int(s[2],16).bit_length()<248]
out={"n_sigs":len(sigs),"n_puzzles":len(set(s[0] for s in sigs)),
     "reused_r":dups,"short_nonces":short,"sigs":sigs}
json.dump(out,open("/tmp/nonce_results.json","w"))
print("DONE",len(sigs),"sigs,",len(dups),"reused,",len(short),"short")
