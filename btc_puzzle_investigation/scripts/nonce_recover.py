import csv, hashlib, urllib.request, json, time, ssl
from ecdsa.ecdsa import generator_secp256k1
G=generator_secp256k1; N=G.order()
ctx=ssl.create_default_context(); ctx.check_hostname=False; ctx.verify_mode=ssl.CERT_NONE
def get(u,txt=False):
    r=urllib.request.Request(u,headers={"User-Agent":"r"})
    for _ in range(4):
        try:
            x=urllib.request.urlopen(r,timeout=20,context=ctx)
            return x.read().decode() if txt else json.load(x)
        except Exception as e: last=e; time.sleep(2)
    return None
def dsha(b): return hashlib.sha256(hashlib.sha256(b).digest()).digest()
def parse_der(h):
    b=bytes.fromhex(h)
    if b[-1] in (1,2,3,0x81,0x82,0x83): b=b[:-1]
    i=2; rl=b[i+1]; r=int.from_bytes(b[i+2:i+2+rl],'big'); j=i+2+rl; sl=b[j+1]; s=int.from_bytes(b[j+2:j+2+sl],'big'); return r,s
def rd_varint(b,p):
    v=b[p]
    if v<0xfd: return v,p+1
    if v==0xfd: return int.from_bytes(b[p+1:p+3],'little'),p+3
    if v==0xfe: return int.from_bytes(b[p+1:p+5],'little'),p+5
    return int.from_bytes(b[p+1:p+9],'little'),p+9
def parse_tx(hx):
    b=bytes.fromhex(hx); p=0; ver=b[p:p+4]; p+=4
    seg=(b[p]==0 and b[p+1]==1)
    if seg: p+=2
    nin,p=rd_varint(b,p); ins=[]
    for _ in range(nin):
        op=b[p:p+36]; p+=36; sl,p=rd_varint(b,p); sig=b[p:p+sl]; p+=sl; seq=b[p:p+4]; p+=4
        ins.append([op,sig,seq])
    nout,p=rd_varint(b,p); outs=[]
    for _ in range(nout):
        val=b[p:p+8]; p+=8; sl,p=rd_varint(b,p); spk=b[p:p+sl]; p+=sl; outs.append(val+bytes([sl])+spk if sl<0xfd else None)
        # store raw
    return ver,ins,outs,b,seg
def legacy_sighash(hx,in_idx,subscript):
    ver,ins,outs,b,seg=parse_tx(hx)
    def vi(n): return bytes([n]) if n<0xfd else b'\xfd'+n.to_bytes(2,'little')
    out=ver+vi(len(ins))
    for j,(op,sig,seq) in enumerate(ins):
        sc=subscript if j==in_idx else b''
        out+=op+vi(len(sc))+sc+seq
    # re-read outputs raw from b (simplest: reserialize from parse). Re-parse outputs properly:
    # redo output parse to get exact bytes
    p=4+(2 if seg else 0)
    ni,p=rd_varint(b,p)
    for _ in range(ni):
        p+=36; sl,p=rd_varint(b,p); p+=sl; p+=4
    no,p=rd_varint(b,p); ostart=p
    for _ in range(no):
        p+=8; sl,p=rd_varint(b,p); p+=sl
    outbytes=b[ostart:p]
    out+=vi(no)+outbytes+b'\x00\x00\x00\x00'+b'\x01\x00\x00\x00'
    return int.from_bytes(dsha(out),'big')
import hashlib as _h
B58="123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
def b58c(p):
    c=_h.sha256(_h.sha256(p).digest()).digest()[:4];n=int.from_bytes(p+c,"big");s=""
    while n>0:n,r=divmod(n,58);s=B58[r]+s
    return "1"*(len(p)-len(p.lstrip(b'\0')))+s
def h160(x):return _h.new("ripemd160",_h.sha256(x).digest()).digest()
def comp_addr(d):
    P=d*G;pre=b"\x02" if P.y()%2==0 else b"\x03";return b58c(b"\x00"+h160(pre+P.x().to_bytes(32,"big")))
keys={}
with open("/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv") as f:
    for r in csv.DictReader(f): keys[int(r["puzzle"])]=int(r["private_key"],16)
nonces=[]
for pz in sorted(keys):
    if pz<20: continue
    d=keys[pz]; a=comp_addr(d); txs=get(f"https://blockstream.info/api/address/{a}/txs")
    if not txs: continue
    for tx in txs:
        idx=None; subscript=None; rs=None
        for i,vin in enumerate(tx.get("vin",[])):
            if (vin.get("prevout") or {}).get("scriptpubkey_address")==a:
                idx=i; spkhex=vin["prevout"]["scriptpubkey"]; subscript=bytes.fromhex(spkhex)
                for pp in (vin.get("scriptsig_asm","") or "").split():
                    if pp.startswith("30") and len(pp)>=140: rs=parse_der(pp)
                break
        if idx is None or rs is None: continue
        hx=get(f"https://blockstream.info/api/tx/{tx['txid']}/hex",txt=True)
        if not hx: continue
        try:
            z=legacy_sighash(hx,idx,subscript)
            r,s=rs; k=((z+r*d)*pow(s,-1,N))%N
            valid=((k*G).x()%N==r)
            nonces.append((pz,k,valid,r))
        except Exception as e: pass
        break
    time.sleep(0.03)
valid=[x for x in nonces if x[2]]
print(f"recovered {len(nonces)} nonces, {len(valid)} self-verify (k*G.x==r)\n")
kb=[k.bit_length() for pz,k,v,r in valid]
from collections import Counter
print(f"nonce bit-lengths: min={min(kb)} max={max(kb)} mean={sum(kb)/len(kb):.1f} (256=full entropy)")
small=[(pz,b) for (pz,k,v,r),b in zip(valid,kb) if b<248]
print(f"suspiciously small nonces (<248 bits): {small}")
# top-byte distribution (bias check)
tops=[k>>248 for pz,k,v,r in valid]
print(f"top-byte spread: {len(set(tops))} distinct of {len(tops)} (uniform if ~equal)")
# any two nonces equal or with small difference?
ks=sorted(k for pz,k,v,r in valid)
mindiff=min(ks[i+1]-ks[i] for i in range(len(ks)-1)) if len(ks)>1 else 0
print(f"min gap between any two nonces: 2^{__import__('math').log2(mindiff):.0f}" if mindiff>0 else "DUPLICATE NONCE!")
