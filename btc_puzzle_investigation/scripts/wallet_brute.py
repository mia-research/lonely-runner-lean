import hashlib, hmac, csv
from ecdsa.ecdsa import generator_secp256k1
G=generator_secp256k1; ORDER=G.order()
keys={}
with open("/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv") as f:
    for r in csv.DictReader(f): keys[int(r["puzzle"])]=int(r["private_key"],16)
puz=sorted(keys)
def hit(w,N): return (w%(2**N)==keys[N]) or ((w%(2**(N-1)))|(1<<(N-1))==keys[N])
found=[]
# ---------- Electrum v1 ----------
def ev1_master(seed):
    old=seed.encode() if isinstance(seed,str) else seed; s=old
    for _ in range(100000): s=hashlib.sha256(s+old).digest()
    return int.from_bytes(s,'big')%ORDER
def ev1_key(m,mpk,n,fc):
    z=int.from_bytes(hashlib.sha256(hashlib.sha256(("%d:%d:"%(n,fc)).encode()+mpk).digest()).digest(),'big')
    return (m+z)%ORDER
ev1_seeds=["","0","1","2","bitcoin","satoshi","password","seed","puzzle","test","electrum","secret",
 "key","btc","abc","hello","0000000000000000","1111111111111111","1234567890abcdef",
 "00000000000000000000000000000000","deadbeefdeadbeefdeadbeefdeadbeef","ffffffffffffffffffffffffffffffff"]
ecount=0
for seed in ev1_seeds:
    m=ev1_master(seed); P=m*G; mpk=P.x().to_bytes(32,'big')+P.y().to_bytes(32,'big')
    for off in (0,-1,1):
        for fc in (0,1):
            for N in puz:
                idx=N+off
                if idx<0: continue
                w=ev1_key(m,mpk,idx,fc); ecount+=1
                if hit(w,N) and N>=25: found.append(("EV1",seed,off,fc,N))
print(f"Electrum-v1: {len(ev1_seeds)} seeds tested, {ecount} derivations")
# ---------- BIP32 ----------
def ser_p(k):
    P=k*G; return (b'\x02' if P.y()%2==0 else b'\x03')+P.x().to_bytes(32,'big')
def ckd(k,c,i):
    data=(b'\x00'+k.to_bytes(32,'big') if i&0x80000000 else ser_p(k))+i.to_bytes(4,'big')
    I=hmac.new(c,data,hashlib.sha512).digest()
    return (int.from_bytes(I[:32],'big')+k)%ORDER, I[32:]
def bip32_master(mn,pw=""):
    seed=hashlib.pbkdf2_hmac('sha512',mn.encode(),("mnemonic"+pw).encode(),2048)
    I=hmac.new(b'Bitcoin seed',seed,hashlib.sha512).digest()
    return int.from_bytes(I[:32],'big'),I[32:]
H=0x80000000
mns=["abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about",
     "legal winner thank year wave sausage worth useful legal winner thank yellow",
     "letter advice cage absurd amount doctor acoustic avoid letter advice cage above",
     "zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo wrong"]
paths=[[],[0],[H],[H,0],[44|H,0|H,0|H,0],[0,0]]
bcount=0
for mn in mns:
    mk,mc=bip32_master(mn)
    for path in paths:
        k,c=mk,mc
        try:
            for idx in path: k,c=ckd(k,c,idx)
        except Exception: continue
        for N in puz:
            kk,cc=ckd(k,c,N); bcount+=1
            if hit(kk,N) and N>=25: found.append(("BIP32",mn[:15],path,N))
            kk2,_=ckd(k,c,N-1)
            if hit(kk2,N) and N>=25: found.append(("BIP32off",mn[:15],path,N))
print(f"BIP32: {len(mns)} mnemonics x {len(paths)} paths, {bcount} derivations")
real=[f for f in found if f[-1]>=25]
print(f"\nchance-impossible hits (N>=25): {len(real)}")
if real:
    print("  *** JACKPOT ***"); [print("   ",x) for x in real[:10]]
else:
    print("  -> neither Electrum-v1 (guessable seeds) nor BIP32 (common mnemonics) generates the keys.")
