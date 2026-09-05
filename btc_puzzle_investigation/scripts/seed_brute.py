import csv, hashlib, itertools
keys={}
with open("/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv") as f:
    for r in csv.DictReader(f): keys[int(r["puzzle"])]=int(r["private_key"],16)
puz=sorted(keys)
def H(b): return int.from_bytes(hashlib.sha256(b).digest(),"big")
def Hd(b): return int.from_bytes(hashlib.sha256(hashlib.sha256(b).digest()).digest(),"big")
def maskA(w,N): return w % (2**N)                       # low N bits
def maskB(w,N): return (w % (2**(N-1))) | (1<<(N-1))    # low N-1 bits + forced top bit
# schemes: given (seed_bytes, i) -> underlying 256-bit key
def schemes(seed, i):
    si=str(i); yield_list=[]
    return [
      ("sha(seed+str(i))",       H(seed+si.encode())),
      ("sha(str(i)+seed)",       H(si.encode()+seed)),
      ("sha(seed+':'+str(i))",   H(seed+b":"+si.encode())),
      ("sha(seed+i_le4)",        H(seed+i.to_bytes(4,'little'))),
      ("dsha(seed+str(i))",      Hd(seed+si.encode())),
    ]
# seed candidates
str_seeds=[b"",b"0",b"1",b"bitcoin",b"satoshi",b"puzzle",b"password",b"secret",b"seed",b"BTC",b"key",b"private"]
int_seeds=[str(n).encode() for n in range(0,20001)]
noseed=[("sha(str(i))",lambda i:H(str(i).encode())),("sha(i_le4)",lambda i:H(i.to_bytes(4,'little'))),
        ("dsha(str(i))",lambda i:Hd(str(i).encode())),("sha(i_be32)",lambda i:H(i.to_bytes(32,'big')))]

BIGN=[N for N in puz if N>=25]   # matches here are impossible by chance
best={}
def record(tag,seed,N,mask):
    best.setdefault(tag,[]).append((N,seed))
# no-seed brainwallet-of-index
for name,fn in noseed:
    for N in puz:
        w=fn(N)
        if maskA(w,N)==keys[N] or maskB(w,N)==keys[N]:
            record("NOSEED:"+name,b"(none)",N,"?")
# seeded schemes
allseeds=str_seeds+int_seeds
hits=[]
for seed in allseeds:
    for i in puz:
        for tag,w in schemes(seed,i):
            if maskA(w,i)==keys[i] or maskB(w,i)==keys[i]:
                hits.append((i,tag,seed[:20]))
# report: only matches at N>=25 are meaningful
mean_hits=[h for h in hits if h[0]>=25]
print(f"tested {len(allseeds)} seeds x 5 schemes x 2 masks + 4 no-seed schemes, against 82 keys\n")
print(f"NO-SEED (index brainwallet) matches: {dict((k,len(v)) for k,v in best.items()) or 'none'}")
print(f"SEEDED matches at ANY N: {len(hits)}   at N>=25 (chance-impossible): {len(mean_hits)}")
if mean_hits:
    print("  *** REAL HITS (N>=25) ***")
    for N,tag,seed in mean_hits[:20]: print(f"    puzzle {N}: scheme={tag} seed={seed}")
else:
    smallhits=[h for h in hits if h[0]<25]
    print(f"  (only {len(smallhits)} spurious small-N matches, expected by chance for tiny keys)")
    print("  -> no guessable-seed brainwallet scheme generates the puzzle.")
