"""
Forward-engine reconstruction: assume key_i was generated at block-339085 time
from public data available then. Search (seed x PRNG x mapping); regenerate the
sequence; check EXACT matches vs the 82 known keys. Discriminator = exact hits
at puzzles >=15 (chance ~2^-14 each). Any config with >=2 such hits = the engine.
Data: btc_puzzle_investigation/puzzles_verified.csv (folder only).
"""
import csv, hashlib, random

# ---- known keys ----
known={}
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        known[int(r['puzzle'])]=int(r['private_key'],16)
CHECK=[p for p in known if known and 8<=p<=45]      # exact-match discriminators
NMAX=45

# ---- block 339085 public data (fetched) ----
B_TIME=1421345234; B_MEDIAN=1421342061; B_NONCE=1164581844; B_BITS=404291887
B_HASH=int("0000000000000000188de542fd76b1676c4be6c380b39ddea119358c290cebd7",16)
B_PREV=int("0000000000000000013aa85f9cc7b6f7ea03c0b9c72fbfa850ab0a5c1813620a",16)
B_MRKL=int("d3f83ca0b0ea91cf932fbdb0e6890a42c10ffa3f35e7463beff8e7f4006af392",16)

# ---- PRNG stream factories: return f(i)->an integer draw for puzzle i ----
def mt_bitstream(seed):
    rng=random.Random(seed)
    def draw(i): return rng.getrandbits(i-1)           # i-1 fresh bits per puzzle
    return draw
def mt_randrange(seed):
    rng=random.Random(seed)
    def draw(i): return rng.randrange(0, 1<<(i-1))
    return draw
def sha_chain(seed):
    st=hashlib.sha256(str(seed).encode()).digest()
    box={'s':st,'buf':b'','ctr':0}
    def draw(i):
        need=(i+7)//8
        while len(box['buf'])<need:
            box['s']=hashlib.sha256(box['s']).digest(); box['buf']+=box['s']
        v=int.from_bytes(box['buf'][:need],'big'); box['buf']=box['buf'][need:]
        return v & ((1<<(i-1))-1)
    return draw
def sha_counter(seed):
    def draw(i):
        h=hashlib.sha256(f"{seed}:{i}".encode()).digest()
        return int.from_bytes(h,'big') & ((1<<(i-1))-1)
    return draw
def lcg_glibc(seed):
    st={'x':seed & 0x7fffffff}
    def draw(i):
        acc=0
        for _ in range((i-1)//31+1):
            st['x']=(1103515245*st['x']+12345)&0x7fffffff; acc=(acc<<31)|st['x']
        return acc & ((1<<(i-1))-1)
    return draw

PRNGS={'MT.getrandbits':mt_bitstream,'MT.randrange':mt_randrange,
       'SHA256chain':sha_chain,'SHA256(seed:i)':sha_counter,'glibcLCG':lcg_glibc}

def gen_seq(factory,seed):
    draw=factory(seed); out={}
    for i in range(1,NMAX+1):
        out[i]=(1<<(i-1)) | draw(i) if i>1 else 1
    return out

def score(seq):
    return [p for p in CHECK if p in seq and seq[p]==known[p]]

# ---- seed candidates ----
block_seeds={'time':B_TIME,'median':B_MEDIAN,'nonce':B_NONCE,'bits':B_BITS,
             'hash':B_HASH,'prevhash':B_PREV,'merkle':B_MRKL,
             'hash&0xffffffff':B_HASH&0xffffffff,'prev&0xffffffff':B_PREV&0xffffffff,
             'height':339085,'prevheight':339084}

print("=== forward-engine search ===")
best=(0,None)
# 1) block-derived integer seeds (NOT covered by ts_sweep)
for sname,seed in block_seeds.items():
    for pname,fac in PRNGS.items():
        try: hits=score(gen_seq(fac,seed))
        except Exception: hits=[]
        if len(hits)>=1: print(f"  seed={sname:16} prng={pname:16} exact-hits@>=8: {hits}")
        if len(hits)>best[0]: best=(len(hits),(sname,pname,hits))

# 2) timestamp window around block time (MT + SHA, mappings ts_sweep may not have)
print("  scanning timestamp window +/-4000s around block time ...")
for seed in range(B_TIME-4000,B_TIME+4001):
    for pname in ('MT.getrandbits','MT.randrange','SHA256(seed:i)'):
        hits=score(gen_seq(PRNGS[pname],seed))
        if len(hits)>=2:
            print(f"  *** ts={seed} prng={pname} hits={hits}")
        if len(hits)>best[0]: best=(len(hits),(f"ts={seed}",pname,hits))

print(f"\nBEST: {best[0]} exact discriminator-hits  ->  {best[1]}")
print("(>=2 hits at puzzles 8-45 would indicate a real engine; 0-1 is chance)")
