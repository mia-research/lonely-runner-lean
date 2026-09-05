"""
Psychology-driven: casual creator, plain seedable PRNG, MEMORABLE explicit seed
(for reproducibility), idiomatic N-bit generation. Test the combos ts_sweep /
seed_brute never did:
  - Python random.seed(s) + getrandbits / randrange   (s = small ints, words, years)
  - Java Random(s) + BigInteger(N,rnd) idiom          (s = small ints)
Discriminator: EXACT match at puzzles 25/30/35/40 (>=2^-24). Any hit is verified
against ALL puzzles before being believed.
"""
import csv, random

known={}
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f): known[int(r['puzzle'])]=int(r['private_key'],16)
CHECK=[25,30,35,40]; NMAX=42
def verify_all(gen):
    return [N for N in known if N in gen and gen[N]==known[N]]

# ---------- Python MT, idiomatic generations ----------
def py_getrandbits(seed):
    random.seed(seed); g={1:1}
    for N in range(2,NMAX+1): g[N]=(1<<(N-1))|random.getrandbits(N-1)
    return g
def py_randrange(seed):
    random.seed(seed); g={}
    for N in range(1,NMAX+1): g[N]=random.randrange(1<<(N-1),1<<N)
    return g
def py_getrandbits_full(seed):   # getrandbits(N) then force top bit
    random.seed(seed); g={}
    for N in range(1,NMAX+1): g[N]=random.getrandbits(N)|(1<<(N-1))
    return g

# ---------- Java java.util.Random + BigInteger(numBits,rnd) ----------
class JavaRandom:
    def __init__(self,seed): self.s=(seed^0x5DEECE66D)&((1<<48)-1)
    def next(self,bits):
        self.s=(self.s*0x5DEECE66D+0xB)&((1<<48)-1)
        r=self.s>>(48-bits)
        return r-(1<<bits) if r>=(1<<(bits-1)) else r     # signed int
    def nextBytes(self,n):
        out=bytearray(n); i=0
        while i<n:
            rnd=self.next(32); k=min(n-i,4)
            for _ in range(k):
                out[i]=rnd&0xff; rnd>>=8; i+=1
        return out
def java_biginteger(rnd,numBits):
    if numBits==0: return 0
    nb=(numBits+7)//8; b=rnd.nextBytes(nb)
    excess=8*nb-numBits; b[0]&=(1<<(8-excess))-1
    v=0
    for x in b: v=(v<<8)|x
    return v
def java_topbit(seed):     # BigInteger(N-1,rnd) with top bit set
    rnd=JavaRandom(seed); g={1:1}
    for N in range(2,NMAX+1): g[N]=(1<<(N-1))|java_biginteger(rnd,N-1)
    return g
def java_nbits_forced(seed):   # BigInteger(N,rnd) | topbit
    rnd=JavaRandom(seed); g={}
    for N in range(1,NMAX+1): g[N]=java_biginteger(rnd,N)|(1<<(N-1))
    return g

METHODS=[("py_getrandbits",py_getrandbits),("py_randrange",py_randrange),
         ("py_getrandbits_full",py_getrandbits_full),
         ("java_topbit",java_topbit),("java_nbits_forced",java_nbits_forced)]

word_seeds=["bitcoin","satoshi","puzzle","btc","key","secret","password","seed",
            "test","challenge","private","2015","2014","lonely","runner"]
int_seeds=list(range(0,1000001))          # 0 .. 1,000,000 memorable/small ints
year_seeds=[20150115,20140101,1421345234] # date-ish
best=(0,None); hits=[]
for name,fn in METHODS:
    for s in int_seeds+word_seeds+year_seeds:
        if name.startswith("java") and not isinstance(s,int): continue
        g=fn(s); m=[N for N in CHECK if N in g and g[N]==known[N]]
        if m:
            allm=verify_all(g)
            hits.append((name,s,m,len(allm)))
            if len(allm)>best[0]: best=(len(allm),(name,s,m))
            if len(m)>=2 or len(allm)>=5:
                print(f"  *** {name} seed={s!r} CHECK-hits={m} total-exact={len(allm)} ***")
print(f"\ntested {len(METHODS)} methods x ~{len(int_seeds)} seeds")
print(f"high-N (>=25) hits total: {len(hits)}")
if best[1]: print(f"best: {best[1][0]} seed={best[1][1][1]!r} matched CHECK {best[1][1][2]}, {best[0]} keys total")
print(">=2 CHECK hits or >=5 total = real engine; isolated single high-N hits = chance (~0.06 expected)")
