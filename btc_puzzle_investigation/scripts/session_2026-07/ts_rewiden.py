"""
Re-run ts_sweep's time-seed hypothesis with the ONE parameter our discussion
changed: the window. Keys are created BEFORE funding (block 339085), so the
seed-time can predate ts_sweep's Nov-2014 lower bound. Also removes ts_sweep's
ts%3 MT subsampling (2/3 of its own window was never MT-tested).
Faithful to ts_sweep scheme B (MT + sequential randrange) and scheme A (SHA).
Discriminator: exact match at puzzle 30 (2^-29), verified at 32/35/40.
"""
import csv, hashlib, random, time

keys={}
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f): keys[int(r['puzzle'])]=int(r['private_key'],16)
VERIFY=[30,32,35,40]

def sha(b): return int.from_bytes(hashlib.sha256(b).digest(),'big')

# ---- Scheme B: MT seeded by ts, sequential randrange, FULL (no ts%3), extended window ----
# window: 2014-01-01 .. 2015-01-20  (covers ts_sweep's window fully + 10 months earlier,
#         and removes the ts%3 gap). Discriminator puzzle 30 needs 30 draws/seed.
B_LO, B_HI = 1388534400, 1421712000   # 2014-01-01 .. 2015-01-20  (~33.2M s)
print(f"[Scheme B: MT] window {B_LO}..{B_HI}  ({(B_HI-B_LO)//1000000}M seeds), full (no subsample)")
t=time.time(); mt_hits=[]
for ts in range(B_LO,B_HI):
    random.seed(ts)
    d=None
    for i in range(1,31):
        d=random.randrange(1<<(i-1),1<<i)      # draw for puzzle i; keep last
    if d==keys[30]:
        # decisive at 30 -> verify the rest
        random.seed(ts); full={}
        for i in range(1,41): full[i]=random.randrange(1<<(i-1),1<<i)
        v=[N for N in VERIFY if full[N]==keys[N]]
        mt_hits.append((ts,v)); print(f"  *** MT ts={ts} matches puzzle30; verify {v} ***")
    if (ts-B_LO)%5000000==0 and ts>B_LO:
        print(f"    ...{(ts-B_LO)//1000000}M seeds, {time.time()-t:.0f}s, hits {len(mt_hits)}")
print(f"[Scheme B] done, {time.time()-t:.0f}s, chance-impossible MT hits: {len(mt_hits)}")

# ---- Scheme A: SHA256(str(ts)+str(N)) masked, WIDER window back to 2013 ----
A_LO, A_HI = 1356998400, 1421712000    # 2013-01-01 .. 2015-01-20
print(f"\n[Scheme A: SHA] window {A_LO}..{A_HI}  ({(A_HI-A_LO)//1000000}M)")
t=time.time(); sha_hits=[]
for ts in range(A_LO,A_HI):
    for N in VERIFY:
        w=sha((str(ts)+str(N)).encode())
        if w%(1<<N)==keys[N] or (w%(1<<(N-1)))|(1<<(N-1))==keys[N]:
            sha_hits.append((ts,N)); print(f"  *** SHA ts={ts} puzzle={N} ***")
print(f"[Scheme A] done, {time.time()-t:.0f}s, chance-impossible SHA hits: {len(sha_hits)}")

print("\n=== RESULT ===")
if mt_hits or sha_hits:
    print("HIT(S) FOUND -> extend/verify; potential engine")
else:
    print("No time-seeded MT/SHA scheme reproduces the keys in the extended window either.")
    print("New conditional boundary now covered: MT full 2014-01..2015-01; SHA 2013-01..2015-01.")
    print("Still open: pre-2013 seeds, other PRNG families, other mappings/encodings.")
