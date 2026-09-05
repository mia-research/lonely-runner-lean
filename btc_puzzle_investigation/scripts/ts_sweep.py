import csv, hashlib, random, time
keys={}
with open("/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv") as f:
    for r in csv.DictReader(f): keys[int(r["puzzle"])]=int(r["private_key"],16)
# window: Nov 1 2014 -> Jan 20 2015 (around funding block 339085)
t0=1414800000; t1=1421712000   # ~6.9M seconds
CHECK=[30,32,35,40]  # high-N keys: a match here is chance-impossible (<=2^-30)
def sha(b): return int.from_bytes(hashlib.sha256(b).digest(),"big")
hits=[]; t=time.time()
count=0
for ts in range(t0,t1):
    count+=1
    # scheme A: SHA256(str(ts)+str(i)) masked
    for N in CHECK:
        w=sha((str(ts)+str(N)).encode())
        if w%(2**N)==keys[N] or (w%(2**(N-1)))|(1<<(N-1))==keys[N]:
            hits.append(("shaTS",ts,N)); 
    # scheme B: python MT seeded with ts, sequential randrange per puzzle 1..40
    if ts % 3 == 0:   # subsample MT (heavier) to keep runtime bounded
        random.seed(ts)
        for i in range(1,41):
            k=random.randrange(2**(i-1),2**i)
            if i in CHECK and k==keys[i]: hits.append(("mtTS",ts,i))
    if count%1500000==0: print(f"  ...{count} seconds scanned, {time.time()-t:.0f}s elapsed, hits so far {len(hits)}")
print(f"\nscanned {count} timestamps ({t0}..{t1}), schemes: SHA256(ts+i) + MT-sequential")
real=[h for h in hits if h[2]>=25]
print(f"chance-impossible hits (N>=25): {len(real)}")
if real:
    print("  *** JACKPOT ***"); 
    for s,ts,N in real[:10]: print(f"    scheme={s} timestamp={ts} ({time.strftime('%Y-%m-%d %H:%M',time.gmtime(ts))}) puzzle={N}")
else:
    print("  -> no time-seeded (SHA256-timestamp or MT) scheme in this window generates the keys.")
