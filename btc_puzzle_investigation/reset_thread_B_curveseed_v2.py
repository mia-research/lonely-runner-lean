#!/usr/bin/env python3
"""
Reset thread B, v2 -- RETRACTION + honest bounded search.

v1 tested 21 seeds x 4 recipes and I wrote it up as "no MT19937 seeded by a curve
constant reproduces the keys." That is NOT proven: 21 seeds is a pinprick in an
unbounded space (Python seeds MT19937 via init_by_array on an arbitrary int, so the
seed space is infinite). This version runs a LARGE bounded search over the seed
CLASSES that actually matter and states the result as bounded, never as absence.

Seed classes:
  - small integers 0 .. 2^22
  - 2015 wall-clock unix seconds (puzzle funded block 339085 = 15 Jan 2015 ~ 1.4213e9)
  - curve constants + their sha256 + string hashes (v1 set)
Recipe: getrandbits_seq (the natural per-key bit draw), forward order.
Metric: longest exact prefix from key 1 (a real hit needs prefix >= ~12).
"""
import hashlib, random, time
from reset_common import load_solved, contiguous_run
from ecc_secp256k1 import N_ORDER as n, P as p, Gx, Gy

solved = load_solved()
RUN = contiguous_run(solved, 1)
LOW = {N: solved[N]["d"] & ((1<<(N-1))-1) for N in RUN}   # target low bits
PRUNE_TO = 12   # a wrong seed almost never matches keys 1..12 (sum widths = 66 bits)

def prefix_len(seed):
    r = random.Random(seed)
    pre = 0
    for N in RUN:
        w = N-1
        low = r.getrandbits(w) if w>0 else 0
        if low == LOW[N]:
            pre += 1
        else:
            return pre
    return pre

def scan(seeds, label, report_every=0):
    best = (0, None); t0=time.time(); cnt=0
    for sd in seeds:
        pre = prefix_len(sd)
        cnt += 1
        if pre > best[0]:
            best = (pre, sd)
            if pre >= PRUNE_TO:
                print(f"   !!! {label}: prefix {pre} at seed {sd}")
    print(f"  {label}: scanned {cnt} seeds in {time.time()-t0:.1f}s; best prefix {best[0]} (seed {best[1]})")
    return best

def h_int(x):
    b=int(x).to_bytes((int(x).bit_length()+7)//8 or 1,"big"); return int(hashlib.sha256(b).hexdigest(),16)
def h_str(s): return int(hashlib.sha256(s.encode()).hexdigest(),16)

print("=== Thread B v2: large BOUNDED MT19937 seed search (not a proof of absence) ===")
print(f"prune/hit threshold: prefix >= {PRUNE_TO}\n")

# baseline: what prefix does a random seed reach? (context for 'best prefix' numbers)
rng=random.Random(7); base=[prefix_len(rng.randrange(1<<40)) for _ in range(200000)]
from collections import Counter
c=Counter(base)
print(f"null (200k random seeds): prefix distribution {dict(sorted(c.items()))}; max {max(base)}")
print(f"  -> any real seed class must beat this max ({max(base)}) to be interesting.\n")

overall = (0, None)
# class 1: small integers
b1 = scan(range(0, 1<<22), "small ints 0..2^22")
# class 2: 2015 unix-second timestamps (Dec 2014 .. Mar 2015)
b2 = scan(range(1419000000, 1425000000, 1), "2015 unix seconds")   # ~6M
# class 3: curve constants + hashes
CURVE = [n,p,Gx,Gy,p+1-n, h_int(n),h_int(p),h_int(Gx),h_int(Gy),
         h_str("secp256k1"),h_str("bitcoin"),h_str("puzzle"),
         n&((1<<64)-1), p&((1<<64)-1), Gx&((1<<64)-1)]
b3 = scan(CURVE, "curve constants+hashes")

best = max([b1,b2,b3])
print(f"\nBEST prefix over all classes: {best[0]} (seed {best[1]})")
print(f"null max was {max(base)}.")
if best[0] > max(base)+2:
    print("  -> EXCEEDS null: worth a full-70 check.")
else:
    print("  -> within null band. SCOPED RESULT: none of the ~10M seeds in these")
    print("     three classes (small ints, 2015 timestamps, curve constants) under")
    print("     the getrandbits_seq recipe reproduce the keys beyond chance. This is")
    print("     a BOUNDED search over an UNBOUNDED seed space -- not a proof of absence,")
    print("     and it does not touch other recipes/orders or non-MT generators.")
