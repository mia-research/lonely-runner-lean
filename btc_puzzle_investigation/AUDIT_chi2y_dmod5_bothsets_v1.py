#!/usr/bin/env python3
"""
Drill follow-up on the buried positive: chi2(y) -> d mod 5 (secp-82: MI=0.17,
perm-p=0.0013, Holm-24 survivor). Test the MATCHED, high-power OOS control:
the constructed known-generator set (same select-bitlen->curve pipeline,
range-structured keys) at N up to 100k. Rule: run on BOTH sets.

chi2(y) = 0 if y is a QR mod p else 1  (the exact F6 of the frozen features()).
No scalar mult needed: both CSVs carry Y directly. Exact int; MI(float) is a
monotone statistic vs an integer-count permutation null (permitted carve-out).
"""
import csv, math, random
from collections import Counter

P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

def chi2y(y):
    return 0 if pow(y, (P - 1) // 2, P) == 1 else 1

def H(counter, N):
    return -sum((c / N) * math.log2(c / N) for c in counter.values() if c)

def mi(xs, ts):
    N = len(xs)
    return H(Counter(xs), N) + H(Counter(ts), N) - H(Counter(zip(xs, ts)), N)

def perm_p(xs, ts, R, seed):
    obs = mi(xs, ts); rng = random.Random(seed); t = list(ts); ge = 0; vs = []
    for _ in range(R):
        rng.shuffle(t); v = mi(xs, t); vs.append(v)
        if v >= obs - 1e-15: ge += 1
    mu = sum(vs) / R; sd = (sum((v - mu) ** 2 for v in vs) / R) ** 0.5
    return obs, (ge + 1) / (R + 1), ((obs - mu) / sd if sd else 0.0)

def load(path, dcol, ycol, limit=None):
    ds, ys = [], []
    with open(path, newline="") as f:
        for i, r in enumerate(csv.DictReader(f)):
            if limit and i >= limit: break
            d = (r.get(dcol) or r.get("private_key") or "").strip()
            y = (r.get(ycol) or "").strip()
            if not d or not y: continue
            if d.lower().startswith("0x"):
                d = int(d, 16)
            elif len(d) > 12 and any(c in "abcdefABCDEF" for c in d):
                d = int(d, 16)
            else:
                d = int(d)
            ds.append(d); ys.append(int(y, 16))
    return ds, ys

def run(name, ds, ys, R=20000):
    fs = [chi2y(y) for y in ys]
    N = len(ds)
    print(f"\n### {name}  N={N}   Pr[chi2y=1]={sum(fs)/N:.4f}")
    for m in (2, 3, 4, 5, 7):
        ts = [d % m for d in ds]
        obs, p, z = perm_p(fs, ts, R, 424242 + m)
        flag = "  <--" if p < 0.01 else ("  <" if p < 0.05 else "")
        print(f"  chi2y -> d mod {m}:  MI={obs:.5f}  perm_p={p:.4f}  z={z:+.2f}{flag}")
    # show the 2x5 contingency proportions for d mod 5
    ts5 = [d % 5 for d in ds]
    tab = {(f, t): 0 for f in (0, 1) for t in range(5)}
    for f, t in zip(fs, ts5): tab[(f, t)] += 1
    print("  d mod 5 contingency [chi2y=0 row / =1 row], col=residue 0..4:")
    for f in (0, 1):
        row = [tab[(f, t)] for t in range(5)]
        tot = sum(row) or 1
        print(f"    f={f}: counts={row}  props={[round(c/tot,3) for c in row]}")

if __name__ == "__main__":
    # real 82 (holdout)
    ds, ys = load("solved_puzzles_xy.csv", "private_key", "Y")
    run("REAL secp-82 (solved puzzles)", ds, ys, R=50000)
    # constructed known-generator, matched range structure, high power
    for lim in (20000, 100000):
        dc, yc = load("constructed_keys_1to160_100k_exact.csv", "d", "Y", limit=lim)
        run(f"CONSTRUCTED known-generator (matched pipeline), first {lim}", dc, yc, R=20000)
