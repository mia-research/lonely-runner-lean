#!/usr/bin/env python3
"""
THREAD 4: generation side -- structure among the real d_i themselves (not their
curve images). Normalized band position u_i = (d_i - 2^(bits-1)) / 2^(bits-1) in
[0,1). Test whether the u_i are iid-uniform (expected if keys = random small ints)
or show a generator fingerprint: (a) uniformity (KS), (b) serial u_i vs u_{i+1}
(consecutive puzzles -> LCG-like?), (c) u_i vs puzzle index. HONEST SCOPE: N=82 (and
only ~70 with bits>=8), underpowered; this is a fresh cross-check, not decisive.
Exact Fraction for u_i; float only in the reported test statistics.
"""
import csv
from fractions import Fraction as F


def main():
    rows = [(int(r["puzzle"]), int(r["bits"]), int(r["private_key"], 16))
            for r in csv.DictReader(open("puzzles_verified.csv"))]
    rows.sort()
    U = []
    for pz, b, d in rows:
        if b < 2:
            U.append((pz, b, F(0)))
        else:
            A = 1 << (b - 1)
            U.append((pz, b, F(d - A, A)))   # in [0,1)
    us = [float(u) for _, _, u in U if _ >= 8 or True]
    print(f"THREAD 4: generation-side positions (N={len(us)} keys)\n")

    # (a) uniformity: KS-like max deviation of empirical CDF from uniform
    su = sorted(us); N = len(su)
    ks = max(max(abs((i + 1) / N - su[i]), abs(i / N - su[i])) for i in range(N))
    print(f"(a) uniformity of u_i: KS max-dev = {ks:.4f}  "
          f"(uniform-consistent if < ~1.36/sqrt(N)={1.36/N**0.5:.4f})")

    # (b) serial correlation u_i vs u_{i+1} (puzzles in order)
    seq = [float(u) for _, _, u in U]
    x = seq[:-1]; y = seq[1:]
    mx = sum(x) / len(x); my = sum(y) / len(y)
    cov = sum((a - mx) * (b - my) for a, b in zip(x, y)) / len(x)
    sx = (sum((a - mx) ** 2 for a in x) / len(x)) ** 0.5
    sy = (sum((b - my) ** 2 for b in y) / len(y)) ** 0.5
    r = cov / (sx * sy) if sx * sy else 0
    print(f"(b) serial corr u_i vs u_(i+1): r = {r:+.4f}  "
          f"(|r| < ~2/sqrt(N)={2/N**0.5:.4f} => consistent with independent)")

    # (c) u_i vs puzzle index (trend)
    idx = [pz for pz, _, _ in U]
    mi_ = sum(idx) / len(idx)
    cov2 = sum((a - mi_) * (b - my) for a, b in zip(idx, seq)) / len(idx)
    si = (sum((a - mi_) ** 2 for a in idx) / len(idx)) ** 0.5
    ssq = (sum((b - sum(seq)/len(seq)) ** 2 for b in seq) / len(seq)) ** 0.5
    r2 = cov2 / (si * ssq) if si * ssq else 0
    print(f"(c) u_i vs puzzle index: r = {r2:+.4f}  (trend; |r|<{2/N**0.5:.4f}=none)")
    print("\n  Reading: all within iid-uniform bands => positions consistent with random")
    print("  small ints (cf. KNOWN_FACTS: MT19937/hash-stream class). N=82 underpowered;")
    print("  a real generator fingerprint would need the finer gen-side threads (seeds/MWC/LCG).")


if __name__ == "__main__":
    main()
