#!/usr/bin/env python3
"""Minimal masks of seven_abstract_v1.py rewritten as six c-blocks (35 runner-1 instants each)."""
import pickle, sys
d = pickle.load(open(sys.argv[1], "rb")); R = d["R"]
exec(open("seven_abstract_v1.py").read().split("units49 =")[0].replace("CMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 6", "CMAX = 6"))
blocks = [[i for i, b in enumerate(R) if strategies[b][0] == c] for c in range(1, 7)]
assert all(len(bl) == 35 for bl in blocks)
with open(sys.argv[2], "w") as f:
    f.write(f"{len(d['minimal'])}\n")
    for m, _ in d["minimal"]:
        f.write(" ".join(str(sum(1 << t for t, i in enumerate(bl) if m >> i & 1)) for bl in blocks) + "\n")
