#!/usr/bin/env python3
"""Input for seven_class_bb_v1.c (third argument `minimal`: keep only inclusion-minimal good sets, complete for covers): all distinct unit-state masks (good instants) over the instants allowed by
runner 1, plus the class of each instant.  Classes C(c, s0) = {(c, s0 + 7 s1)} (E27).  Usage: out.txt [CMAX]"""
import sys
CM = int(sys.argv[2]) if len(sys.argv) > 2 else 6
exec(open("seven_abstract_v1.py").read().split("units49 =")[0].replace("CMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 6", f"CMAX = {CM}"))
units49 = [r for r in range(1, 49) if r % 7]
m1 = mask(0, FL[0], 1)
R = [b for b in range(len(strategies)) if m1 >> b & 1]
cls = [(strategies[b][0] - 1) * 7 + strategies[b][1] % 7 for b in R]
full = {}
for T in range(49):
    for fl in FL:
        for rho in units49:
            m = mask(T, fl, rho)
            full.setdefault(sum(1 << i for i, b in enumerate(R) if m >> b & 1), (m, rho % 7))
ms = sorted(full)
if len(sys.argv) > 3 and sys.argv[3] == "minimal":
    byp = sorted(ms, key=lambda m: bin(m).count("1"))
    keep = []
    for m in byp:
        if not any((k & m) == k for k in keep): keep.append(m)
    ms = sorted(keep)
sidx = {st: b for b, st in enumerate(strategies)}
def pairs_of(m):
    out = []
    for c in range(1, CM + 1):
        for s0 in range(7):
            out.append(sum(1 << s1 for s1 in range(7) if not (m >> sidx[(c, s0 + 7 * s1)] & 1)))
    return out
with open(sys.argv[1], "w") as f:
    f.write(f"{len(R)} {len(ms)} {CM * 7}\n")
    f.write(" ".join(map(str, cls)) + "\n")
    f.write(" ".join(str(strategies[b][1] // 7) for b in R) + "\n")
    f.write(" ".join(str(strategies[b][0]) for b in R) + "\n")
    for m in ms: f.write(" ".join(str((m >> (64 * w)) & ((1 << 64) - 1)) for w in range(4)) + "\n")
    for m in ms: f.write(" ".join(map(str, pairs_of(full[m][0]))) + "\n")
    f.write(" ".join(str(full[m][1]) for m in ms) + "\n")
print("instants", len(R), "masks", len(ms), "classes", CM * 7)
