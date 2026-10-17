#!/bin/sh
# Exact check of the three finite statements named in LonelyRunner/LRC/Spec/OrderSevenAbsN.lean
# (AbsU5, AbsP1, AbsP2).  The mask rule in seven_abstract_v1.py is Lean's `ok`:
# cell = (c*T + g[c-1] + s*c*rho) % 49 in [7, 41]; fvecs = the twelve Farey vectors in the same order.
# Prints "covers 0" lines; any nonzero cover count refutes the statement.  U5 takes ~20 min on 8 cores.
set -e
D=${1:-/tmp/o7abs}; mkdir -p "$D"
cc -O3 -march=native -o "$D/cover" seven_abstract_cover_v1.c
cc -O3 -march=native -o "$D/triples" seven_abstract_triples_v1.c
python3 seven_abstract_v1.py "$D/abs_units.pkl"
python3 - "$D" <<'PY'
import pickle, sys
D = sys.argv[1]
d = pickle.load(open(f"{D}/abs_units.pkl", "rb"))
ms = sorted((m for m, _ in d["minimal"]), key=lambda m: bin(m).count("1"))
with open(f"{D}/u5.txt", "w") as f:
    f.write(f"{len(ms)} {d['nbits']}\n")
    for m in ms: f.write(" ".join(str((m >> (64 * w)) & ((1 << 64) - 1)) for w in range(4)) + "\n")
n = len(ms); tot = sum((n - i) ** 2 for i in range(n)); K = 48; cuts = [0]; acc = 0
for i in range(n):
    acc += (n - i) ** 2
    if acc >= tot * len(cuts) / K and len(cuts) < K: cuts.append(i + 1)
cuts.append(n)
open(f"{D}/chunks.txt", "w").write("\n".join(f"{a} {b}" for a, b in zip(cuts, cuts[1:])) + "\n")
PY
python3 seven_abstract_mixed_v2.py "$D"
echo "== AbsU5"; xargs -P 8 -L 1 "$D/cover" "$D/u5.txt" < "$D/chunks.txt" | awk '{print} /covers/ {split($NF,a," "); c+=$NF} END {print "AbsU5 total covers", c}'
echo "== AbsP1"; "$D/triples" "$D/units.txt" "$D/bases_P1.txt"
echo "== AbsP2"; "$D/triples" "$D/units.txt" "$D/bases_P2.txt"
