import csv
from fractions import Fraction as F
from collections import Counter, defaultdict
rows = list(csv.DictReader(open("out_full_transit_positions_v2.csv")))
AP = {m: m for m in range(1, 9)}
byconf = defaultdict(dict)
for r in rows: byconf[(int(r["mover"]), r["r"])][int(r["runner"])] = r
pair = Counter(); size = defaultdict(Counter)
for (m, rv), R in byconf.items():
    dev = F(rv) - m
    if dev == 0: continue
    nb = m + 1 if dev > 0 else m - 1                      # the neighbour approached (on the speed line)
    if nb in (0, 9): continue
    a, b = R[m], R[nb]
    same_t = a["t"] == b["t"]
    mutual = (dev > 0 and a["ahead"] == str(nb) and b["behind"] == str(m) and "ahead" in a["setter"] and "behind" in b["setter"]) or \
             (dev < 0 and a["behind"] == str(nb) and b["ahead"] == str(m) and "behind" in a["setter"] and "ahead" in b["setter"])
    bucket = min(int(abs(dev) * 10), 9) / 10
    size[bucket]["pairs"] += 1
    size[bucket]["mover and approached neighbour share the time"] += same_t
    size[bucket]["... each is the other's flank at exactly 1/8"] += same_t and mutual
    size[bucket]["t = 1/(8*|gap between them|)"] += same_t and F(a["t"]) == 1 / (8 * abs(F(rv) - nb))
    for x in (a, b):
        sn = {str((int(x["runner"]) - 2) % 8 + 1), str(int(x["runner"]) % 8 + 1)}
        size[bucket]["pair members flanked by speed-neighbours"] += {x["behind"], x["ahead"]} == sn
print("mover + the neighbour it approaches (interior movers and ends where the neighbour exists), by |deviation|:")
for k in sorted(size): print(f"  |dev| in [{k:.1f},{k+0.1:.1f}): {dict(size[k])}")
