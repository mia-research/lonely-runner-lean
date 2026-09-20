"""Is a disturbed runner's time an opening (8k+1)/(8|D|) (or closing (8k-1)/(8|D|)) of its difference D to a mover?
And is a mover's time an opening of its difference to some runner (which one)?"""
import csv
from fractions import Fraction as F
from math import floor
from collections import Counter, defaultdict
AP = [F(k) for k in range(1, 9)]
def kind(D, t):
    x = abs(D) * t; f = x - floor(x)
    return "opening" if f == F(1, 8) else ("closing" if f == F(7, 8) else None)
def analyse(name, rows, getV, getmovers):
    c = Counter(); lap = Counter(); which = Counter()
    for r in rows:
        if r["role"] == "untouched": continue
        V = getV(r); mv = getmovers(r); i = int(r["runner"]) - 1; t = F(r["t"])
        if r["role"] == "disturbed":
            ks = [(m, kind(V[m - 1] - V[i], t)) for m in mv]
            hit = [(m, k) for m, k in ks if k]
            c["disturbed"] += 1
            c["time is an opening of its difference to a mover"] += any(k == "opening" for m, k in hit)
            c["... or a closing"] += any(k == "closing" for m, k in hit) and not any(k == "opening" for m, k in hit)
            for m, k in hit:
                if k == "opening": lap[int(abs(V[m - 1] - V[i]) * t)] += 1; break
        else:
            c["movers"] += 1
            hits = [j + 1 for j in range(8) if j != i and kind(V[j] - V[i], t) == "opening"]
            c["mover time is an opening of some difference"] += bool(hits)
            nb = [x for x in (i, i + 2) if 1 <= x <= 8]
            which["opening of a speed-neighbour" if any(h in nb for h in hits) else ("opening of another runner" if hits else "neither")] += 1
    print(f"{name}: {dict(c)}\n   disturbed: lap k of that opening: {dict(sorted(lap.items()))}\n   movers: {dict(which)}")
ft = list(csv.DictReader(open("out_full_transit_positions_v2.csv")))
def V_ft(r): V = list(AP); V[int(r["mover"]) - 1] = F(r["r"]); return V
analyse("full transit (one mover)", [r for r in ft if F(r["r"]) != int(r["mover"])], V_ft, lambda r: [int(r["mover"])])
rp = list(csv.DictReader(open("out_replications_positions_v2.csv")))
def V_rp(r): return [F(x) for x in r["V"].split()]
analyse("r8 8.1..16.9", [r for r in rp if r["test"] == "R1"], V_rp, lambda r: [int(x) for x in r["movers"].split()])
analyse("two movers", [r for r in rp if r["test"] == "R2"], V_rp, lambda r: [int(x) for x in r["movers"].split()])
