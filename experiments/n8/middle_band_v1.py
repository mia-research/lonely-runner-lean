"""Middle-band cases of the full transit replication: mover and approached neighbour do NOT share the pair's spine
point t_c = 1/(8*gap).  Pure evaluation at named instants (BSM times come from the replication CSV).
At t_c: who is within 1/8 of the mover (in the way), where (eighths, signed), their AP label and shift.
At the mover's actual time t: t/t_c, which instant of the pair's own spine it is (8*gap*t), who sits at exactly 1/8."""
import csv
from fractions import Fraction as F
from math import floor
from collections import Counter, defaultdict
def fr(x): return x - floor(x)
def signed8(x):
    x = fr(x); return 8 * (x if x <= F(1, 2) else x - 1)
rows = list(csv.DictReader(open("out_full_transit_positions_v2.csv")))
conf = defaultdict(dict)
for r in rows: conf[(int(r["mover"]), r["r"])][int(r["runner"])] = r
AP = [F(k) for k in range(1, 9)]
tally = Counter(); inway = Counter(); actual = Counter(); examples = []
for (m, rv), R in sorted(conf.items(), key=lambda x: (x[0][0], F(x[0][1]))):
    V = list(AP); V[m - 1] = F(rv); dev = V[m - 1] - AP[m - 1]
    if dev == 0: continue
    nb = m + 1 if dev > 0 else m - 1
    if nb in (0, 9): continue
    gap = abs(V[m - 1] - V[nb - 1]); tc = 1 / (8 * gap)
    if R[m]["t"] == R[nb]["t"] and F(R[m]["t"]) == tc: continue
    if not (F(3, 10) <= abs(dev) < F(8, 10)): continue
    tally["middle-band cases"] += 1
    i = m - 1
    who = [(j + 1, signed8((V[j] - V[i]) * tc)) for j in range(8) if j != i and abs(signed8((V[j] - V[i]) * tc)) < 1]
    key = []
    for j, p in who:
        rel = j - m
        key.append(f"r{m}{'+' if rel > 0 else ''}{rel}")
    inway[tuple(sorted(key))] += 1
    t = F(R[m]["t"]); k8 = 8 * gap * t
    atq = [j + 1 for j in range(8) if j != i and abs(signed8((V[j] - V[i]) * t)) == 1]
    lab = "on the pair's spine (odd eighth of the pair lap)" if k8.denominator == 1 and k8.numerator % 2 else f"off the pair's spine"
    actual[(lab, tuple(sorted(f"r{m}{'+' if j-m>0 else ''}{j-m}" for j in atq)))] += 1
    if len(examples) < 12 and F(rv) * 100 % 10 == 0:
        examples.append(f"r{m}={rv}: gap {gap}, t_c={tc}; in the way at t_c: " +
                        ", ".join(f"r{j} at {p} eighths (AP shift {8*(V[j-1]-AP[j-1])*tc})" for j, p in who) +
                        f"; actual t={t} = {t/tc} t_c, pair-lap position 8*gap*t={k8}; at exactly 1/8: {atq}")
print(dict(tally))
print("\nrunners in the way of the mover at the pair's spine point (labels relative to the mover):")
for k, v in inway.most_common(12): print(f"   {v:>4}  {k}")
print("\nthe mover's actual time: (relation to the pair's spine, runners at exactly 1/8):")
for k, v in actual.most_common(12): print(f"   {v:>4}  {k}")
print("\nexamples:"); [print("  ", e) for e in examples]
