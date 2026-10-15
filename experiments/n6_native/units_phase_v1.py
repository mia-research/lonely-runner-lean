#!/usr/bin/env python3
"""E46: the unit / zero-divisor split with phases, at the coarse shifts of every divisible flank e = 6E of every
SixResidual set in [1,40]. Runner d, s = d mod 6, phase a = floor(d/e) mod 6 (0 for runners slower than the flank;
FreeFlank's (d k + d/e) % 6). Rule: d blocks shift u iff (s u + a) mod 6 in {0, 5}, except a reading exactly at 5/6
(d/e an integer and s u + a = 5 mod 6), which is clear. Control: rule against direct blocking (opening j = uE).
Shift classes: 0; events {1, 5} (units); non-events {2, 3, 4}. For each flank: which runner types block each class
(type = unit/zero-divisor/multiple x slower/faster); whether E45's separation holds (events blocked only by units,
non-events only by zero divisors); and the signature {(s, a)} of the non-flank runners."""
from collections import Counter
rows = [l.rstrip("\n").split("\t") for l in open("six_cascade_observe_v1.tsv")][1:]
def clear(d, e, j): r = d * (6 * j + 1) % (6 * e); return e <= r <= 5 * e
def rule(d, e, u):
    s, a = d % 6, (d // e) % 6
    c = (s * u + a) % 6
    if c == 5 and d % e == 0: return False          # exactly 5/6: clear
    return c in (0, 5)
def rtype(d, e):
    s = d % 6
    kind = "unit" if s in (1, 5) else ("mult" if s == 0 else "zd")
    return kind + ("-slow" if d < e else "-fast")
ctrl = Counter(); who = {"0": Counter(), "event": Counter(), "nonevent": Counter()}; sep = Counter(); flanks = 0
evt_by = Counter(); allblocked = Counter()
for r in rows:
    S = eval(r[0])
    for e in [d for d in S if d % 6 == 0]:
        E = e // 6; flanks += 1
        blk = {}
        for d in S:
            if d == e: continue
            dir_ = {u for u in range(6) if not clear(d, e, u * E)}
            rl = {u for u in range(6) if rule(d, e, u)}
            ctrl[dir_ == rl] += 1
            blk[d] = dir_
        allblocked[set().union(*blk.values()) == set(range(6))] += 1
        ok = True
        for u in range(6):
            cls = "0" if u == 0 else ("event" if u in (1, 5) else "nonevent")
            types = tuple(sorted({rtype(d, e) for d, b in blk.items() if u in b}))
            who[cls][types] += 1
            if cls == "event" and any(rtype(d, e).startswith(("zd", "mult")) for d, b in blk.items() if u in b): ok = False
            if cls == "nonevent" and any(rtype(d, e).startswith("unit") for d, b in blk.items() if u in b): ok = False
            if cls == "event":
                evt_by["only units" if all(rtype(d, e).startswith("unit") for d, b in blk.items() if u in b) else
                       ("only zero divisors / multiples" if not any(rtype(d, e).startswith("unit") for d, b in blk.items() if u in b) else "both")] += 1
        sep["separation holds" if ok else "separation fails"] += 1
print("control (rule == direct):", dict(ctrl))
print("divisible flanks", flanks, "; all coarse shifts blocked:", dict(allblocked))
print("E45 separation at the flank:", dict(sep))
print("event shifts (1, 5) blocked by:", dict(evt_by))
for k in ("0", "event", "nonevent"):
    print(f"shift class {k}: blocking runner types (top):", who[k].most_common(6))
