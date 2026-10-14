"""Spread-grid series (R8_INTEGER_LAW, R7_R8_PAIR_LAW, BLOCK_PUSHOUT_LAW, PREDICTION_SPREAD_GRID) replicated with positions.
BSM engine and snapshot from full_transit_positions_v2 (unchanged).  Per runner at its first isolation time:
  t, d_min, t vs 1/(8 d_min); behind|ahead on the track (labels = speed rank 1..8) and their SLOTS (speed mod 8);
  whether the track neighbours are the speed-neighbours, or the slot-neighbours (slot +-1 mod 8); which gap is 1/8;
  shift from the AP location in laps: (v_j - j) * t."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from math import floor
from collections import Counter
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from full_transit_positions_v2 import first_time, snapshot
def slot(v): return floor(v) % 8 if v.denominator == 1 else None
def row(V, i):
    t = first_time(V, i); s = snapshot(V, i, t)
    dmin = min(abs(V[j] - V[i]) for j in range(8) if j != i)
    b, a = s["behind"], s["ahead"]
    speed_nb = {(i - 1) % 8 + 1, (i + 1) % 8 + 1}
    sl = slot(V[i])
    slot_nb = None if sl is None else {(sl - 1) % 8, (sl + 1) % 8}
    got_slots = {slot(V[j - 1]) for j in b + a}
    return dict(t=t, dmin=dmin, at_bound=(t == 1 / (8 * dmin)), behind=b, ahead=a,
                speed_nbrs=(set(b + a) == speed_nb and len(b) == len(a) == 1),
                slot_nbrs=(slot_nb is not None and got_slots == slot_nb and len(b) == len(a) == 1),
                setter=s["setter"], eight_t=s["eight_t"], ties=s["ties"])
def show(title, configs, detail=True):
    c = Counter()
    print(f"\n=== {title}")
    for V in configs:
        V = [F(v) for v in V]
        rs = [row(V, i) for i in range(8)]
        for r in rs:
            c["runners"] += 1; c["t = 1/(8 d_min)"] += r["at_bound"]
            c["track neighbours = speed-neighbours"] += r["speed_nbrs"]; c["track neighbours = slot-neighbours (mod 8)"] += r["slot_nbrs"]
            c["ties"] += r["ties"]
        if detail:
            print(f"  {[str(v) for v in V]}")
            print("    " + " | ".join(f"r{i+1} t={r['t']} dmin={r['dmin']} {'/'.join(map(str,r['behind']))}|{'/'.join(map(str,r['ahead']))}"
                                     f"{' S' if r['speed_nbrs'] else ''}{' R' if r['slot_nbrs'] else ''}" for i, r in enumerate(rs)))
    print("  tally:", dict(c), "   (S = speed-neighbours either side, R = slot-neighbours either side)")
if __name__ == "__main__":
    show("one runner pushed out: (1..7, x)", [(1,2,3,4,5,6,7,x) for x in (9, 12, 15, 16, 17, 24, 40, 160)])
    show("pair pushed out: (1..6, x-1, x)", [(1,2,3,4,5,6,x-1,x) for x in (10, 13, 16, 24, 160)])
    show("block of three pushed out: (1..5, x-2, x-1, x)", [(1,2,3,4,5,x-2,x-1,x) for x in (11, 14, 16, 32)])
    show("spread block (1..5, 14, 23, 32) and spread grid (1..6, 159, 160)", [(1,2,3,4,5,14,23,32), (1,2,3,4,5,6,159,160)])
    show("spread grid (1..6,159,160) with one of r1..r6 displaced (PREDICTION_SPREAD_GRID)",
         [(1,F(21,10),3,4,5,6,159,160), (1,2,3,4,F(49,10),6,159,160), (F(9,10),2,3,4,5,6,159,160), (1,2,3,4,5,F(61,10),159,160), (1,2,3,4,5,7,159,160)])
    show("integer sweep: (1..7, x), x = 8..40 (tally only)", [(1,2,3,4,5,6,7,x) for x in range(8, 41)], detail=False)
    show("integer sweep: (1..6, x-1, x), x = 8..40 (tally only)", [(1,2,3,4,5,6,x-1,x) for x in range(8, 41)], detail=False)
    show("integer sweep: (1..5, x-2, x-1, x), x = 8..40 (tally only)", [(1,2,3,4,5,x-2,x-1,x) for x in range(8, 41)], detail=False)
