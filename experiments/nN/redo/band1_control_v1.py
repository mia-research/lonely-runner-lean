"""Positive control for climb_cells_v3 (readings <= 9, bands = 2): every real late climb must appear as a band-1
EVENT cell (a cell where no runner is in the way, reached after d_min set the move to R = 9), with its full cascade
word.  Events whose word contains (1, 1) (d_min setting the move to R = 9) are written to a file by every worker.
Exact."""
import sys, os
from fractions import Fraction as F
from math import floor
import climb_cells_v3 as v3
SINK = 'band1_control_v1.events.txt'
_orig = v3.Search.children
def children(self, st):
    rows, wit, N, p, lab, word = st
    W = [k for k in self.runners if lab[k][0] == 'way']
    if not W and (1, 1) in word:
        with open(SINK, 'a') as f: f.write(repr(word) + '\n')
    return _orig(self, st)
v3.Search.children = children

if __name__ == '__main__':
    from multiprocessing import Pool
    from late_word_validate_v1 import cases
    from arrangement_lib import readings, nd
    if os.path.exists(SINK): os.remove(SINK)
    M = v3.Search(9, 1, None, 2)
    tasks = [c for r in M.roots() for c in M.children(r)]
    with Pool() as pool:
        for _ in pool.imap_unordered(v3.work, [(st, 9, 1, None, 2) for st in tasks]): pass
    events = set(line.strip() for line in open(SINK))
    print(f"band-1 event cells recorded: {len(events)} distinct words")
    def full_word(ds):
        dsorted = sorted(ds); dmin = dsorted[0]; t = F(1, 8 * dmin); w = []
        while True:
            way = [d for d in ds if nd(d * t) < F(1, 8)]
            if not way: return w, 8 * dmin * t
            cand = {d: (F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way}
            d = max(cand, key=lambda x: cand[x]); t = cand[d]; w.append((dsorted.index(d) + 1, floor(d * t)))
    found = miss = 0
    for V, sub in cases:
        ds = readings(V, V.index(sub))
        if max(ds) > 9 * min(ds): continue
        w, R = full_word(ds)
        if repr(w) in events: found += 1
        else: miss += 1; print("MISSING", V, sub, w, R)
    print(f"real late climbs (readings <= 9) whose full cascade word is a band-1 event cell: {found}; missing {miss}")
