"""E137: what the proved instant families settle together on the band (spread in (7, 9]), readings <= 24, and what
remains.  Families (each an instance of a proved Lean theorem, decided exactly at its own instant or cell):
  AP(c), c in {1,3,5,7}: lap assignment k_i = floor(c n_i / 8), n_i = round(s_i), a captured reading on the lap before or
    at; decided by 1-D Helly  -> TwoBlockN.lonely_eight_of_pairwise_laps.
  BLOCK(K, e), K = 1, 2 (two-block, three-block), e any reading: every position (8K+1) d / e in a block [8k+1, 8k+7]
    -> TwoBlockN.lonely_eight_of_blocks.
Also: are the 149 pure crossing-edge sets (E136) all BLOCK(1, .)?  Exact."""
import itertools
from fractions import Fraction as F
from collections import Counter
from ap_pairs_vs_late_v1 import class_status
def block(T, K):
    for e in T:
        if all(1 <= ((8 * K + 1) * d) % (8 * e) * F(1, e) <= 7 for d in T): return e
    return None
cov = Counter(); rem = []; cross149 = Counter()
for T in itertools.combinations(range(1, 25), 7):
    if not (7 * T[0] < T[-1] <= 9 * T[0]): continue
    s = [F(d, T[0]) for d in T]
    st = {c: class_status(s, c) for c in (1, 3, 5, 7)}
    ap = any(v == 'works' for v in st.values())
    b1 = block(T, 1) is not None; b2 = block(T, 2) is not None
    cov[(('AP' if ap else '') + (' B1' if b1 else '') + (' B2' if b2 else '')).strip() or 'none'] += 1
    if set(st.values()) == {'fails: edges cross'}: cross149['two-block' if b1 else ('three-block' if b2 else 'neither')] += 1
    if not (ap or b1 or b2): rem.append((T, tuple(sorted(set(st.values())))))
tot = sum(cov.values())
print("band sets to 24:", tot)
for k, v in sorted(cov.items(), key=lambda kv: -kv[1]): print("  %6d  %s" % (v, k))
print("the 149 pure crossing-edge sets:", dict(cross149))
print("remaining after AP classes + two-block + three-block:", len(rem))
print("  AP failure reasons among them:", Counter(r[1] for r in rem).most_common())
for T, w in rem[:25]: print("   ", T, [round(d / T[0], 3) for d in T], w)
