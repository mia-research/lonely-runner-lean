"""How far past the first push does the q-rule need to go?

For q, e a multiple of q, write a lap of e as j = i*(e/q) + r, 0 <= r < e/q: the instant
(j + 1/8)/e = i/q + (r + 1/8)/e is the q-gon vertex i/q with the push eps = (r + 1/8)/e.  The rule
(rung_selection_v1) uses r = 0 and e the least multiple of q.  For each hard set: the least r at
which some q <= 8 (e its least multiple, or any multiple) has a lonely opening, and the push in
units of the first push, (8r + 1).
"""
import json, os
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
H = [tuple(S) for S in json.load(open(os.path.join(HERE, 'hard_sets_41_60.json')))]
def lonely(S, e, j): return all(e <= d * (8 * j + 1) % (8 * e) <= 7 * e for d in S)
def least_r(S, flanks):
    best = None
    for q, e in flanks:
        M = e // q
        for r in range(M):
            if any(lonely(S, e, i * M + r) for i in range(q)):
                if best is None or r < best[0]: best = (r, q, e)
                break
    return best
for label, pick in (("least multiple of q", lambda S, q: [min(d for d in S if d % q == 0)]),
                    ("any multiple of q", lambda S, q: [d for d in S if d % q == 0])):
    c = Counter(); none = 0
    for S in H:
        fl = [(q, e) for q in range(2, 9) for e in pick(S, q) if any(d % q == 0 for d in S)]
        b = least_r(S, fl)
        if b is None: none += 1
        else: c[b[0]] += 1
    print(f"{label}: least push lap r over the hard sets {sorted(c.items())[:12]}{' ...' if len(c) > 12 else ''}; none {none}; "
          f"r <= 1: {sum(v for r, v in c.items() if r <= 1)}, r <= 3: {sum(v for r, v in c.items() if r <= 3)}")
