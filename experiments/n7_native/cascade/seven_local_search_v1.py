#!/usr/bin/env python3
"""Local search for a covering in the local digit lemma (EXACT masks): five runner states whose forbidden (y, s) cells
cover the whole 7x7 grid.  Hill climbing with restarts on the number of still-allowed cells.  Finding one shows the
one-free-digit lemma is false (then a second free digit is needed)."""
import random
states = []; masks = []
for u0 in range(1, 7):
    for u1 in range(7):
        for e in range(7):
            for D in range(7):
                m = 0
                for y in range(7):
                    for s in range(7):
                        t = (D + u1 * y + (e + u0 * y) // 7 + u0 * s) % 7
                        if t in (0, 6): m |= 1 << (7 * y + s)
                states.append((u0, u1, e, D)); masks.append(m)
FULL = (1 << 49) - 1
rnd = random.Random(3); best = 49; found = []
for restart in range(400):
    pick = [rnd.randrange(len(masks)) for _ in range(5)]
    def allowed(p): 
        c = 0
        for i in p: c |= masks[i]
        return 49 - bin(c).count("1")
    cur = allowed(pick)
    for it in range(3000):
        j = rnd.randrange(5); cand = rnd.randrange(len(masks))
        p2 = pick[:]; p2[j] = cand; a = allowed(p2)
        if a <= cur: pick, cur = p2, a
        if cur == 0: break
    best = min(best, cur)
    if cur == 0:
        found.append(tuple(sorted(states[i] for i in pick)))
        if len(found) >= 5: break
print(f"best number of allowed cells over restarts: {best}; coverings found: {len(found)}")
for f in found: print("   covering states (u0,u1,e,D):", f)
