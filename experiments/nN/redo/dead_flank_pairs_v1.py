"""E398 (2026-10-05), dead_flank_pairs_v1: (1) the reverse view of dead flanks; (2) the six-dead set and the five-dead sets, flank by flank.
Owner: "Ok" (to: pairs of flanks, where e is dead through x_j and x_j through e; and the six-dead set and its near relatives).
(1) For every dead flank e of every 7-subset of [1,20] with gcd 1 and every minimal cover walker x_j: the walker's type (q, p mod 8),
whether the flank x_j is itself dead, and the reverse ratio (e/x_j in lowest terms: reverse q' = p, reverse p' = q).  Counts of
(type, reverse dead?) for the most frequent types; and the sets where e and x_j are both dead through each other (mutual pairs).
(2) The six-dead set {2,3,4,5,6,7,16} and the 40 five-dead sets: per flank, dead or not, the minimal covers; for the surviving flank
the clear openings and, at each blocked opening k mod e, the walkers in the way.
Exact (integers).
"""
import itertools, math, sys
from collections import Counter
N = 20
MASK = {}
for e in range(1, N + 1):
    for x in range(1, N + 1):
        if x == e: continue
        m = 0
        for k in range(e):
            r = ((8 * k + 1) * x) % (8 * e)
            if r < e or r > 7 * e: m |= 1 << k
        MASK[(e, x)] = m

def dead_flank(S, e):
    full = (1 << e) - 1; o = 0
    for x in S:
        if x != e: o |= MASK[(e, x)]
    return o == full

def min_covers(S, e):
    full = (1 << e) - 1; w = [x for x in S if x != e]; ms = [MASK[(e, x)] for x in w]
    for size in range(1, 7):
        found = []
        for sub in itertools.combinations(range(6), size):
            o = 0
            for i in sub: o |= ms[i]
            if o == full: found.append([w[i] for i in sub])
        if found: return found
    return []

out = open('dead_flank_pairs_v1.out', 'w'); out.write(__doc__ + "\n")
rev = Counter(); mutual = 0; total = 0; mutual_ex = []
dead_sets = Counter()
five = []
for S in itertools.combinations(range(1, N + 1), 7):
    g = 0
    for x in S: g = math.gcd(g, x)
    if g != 1: continue
    deadf = [e for e in S if dead_flank(S, e)]
    if len(deadf) >= 5: five.append((S, deadf))
    for e in deadf:
        for cover in min_covers(S, e):
            for x in cover:
                gg = math.gcd(x, e); q = e // gg; p = x // gg
                xd = x in deadf
                rev[((q, p % 8), xd)] += 1
                total += 1
                if xd:
                    # is e in some minimal cover of x?
                    if any(e in c for c in min_covers(S, x)):
                        mutual += 1
                        if len(mutual_ex) < 5: mutual_ex.append((S, e, x))
out.write("walker occurrences in minimal covers: %d; the walker's own flank is dead in %d; mutual (e in a minimal cover of x as well): %d\n" % (
    total, sum(c for (t, d), c in rev.items() if d), mutual))
byt = Counter()
for (t, d), c in rev.items(): byt[t] += c
for t, c in byt.most_common(15):
    out.write("  type %s: %d occurrences; walker's flank dead in %d\n" % (t, c, rev[(t, True)]))
out.write("mutual examples: %s\n" % mutual_ex)
out.write("\nsets with at least five dead flanks: %d\n" % len(five))
for S, deadf in five:
    out.write("  %s dead flanks %s surviving %s\n" % (S, deadf, [e for e in S if e not in deadf]))
S6 = (2, 3, 4, 5, 6, 7, 16)
out.write("\nSIX-DEAD SET %s\n" % (S6,))
for e in S6:
    if dead_flank(S6, e):
        mc = min_covers(S6, e)
        out.write("  flank %d dead; minimal covers (walkers): %s\n" % (e, mc))
    else:
        out.write("  flank %d NOT dead: openings k mod %d in the way / clear:\n" % (e, e))
        for k in range(e):
            inway = [x for x in S6 if x != e and (MASK[(e, x)] >> k) & 1]
            out.write("     k=%2d: %s\n" % (k, ("walkers in the way " + str(inway)) if inway else "CLEAR"))
out.close(); print(open('dead_flank_pairs_v1.out').read()[len(__doc__):][:6500])
