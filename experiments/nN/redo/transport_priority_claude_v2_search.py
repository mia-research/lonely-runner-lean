"""transport_priority_claude_v2_search.py (2026-10-05). Targeted test of lemma (C) for the restricted
"fastest-flank" regime: flank e, walkers x < e only (ratio x/e < 1), as used by E395's twin-chain route.
Formula (given, exact): opening k is blocked by walker x iff (8k+1)*x mod (8e) is outside [e, 7e]. Period e.
(C), unrestricted: a flank fully blocked (dead) by the union of <=5 walkers is blocked by one near-sharer
(a single walker whose blocked set alone is the whole period) or by an exact half-pair (two walkers).
This script restricts to walkers x < e (fastest-flank) and single-threaded, exact-integer brute force:
(1) confirms or refutes that a single walker with x < e can ever be a universal blocker (near-sharer) alone;
(2) for every e in [2, EMAX], finds the SMALLEST full cover (if any) by <=5 walkers drawn only from x < e,
    and classifies it by (q, p, class_count) per walker, flagging any cover that is not "one near-sharer"
    and not "two q=2 walkers" (an exact half-pair) as a counterexample to the restricted (C).
No multiprocessing, no randomness, exact integers throughout.
"""
import itertools, math, time, sys

EMAX = 24

def mask(e, x):
    m = 0
    for k in range(e):
        r = ((8 * k + 1) * x) % (8 * e)
        if r < e or r > 7 * e:
            m |= 1 << k
    return m

def classify(e, x):
    g = math.gcd(x, e)
    q = e // g
    p = x // g
    return q, p

t0 = time.time()
near_sharer_x_lt_e = []     # should stay empty: x<e can never be a lone universal blocker
counterexamples = []        # covers of size<=5, not reducible to 1 near-sharer or 1 half-pair
all_minimal = []            # record of the minimal cover found for every dead e (or None)

for e in range(2, EMAX + 1):
    xs = list(range(1, e))
    masks = {x: mask(e, x) for x in xs}
    full = (1 << e) - 1

    singles = [x for x in xs if masks[x] == full]
    if singles:
        near_sharer_x_lt_e.append((e, singles))

    found = None
    for size in range(1, 6):
        for combo in itertools.combinations(xs, size):
            o = 0
            for x in combo:
                o |= masks[x]
            if o == full:
                found = combo
                break
        if found:
            break

    if found is None:
        all_minimal.append((e, None))
        continue

    types = [(x,) + classify(e, x) + (bin(masks[x]).count("1"),) for x in found]
    is_near_sharer_alone = (len(found) == 1)
    is_half_pair = (len(found) == 2 and all(t[1] == 2 for t in types))
    all_minimal.append((e, found, types, is_near_sharer_alone, is_half_pair))

    if not is_near_sharer_alone and not is_half_pair:
        # full residue table for this witness
        table = []
        for k in range(e):
            blockers = [x for x in found if (masks[x] >> k) & 1]
            table.append((k, blockers))
        counterexamples.append((e, found, types, table))

elapsed = time.time() - t0

with open("transport_priority_claude_v2_search.out", "w") as o:
    o.write("transport_priority_claude_v2_search: fastest-flank (x<e) restricted test of lemma (C)\n")
    o.write("EMAX=%d, elapsed=%.3fs\n\n" % (EMAX, elapsed))
    o.write("(1) Single walker x<e ever a universal blocker alone (near-sharer)? instances: %s\n" % near_sharer_x_lt_e)
    o.write("\n(2) Minimal full-cover by walkers x<e, per e (None = no cover of size<=5 found):\n")
    for row in all_minimal:
        o.write("  %s\n" % (row,))
    o.write("\n(3) Counterexamples to the x<e-restricted (C) (cover size<=5, not 1 near-sharer, not a q=2 half-pair):\n")
    for e, found, types, table in counterexamples:
        o.write("  e=%d  walkers(x,q,p,class_count)=%s\n" % (e, types))
        o.write("    residue table (k: blocking walkers): %s\n" % table)
    o.write("\ncount of counterexamples found: %d\n" % len(counterexamples))

print(open("transport_priority_claude_v2_search.out").read())
