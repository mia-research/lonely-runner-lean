"""Exact continuum covering of the band by block-type zones (agent_caseB_A).

Algorithm (zone subtraction):
  stack = [band zone]
  pop a zone P; choose a rational point p in P; list the block types that work at p
  (if none: p is a counterexample to the target -> record and stop that branch);
  choose one type T (largest multiplicative margin at p); P \\ T is a disjoint union of
  zones  P & not c1,  P & c1 & not c2, ...  (c_j = the cluster constraints of T that P
  does not already imply); push the non-empty ones.
Terminates when the stack is empty (every piece removed by a type) => the finite list of
types used covers the band exactly (continuum, not samples).
All decisions exact (Fraction).  Progress to progress_polycover.txt.
Usage: python3 polycover.py MAXPIECES [pick]   pick in {margin, lowK}
"""
import sys, time, json
from fractions import Fraction as F
from zones import *

def margin(vals, cons):
    """min over constraints of q*s_b/s_a (>=1 inside); multiplicative slack."""
    m = None
    for a, b, q, st in cons:
        r = q * vals[b] / vals[a]
        if m is None or r < m:
            m = r
    return m if m is not None else F(10**9)

def choose(vals, types, pick):
    best = None
    for t in types:
        cons = type_constraints(*t)
        mg = margin(vals, cons)
        key = (mg, -t[1]) if pick == 'margin' else (-t[1], mg)
        if best is None or key > best[0]:
            best = (key, t)
    return best[1]

def run(maxpieces, pick='margin'):
    t0 = time.time()
    stack = [band_zone()]
    used = {}
    counter = []
    uncovered = []
    npieces = 0
    while stack:
        P = stack.pop()
        npieces += 1
        if npieces > maxpieces:
            uncovered.append(P); uncovered.extend(stack); break
        p = P.point()
        types = all_types_at(p)
        if not types:
            counter.append(p)
            continue
        T = choose(p, types, pick)
        used[T] = used.get(T, 0) + 1
        cons = type_constraints(*T)
        # sanity: p satisfies T
        assert all(contains(p, c) for c in cons), (p, T)
        base = P.copy()
        for (a, b, q, st) in cons:
            if base.implies(a, b, q, st):
                continue
            # piece: base & not(s_a <= q s_b)  ==  s_b < (1/q) s_a  (strict)
            piece = base.copy().add(b, a, 1 / q, True).close()
            if not piece.empty():
                stack.append(piece)
            base.add(a, b, q, st).close()
            if base.empty():
                break
        if npieces % 200 == 0:
            with open(f'progress_polycover_{pick}.txt', 'w') as f:
                f.write(f"pieces {npieces} stack {len(stack)} types {len(used)} counter {len(counter)} "
                        f"elapsed {time.time()-t0:.0f}s\n")
    return used, counter, uncovered, npieces, time.time() - t0

if __name__ == '__main__':
    maxp = int(sys.argv[1]); pick = sys.argv[2] if len(sys.argv) > 2 else 'margin'
    used, counter, unc, n, dt = run(maxp, pick)
    print(f"pieces processed {n}, types used {len(used)}, counterexamples {len(counter)}, "
          f"uncovered zones {len(unc)}, time {dt:.1f}s")
    out = {'types': [[list(map(int, [t[0], t[1]])), list(t[2]), c] for t, c in
                     sorted(used.items(), key=lambda x: -x[1])],
           'counter': [[str(v) for v in p] for p in counter],
           'uncovered': [[[a, b, str(q), st] for a, b, q, st in z.constraints()] for z in unc[:200]],
           'n_uncovered': len(unc), 'pieces': n, 'complete': (not unc and not counter)}
    with open(f'polycover_{pick}_{maxp}.json', 'w') as f:
        json.dump(out, f)
    for t, c in sorted(used.items(), key=lambda x: -x[1])[:60]:
        print(c, t)
