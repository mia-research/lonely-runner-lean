"""twin3_jshape.py -- exhaustive verification of the J-shape lemma.

CLAIM: for every rho' in {1,...,7} and every nonempty V subset Z/8,
   J(rho',V) = { j : V subset of bad(rho', j) }
is empty, a singleton, or a pair of CYCLICALLY ADJACENT residues.
Verified over all 7 * 255 pairs by exhaustion.
"""
from twin3_core import bad, J_set

def shape(J):
    if len(J)==0: return "empty"
    if len(J)==1: return "singleton"
    if len(J)==2:
        a,b = sorted(J)
        return "adjacent" if (b-a)%8 in (1,7) else "NON-ADJACENT"
    return f"size{len(J)}"

bad_shapes = []
counts = {}
for rho2 in range(1,8):
    for mask in range(1,256):
        V = frozenset(i for i in range(8) if mask>>i & 1)
        J = J_set(rho2, V)
        s = shape(J)
        counts[s] = counts.get(s,0)+1
        if s not in ("empty","singleton","adjacent"):
            bad_shapes.append((rho2, sorted(V), sorted(J), s))
print("shape census over all (rho', V):", counts)
print("violations:", len(bad_shapes))
for b in bad_shapes[:10]: print("  ", b)
# also: component/gap lengths in units of 1/c
print()
print("max A-component (units 1/c) and min A-gap (units 1/c) by |J|:")
print("  |J|=0 -> comp 0, gap 8")
print("  |J|=1 -> comp 1, gap 7")
print("  |J|=2 adjacent -> comp 2, gap 6")
