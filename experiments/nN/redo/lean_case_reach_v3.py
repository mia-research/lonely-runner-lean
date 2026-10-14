"""E406 (2026-10-06), lean_case_reach_v3: as lean_case_reach_v2, with M(2,2) now a Lean theorem
(LRC/Spec/ParityMixedTwoTwoN.lean: lonely_eight_of_quarter_two_two, lonely_eight_of_eighth_two_two; axioms
experiments/nN/parity_mixed_two_two_print_axioms_v1.out) and, on stored members, the grid corollary
(LRC/Spec/ParityGridN.lean: lonely_eight_of_grid; at most 3 multiples of 8, at most 4 non-multiples, none
divisible by 4, an odd non-multiple w dividing no cofactor m/8; axioms parity_grid_print_axioms_v1.out).
The grid corollary depends on the values, not only the residues, so it is read on members only.
Hypotheses are evaluated exactly (integers); no instant is computed here.  M(1,3) stays conditional.
"""
import sys, collections, itertools
sys.path.insert(0, '.')
from lean_case_reach_v2 import settled, typ, cost
from members_reach_check_v1 import load, full_residual
def grid(S):
    M = [d for d in S if d % 8 == 0]; N = [d for d in S if d % 8]
    if len(M) > 3 or len(N) > 4 or any(d % 4 == 0 for d in N): return False
    return any(w % 2 and all((m // 8) % w for m in M) for w in N)
if __name__ == '__main__':
    out = open('lean_case_reach_v3.out', 'w'); out.write(__doc__ + "\n")
    for m in (1, 2, 3, 4):
        n = 7 - m
        pats = [p for p in itertools.combinations_with_replacement((1, 2, 3, 4, 5, 6, 7), n)
                if sum(1 for r in p if r % 2) >= 2 and sum(cost(r) for r in p) >= 8]
        L = sum(1 for p in pats if settled(m, p, '22')); C = sum(1 for p in pats if settled(m, p, 'both'))
        out.write("shape (%d,%d): patterns %d; Lean (with M(2,2)) %d; with M(1,3) as well %d\n" % (m, n, len(pats), L, C))
    for fn in ['../residual_members_C_list_v1.json', 'both_shadowed_members_v1.json']:
        sets = [S for S in dict.fromkeys(load(fn)) if full_residual(S)]
        c = collections.Counter(); left = collections.Counter()
        for S in sets:
            mult = [d for d in S if d % 8 == 0]; rs = tuple(sorted(d % 8 for d in S if d % 8))
            if settled(len(mult), rs, '22'): c['Lean, residue cases'] += 1
            elif grid(S): c['Lean, grid corollary'] += 1
            elif settled(len(mult), rs, 'both'): c['M(1,3) only'] += 1
            else:
                c['open'] += 1; left[(len(mult), typ([d % 8 for d in S if d % 8]))] += 1
        out.write("\n%s: %d residual members: %s\n" % (fn, len(sets), dict(c)))
        out.write("  open, by (multiples, type): %s\n" % dict(sorted(left.items())))
    out.close(); print(open('lean_case_reach_v3.out').read()[len(__doc__):])
