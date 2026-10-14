"""Try the measure route on ExistenceAt8 directly, and see what happens.

Last message claimed: 'a continuity or measure argument would reach a set with interior far
more easily than the framework's machinery reaches its boundary.' That was asserted, not
tested. This tests it.

THE MEASURE ARGUMENT, written out. Runner d is BLOCKED at time s when circDist(d*s) < 1/n.
As s runs over a period, that is an arc of width 2/n, so the blocked set for one runner has
density 2/n. The subject is lonely when NO runner blocks. A union bound gives

    density(some runner blocks)  <=  sum over runners of 2/n  =  k * 2/n

and the lonely set is non-empty as soon as that is < 1, i.e. 2k < n.
"""
from fractions import Fraction as F

for n, k in ((8, 7), (8, 3), (6, 2), (5, 2), (11, 5)):
    tot = F(2 * k, n)
    print(f"  n={n:<3} k={k:<2} total blocked density = k*2/n = {tot}  "
          f"{'< 1  -> union bound SUCCEEDS' if tot < 1 else '>= 1 -> union bound gives NOTHING'}")
print()
print("At n = 8 with k = 7 the total is 7/4 = 1.75. The blocked arcs cover the circle 1.75")
print("times over, so the union bound is vacuous -- it does not even show the lonely set is")
print("non-empty, let alone locate it.")
print()
print("AND THAT IS THE SAME THRESHOLD AS EVERYTHING ELSE.")
print("  section 8.2's potential Psi caps the cascade exactly when 2k < n.")
print("  move_count_ceiling_v1 showed any move-counting argument hits log G (1 - 2k/n) <= C,")
print("    which is vacuous at n=8, k=7 with coefficient -0.75.")
print("  the withdrawn Proposition 6.11's criterion is sum (2/n + 1/c_j) < 1, which needs")
print("    |J| <= 3 at order 8 for the SAME reason: each term is at least 2/n.")
print()
print("So the measure route is not a different route. It is the union bound, it is the n > 2k")
print("threshold, and it dies at n = 8, k = 7 exactly where the others die.")

print()
print("=" * 72)
print("THE SECOND ERROR, and it is a logical one.")
print()
print("  existence_impositions_v1 measured 'the lonely set always has interior' on 400")
print("  arrangements. Having interior is a property of a NON-EMPTY set. Every arrangement")
print("  measured had a non-empty lonely set -- which is just Existence holding empirically,")
print("  which was already known. The interior observation gives NO route to non-emptiness.")
print()
print("  'The set is fat once you know it is there' does not help you learn it is there. I")
print("  presented it as though it did.")
print()
print("WHAT THIS DOES TO THE REGISTER'S RULING.")
print()
print("  The register marks covering (item 4), measure (item 5) and union bounds (item 27)")
print("  NOT APPLICABLE. I read that as a methodological commitment that a measure argument")
print("  could nonetheless discharge ExistenceAt8. It cannot: at n = 8, k = 7 the union bound")
print("  is 7/4 and yields nothing at all.")
print()
print("  So the ruling is right on the MATHEMATICS, not only on method. Those routes are")
print("  inapplicable because they do not work here, exactly as 'NOT APPLICABLE' says.")
print()
print("  The distinction between the frozen target and the framework's conjecture stands --")
print("  ExistenceAt8 is an existence statement and section 3 says existence is not what is")
print("  being asked. But no easier route to the frozen target follows from it, which is what")
print("  I implied.")

print()
print("=" * 72)
print("AND THE OTHER HALF OF THE SUGGESTION -- 'continuity' -- dies on a theorem already")
print("in the tree, without needing any new argument.")
print()
print("  Flanks.lonely_iff_exists_flank is an IFF:")
print("      (exists s, 0 < s and Lonely n ds s)  <->  exists e in ds, exists k,")
print("                                                Lonely n ds (flankOpening n e k)")
print()
print("  So the flank openings -- the BOUNDARY points, the ones circDist_flank_self puts")
print("  exactly on 1/n -- are a COMPLETE search. The interior contains nothing the boundary")
print("  misses.")
print()
print("  'Interior points are easier to reach than boundary points' presupposes the interior")
print("  holds something the boundary does not. It does not. There is no easier target.")
print()
print("  Both halves of the suggestion are therefore void: the measure half by the 7/4")
print("  arithmetic above, the continuity half by a theorem that was already proved.")
