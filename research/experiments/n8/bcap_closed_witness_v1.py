"""At every BCAP counterexample, does Theorem 5.2's ACTUAL conclusion
   G n {t : {pt} in A} != empty   (with G,A defined by ||u t|| >= 1/n, CLOSED)
still hold?  Exhibit an exact rational witness for each.
Run: python3 bcap_closed_witness_v1.py
"""
from fractions import Fraction as F
from bcap_attack_v1 import *
from bcap_tightness_v1 import maxmin_gap, norm

CASES = [
 (3,[1],[1],2),(3,[3],[3],2),(3,[5],[5],2),(3,[7],[7],2),(3,[9],[9],2),(3,[11],[11],2),
 (4,[1,2],[1],3),(4,[1,3],[1],2),(4,[2,4],[2],3),(4,[3,9],[3],2),(4,[4,8],[4],3),(4,[5,10],[5],3),
 (5,[1,3],[1,2],2),(5,[3,9],[3,6],2),(5,[1,2,4],[1],3),(5,[1,3,4],[1],7),(5,[1,3,7],[2],2),
 (5,[1,4,7],[1],3),(5,[2,4,8],[2],3),(5,[2,6,8],[2],7),(5,[3,9,12],[3],7),
 (6,[1,3,5],[1,2],2),(6,[1,4,5],[1,3],3),(6,[2,8,10],[2,6],3),
 (8,[1,2,4,5,7],[1,2],3),(8,[1,2,4,5,7],[1,4],3),(8,[1,2,3,4,5,6],[1],7),(8,[1,2,3,4,6,7],[1],5),
]
ok = 0
print(f"{'n':>2}  {'S_G':<18}{'S_A':<9}{'p':>3}  {'B∩I_A':>7}  {'g(T)':>6}  witness t*  min||u t*||")
for n,SG,SA,p in CASES:
    LG,IG,LA,IA,B = B_direct(n,SG,SA,p)
    inter = sorted(B & set(IA))
    T = sorted(set(SG)|set(p*v for v in SA))
    g, args = maxmin_gap(T)
    t = args[0]
    mn = min(norm(u*t) for u in T)
    # independent re-check that t is in G and {pt} in A
    inG  = all(norm(F(u)*t) >= F(1,n) for u in SG)
    inA  = all(norm(F(v*p)*t) >= F(1,n) for v in SA)
    good = inG and inA
    ok += good
    print(f"{n:>2}  {str(SG):<18}{str(SA):<9}{p:>3}  {str(inter):>7}  {str(g):>6}  "
          f"{str(t):>8}   {str(mn):>5}   G:{inG} A:{inA}")
print(f"\ncounterexamples: {len(CASES)};  Theorem 5.2 CLOSED conclusion still holds at: {ok}")
