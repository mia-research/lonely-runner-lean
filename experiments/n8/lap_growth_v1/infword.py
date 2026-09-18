# CAN an infinite setter word satisfy  3/rho_x < sum_{window} 1/rho_j  at every return?
# Frequency argument: if letter x has frequency f_x, consecutive occurrences are ~1/f_x apart,
# so the window supplies about (1/f_x) * A  where A = sum_y f_y/rho_y.  The condition becomes
#     A > 3 f_x/rho_x   for every x,   i.e.   f_x/rho_x < A/3.
# But  sum_x f_x/rho_x = A  exactly.  Seven non-negative terms summing to A, each required to be
# below A/3 -- satisfiable whenever at least four letters carry weight.  So: NOT forbidden.
from fractions import Fraction as F
print("Frequency test: need f_x/rho_x < A/3 for all x, with sum_x f_x/rho_x = A.")
print("  7 equal terms give A/7 < A/3.  Satisfiable.  No contradiction available.\n")
# Explicit witness: round-robin word, clustered ratios.
rhos = [F(1), F(11,10), F(6,5), F(13,10), F(7,5), F(3,2), F(8,5)]
print("explicit round-robin word on rho =", [float(r) for r in rhos])
ok = True
for i, rx in enumerate(rhos):
    window = sum(F(1)/r for j, r in enumerate(rhos) if j != i)    # the other six
    need = F(3)/rx
    good = need < window
    ok &= good
    print(f"   x={i}: need 3/rho_x = {float(need):.3f}   window supplies {float(window):.3f}   {'OK' if good else 'FAILS'}")
print(f"\n  infinite round-robin word satisfies the condition at EVERY return: {ok}")
print("  => the scale-free return condition does NOT forbid an infinite setter word.")
# How much room?  Sweep clustering.
print("\nhow clustered must the ratios be for round-robin to work?")
for spread in (F(1,10), F(1,2), F(1), F(2), F(5)):
    rs = [F(1) + spread*F(i,6) for i in range(7)]
    worst = min(float(sum(F(1)/r for j,r in enumerate(rs) if j!=i) - F(3)/rs[i]) for i in range(7))
    print(f"   ratios spread over [1, {float(1+spread):.2f}] : worst margin {worst:+.3f}"
          f"  {'satisfiable' if worst>0 else 'blocked'}")
