"""Is the move-counting route capable of capping the cascade at n = 8, k = 7?

The framework's own bound (SmallOrders.nearest_reading_recurrence) is

    t_N / t_0  <=  prod_{j<N} (Q_j + 1/n)/(Q_j - 1/n),          Q_j = the setter's lap at move j

so    log G  <=  sum_j  2/(n*Q_j)  +  O(sum_j 1/Q_j^2),          G = t_N/t_0.

Each runner x, between two of its own settings, must grow t by at least
(P + 1 - 1/n)/(P + 1/n)  (SmallOrders.return_growth), so its setting laps are essentially
consecutive integers over the run.  Hence for one runner
    sum_i 1/P_i  ~  log(P_max/P_min)  =  log G,
and over k runners   sum_j 1/Q_j  ~  k log G.   Substituting:

    log G  <=  (2k/n) log G  +  C        i.e.    log G (1 - 2k/n)  <=  C.

n > 2k caps.  n <= 2k is VACUOUS -- the coefficient has the wrong sign.  At n = 8, k = 7
it is 1 - 14/8 = -0.75.  This script measures the two quantities on real cascades to check
the "sum_j 1/Q_j ~ k log G" step, which is the only non-mechanical link.
"""
import random, math
from fractions import Fraction

def circ(x):
    f = x - math.floor(x)
    return min(f, 1 - f)

def cascade(ds, n=8, maxsteps=20000):
    """Run the determinator from the bound. Returns (t0, tN, setter laps, stopped?)."""
    m = min(ds)
    t = 1.0 / (n * m)
    t0, laps = t, []
    for _ in range(maxsteps):
        inway = [d for d in ds if circ(d * t) < 1.0 / n]
        if not inway:
            return t0, t, laps, True                 # lonely: the cascade has arrived
        # the move lands on the earliest opening among runners in the way
        best = None
        for d in inway:
            Q = round(d * t)
            nxt = (Q + 1.0 / n) / d
            if nxt > t and (best is None or nxt < best[0]):
                best = (nxt, Q)
        if best is None:
            return t0, t, laps, False
        t, Q = best
        laps.append(Q)
    return t0, t, laps, False

random.seed(20260917)
rows = []
for _ in range(4000):
    k = 7
    ds = sorted(random.uniform(1, 40) for _ in range(k))
    t0, tN, laps, stopped = cascade(ds)
    if len(laps) < 5 or tN <= t0:
        continue
    G = tN / t0
    logG = math.log(G)
    S = sum(1.0 / Q for Q in laps if Q > 0)
    if logG <= 0:
        continue
    rows.append((len(laps), logG, S, S / logG, k))

print(f"cascades used                : {len(rows)}")
print(f"moves per cascade  (median)  : {sorted(r[0] for r in rows)[len(rows)//2]}")
ratios = sorted(r[3] for r in rows)
print()
print("The tested link:  sum_j 1/Q_j  ~  k * log G,  with k = 7")
print(f"  ratio (sum 1/Q_j)/log G    median {ratios[len(ratios)//2]:.2f}"
      f"   10th {ratios[len(ratios)//10]:.2f}   90th {ratios[9*len(ratios)//10]:.2f}")
print(f"  predicted if the link holds: about k = 7")
print()
n = 8
print("The bound's own coefficient, measured per cascade:")
coef = sorted((2.0 / n) * r[2] / r[1] for r in rows)
print(f"  (2/n)*sum(1/Q_j) / log G   median {coef[len(coef)//2]:.2f}"
      f"   10th {coef[len(coef)//10]:.2f}   90th {coef[9*len(coef)//10]:.2f}")
print(f"  predicted 2k/n             = {2*7/8:.2f}")
print()
print(f"VERDICT: the bound reads  log G <= {2*7/8:.2f} * log G + C.")
print(f"         Coefficient {2*7/8:.2f} >= 1, so it never constrains log G at n=8, k=7.")
print(f"         For a cap the coefficient must be < 1, i.e. 2k < n.")

print()
print("LIMITS OF THE MEASUREMENT, stated rather than buried.")
print("  * Only 325 of 4,000 sampled cascades were usable: the rest stop in under 5 moves.")
print("    The median usable run is 6 moves, so the asymptotic step")
print("    sum_i 1/P_i ~ log(P_max/P_min) is being tested on short runs and is crude there.")
print("    That is why the measured ratio (8.60) sits above the predicted k = 7.")
print("  * The measurement does NOT carry the verdict. The verdict is arithmetic:")
print("    the coefficient is 2k/n = 1.75 whatever the data say, and an inequality")
print("    log G <= 1.75 log G + C constrains nothing. The measurement only checks that")
print("    the link 'sum 1/Q_j ~ k log G' is not wildly wrong, and it is not -- the")
print("    measured coefficient 2.15 exceeds 1.75, making the bound MORE vacuous, not less.")
print("  * Cascades are run in floating point here. The verdict does not depend on")
print("    precision; the counts and laps do, mildly.")
print()
print("WHAT THIS DOES AND DOES NOT SHOW.")
print("  Shows: any argument that caps the cascade by counting moves and charging each one")
print("    its growth cost hits 2k < n and stops. That is not a weakness of one lemma --")
print("    the potential Psi of section 8.2 reaches the same threshold by different")
print("    bookkeeping, and this says why.")
print("  Does NOT show: that no cap exists, or that Existence is false at n = 8. It says")
print("    the remaining route cannot be a move count. It must use the ARITHMETIC of the")
print("    particular readings -- which is what the opening/residue/lattice machinery does.")
