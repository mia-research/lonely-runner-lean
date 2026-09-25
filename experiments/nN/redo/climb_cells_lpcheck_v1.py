"""Cross-check climb_cells_v1.lp_max (dual simplex, gmpy2.mpq) against late_word_certificate_v1.simplex_min
(Fraction tableau simplex, the order-5 solver) on random bounded LPs in 7 unknowns.  Exact; must agree exactly."""
import random
from fractions import Fraction as F
from gmpy2 import mpq
from climb_cells_v1 import lp_max, base_rows, NV
from late_word_certificate_v1 import simplex_min
r = random.Random(5); agree = infeas_both = 0; bad = 0
for trial in range(400):
    rows = base_rows(9)
    for _ in range(r.randint(3, 25)):
        a = [mpq(r.randint(-9, 9)) for _ in range(NV)]; b = mpq(r.randint(-20, 40))
        rows.append((a, b))
    c = [mpq(r.randint(-3, 3)) for _ in range(NV)]
    if all(x == 0 for x in c): c[0] = mpq(1)
    init = [i if c[i] >= 0 else 6 + i for i in range(6)] + [12 if c[6] >= 0 else 13]
    got = lp_max(rows, c, init)
    # reference: min -c.x, Ax <= b, x free -> x = x+ - x-
    A = [[F(int(x.numerator), int(x.denominator)) for x in a] + [-F(int(x.numerator), int(x.denominator)) for x in a] for a, b in rows]
    bb = [F(int(b.numerator), int(b.denominator)) for a, b in rows]
    cc = [-F(int(x.numerator), int(x.denominator)) for x in c] + [F(int(x.numerator), int(x.denominator)) for x in c]
    ref = simplex_min(A, bb, cc)
    if ref is None and got is None: infeas_both += 1
    elif ref is not None and ref != 'unbounded' and got is not None and -ref[0] == F(int(got[0].numerator), int(got[0].denominator)): agree += 1
    else: bad += 1; print("DISAGREE", trial, ref if ref is None or ref == 'unbounded' else ref[0], got if got is None else got[0])
print(f"agree on optimum {agree}; both infeasible {infeas_both}; disagreements {bad}")
