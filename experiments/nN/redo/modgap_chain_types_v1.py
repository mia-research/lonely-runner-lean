"""modgap_chain_types_v1 (2026-10-06): the move structure of the twelve exact counterexamples of modgap_real_adv_v5 (r = k/10, k = 60..71), exact Fractions throughout.
For each: the cascade of the six cluster readings at threshold 1/7 in u = 7*m*t from u = 1 (the first move is set by the reading whose zone contains 1); the setters, the zone indices j, the number of moves, whether several readings block at a move, the
ratios s_k = rho_k/rho_0 against the slowest reading (rho_0 = min), and for each s_k the nearest fraction p/q with q <= 12 and its exact error.
[PROVISIONAL: counting tool; supports: the description of what a failing chain looks like, a statement about observed structure and not an existence claim]  [OBS, F17: twelve examples from one continuation path]."""
import re
from fractions import Fraction as F
src = open('modgap_real_adv_v5.out').read()
blocks = re.findall(r"r = (\d\.\d): EXACT counterexample.*\n\s+rho = \[(.*?)\]", src)
out = open('modgap_chain_types_v1.out', 'w'); out.write(__doc__ + "\n")
def log(s): out.write(s + "\n"); print(s)
for r, lst in blocks:
    rho = sorted(F(x.strip().strip("'")) for x in lst.split(','))
    u = F(1); moves = []
    while True:
        bl = []
        for i, q in enumerate(rho):
            x = q * u / 7; j = round(x)
            if abs(x - j) < F(1, 7): bl.append((F(7 * j + 1) / q, i, j))
        if not bl: break
        e, i, j = max(bl); moves.append((i, j, len(bl), u)); u = e
        if u > 6: break
    log("r = %s: min rho = %s, moves = %d, landing u = %s (>6: %s)" % (r, rho[0], len(moves), u, u > 6))
    log("   setters %s" % [m[0] for m in moves])
    log("   zone indices j %s" % [m[1] for m in moves])
    log("   moves with several blockers: %d; first setter %d with rho in (6, 8): %s" % (sum(1 for m in moves if m[2] > 1), moves[0][0], 6 < rho[moves[0][0]] < 8))
    s = [q / rho[0] for q in rho]
    approx = []
    for q in s[1:]:
        best = min(((abs(q - F(p, d)), F(p, d)) for d in range(1, 13) for p in range(d, 3 * d + 1)), key=lambda t: t[0])
        approx.append("%s (err %s)" % (best[1], best[0].limit_denominator(10**6)))
    log("   s_k = rho_k/rho_0 nearest fraction (den <= 12): %s" % approx)
out.close()
