"""What binds in the extremal words?  R = (5Q_f+1)/u_{x_f}.

Decoded LP (from order5_certificate_v3.constraints):
  * first move (x1,Q1):   u_{x1}/5 in [Q1 - 1/5 + tau, Q1 + 1/5 - tau]   so   u_{x1} in [5Q1-1, 5Q1+1]
  * consecutive (xp,Qp) -> (xj,Qj):  (Qj - 1/5) u_xp  <  (Qp + 1/5) u_xj  <  (Qj + 1/5) u_xp
  * advance:  (Qp + 1/5) u_xj  <  (Qj + 1/5) u_xp

So if the FINAL setter is also the FIRST setter, u_{x_f} >= 5Q1 - 1 and
      R <= (5Q_f + 1)/(5Q1 - 1),      which is < 4  iff  Q_f < 4Q1 - 1.
This records, for the best word at each max lap: the first setter and lap, the final setter and
lap, whether they coincide, and the bound that the first-move constraint alone gives.
"""
import sys, importlib.util
_ARGV = list(sys.argv)
from fractions import Fraction as F
from collections import defaultdict
spec = importlib.util.spec_from_file_location("cert", "experiments/n8/order5_certificate_v3.py")
cert = importlib.util.module_from_spec(spec); sys.argv = ["cert"]; spec.loader.exec_module(cert)

S = int(_ARGV[1]) if len(_ARGV) > 1 else 18
L = (4 * S - 1) // 5
best = defaultdict(lambda: [None, None])

def extend(word):
    cons = cert.constraints(word)
    tau = cert.opt(cons, 3, 'max', S, True)
    if tau is None or tau <= 0: return
    x, Q = word[-1]
    m = cert.opt(cons, x - 1, 'min', S, False) if x > 0 else F(1)
    if m is not None and m > 0:
        R = F(5 * Q + 1) / m
        ml = max(q for _, q in word)
        if best[ml][0] is None or R > best[ml][0]: best[ml] = [R, list(word), m]
    if len(word) >= 3 * L: return
    used = {xx: QQ for xx, QQ in word}
    for nx in (1, 2, 3):
        for nq in range(used.get(nx, 0) + 1, L + 1):
            extend(word + [(nx, nq)])

for x in (1, 2, 3):
    for q in range(1, L + 1):
        extend([(x, q)])

print(f"order 5, S = {S}, L = {L}")
print(f"{'maxlap':>6} {'supR':>8} {'x1':>3} {'Q1':>3} {'xf':>3} {'Qf':>3} {'same':>5} {'u_xf':>8} "
      f"{'5Q1-1':>6} {'(5Qf+1)/(5Q1-1)':>17}  verdict")
for ml in sorted(best):
    R, w, m = best[ml]
    x1, Q1 = w[0]; xf, Qf = w[-1]
    same = (x1 == xf)
    fb = F(5*Qf+1, 5*Q1-1) if 5*Q1-1 > 0 else None
    verdict = ""
    if same and fb is not None:
        verdict = f"first-move bound gives R <= {float(fb):.4f}" + ("  (<4)" if fb < 4 else "  (NOT <4)")
    else:
        verdict = "final setter differs from first"
    print(f"{ml:>6} {float(R):>8.4f} {x1:>3} {Q1:>3} {xf:>3} {Qf:>3} {str(same):>5} {float(m):>8.4f} "
          f"{5*Q1-1:>6} {float(fb) if fb else 0:>17.4f}  {verdict}")
