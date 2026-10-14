"""The per-move recursion:  R_new < R_prev + 2/u_setter.

Derivation (order-general, threshold 1/n).  A setter is IN THE WAY just before it sets, at lap Q:
      |u * t_prev - Q| < 1/n      =>      Q < u*t_prev + 1/n = u*R_prev/n + 1/n.
It then sets to its own opening:  t_new = (Q + 1/n)/u,  so  R_new = n*t_new = (nQ + 1)/u.
Hence  R_new < (n(u*R_prev/n + 1/n) + 1)/u = (u*R_prev + 2)/u = R_prev + 2/u.

Consequence:  R_final < 1 + 2 * sum over moves of 1/u(setter),  since R_0 = n*t_0 = 1.
This checks the recursion against the certificate's own LP optima, word by word.
"""
import sys, importlib.util
from fractions import Fraction as F
_ARGV = list(sys.argv)
spec = importlib.util.spec_from_file_location("cert", "experiments/n8/order5_certificate_v3.py")
cert = importlib.util.module_from_spec(spec); sys.argv = ["cert"]; spec.loader.exec_module(cert)
n = 5

words = {
 "extremal (R=31/9)":        [(1,2),(2,1),(1,3),(3,1),(2,2),(1,6)],
 "regime B best (R=27/8)":   [(1,1),(2,1),(3,1)],
 "Q1=1,Qf=2 (R=11/4)":       [(1,1),(2,1),(3,1),(1,2)],
 "high lap (R=561/196)":     [(1,1),(2,1),(3,8),(1,2),(3,10)],
}
print("check: does R advance by less than 2/u at each move, on the LP optimum?")
for name, w in words.items():
    cons = cert.constraints(w)
    tau = cert.opt(cons, 3, 'max', 30, True)
    if tau is None or tau <= 0:
        print(f"  {name}: not realisable at S=30"); continue
    # minimise each setter's reading on the closed polyhedron to get the extremal configuration
    us = {}
    for x in set(xx for xx, _ in w):
        us[x] = cert.opt(cons, x - 1, 'min', 30, False)
    xf, Qf = w[-1]
    R = F(n*Qf + 1)/us[xf]
    bound = F(1) + 2 * sum(F(1)/us[x] for x, _ in w)
    print(f"  {name}")
    print(f"     LP minima u = {{ {', '.join(f'u{x}={us[x]}' for x in sorted(us))} }}")
    print(f"     true R = {R} = {float(R):.4f}")
    print(f"     recursion bound 1 + 2*sum(1/u) = {bound} = {float(bound):.4f}"
          f"   {'HOLDS' if R <= bound else '*** VIOLATED ***'}")
print()
print("Per-setter move budget: a setter of reading u can only be at laps Q <= n*t*u/n = u*t < u*(n-1)/n")
print("while R < n-1, so it has at most floor(u*(n-1)/n) laps available.")
for u in (2,3,4,9,14,20,50,100):
    m = int(u*4//5)
    print(f"   u = {u:>4}:  laps available <= {m:>3}   contribution 2m/u <= {2*m/u:.4f}")
print("   -> each setter contributes at most 8/5 = 1.6 asymptotically; three setters give 4.8,")
print("      so 1 + 4.8 = 5.8 is the crude ceiling. The recursion alone does NOT give R < 4.")
