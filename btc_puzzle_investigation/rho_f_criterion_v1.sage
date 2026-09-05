# F(n)=1 <=> vec(z3) <lex vec(z3^2).  Since z3^2 = -1 - z3, vec(z3^2) = -e0 - vec(z3),
# so the comparison is decided at coordinate 0:  F(n)=1 <=> v0 < -1-v0 <=> v0 <= -1.
# Check the identity and the criterion over a wide n range (prime and composite).
import sys
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
bad = []
v0s = set()
for n in list(range(5, 130)) + [139, 147, 199, 208, 219, 243, 252, 259, 313, 327, 364]:
    if n % 3 == 0: continue
    K = CyclotomicField(12*n); z = K.gen(); z3 = z**(4*n)
    assert z3**2 + z3 + 1 == 0
    v = z3.vector(); w = (z3**2).vector()
    if tuple(w) != tuple(-K(1).vector() - v): bad.append(("identity", n))
    v0 = v[0]; v0s.add(v0)
    F = 1 if tuple((-z3**2).vector()) < tuple((-z3).vector()) else 2
    if (F == 1) != (v0 <= -1): bad.append(("criterion", n))
    if F != 1: bad.append(("F!=1", n, v0))
print("n tested:", len([n for n in list(range(5,130))+[139,147,199,208,219,243,252,259,313,327,364] if n % 3]))
print("observed v0(z3) values:", sorted(v0s))
print("violations:", bad if bad else "NONE — F(n)=1 identically on the tested range")
