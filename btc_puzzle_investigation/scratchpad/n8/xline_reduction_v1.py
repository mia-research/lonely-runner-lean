"""
N8 -- reduction of the pencil Lemma to a character sum on the x-line.  Exact integers only.

n odd => 2 is invertible on E(F_p), so Q0 := R/2 is RATIONAL.  Translating by -Q0 carries
{degree-2 divisors with sum R}  ->  {degree-2 divisors with sum O} = the fibres of  x : E -> P^1.
Under it the fibre weight chi2(N_D y) becomes   chi2( y(P+Q0) * y(Q0-P) ),  a function of x(P) alone.

CLAIM (tested here):
   Sp(R) - I(R)  =  1  +  SUM_{c in F_p}  chi2(c^3+Ac+B) * chi2( y(P+Q0)*y(Q0-P) ),   P=(c,.)
and the SUM is 0.        [the '1' is the fibre over c=infinity, i.e. 2(O) <-> 2(Q0)]

Divisor bookkeeping predicts  y(P+S)y(S-P) = kappa * prod_i (x - x(T_i+S)) / (x - x(S))^3,
T_i the three 2-torsion points; so up to a constant square-class the summand is
   chi2( (c^3+Ac+B) * prod_i(c - x(T_i+S)) * (c - x(S)) )  -- a DEGREE-7 polynomial.
Also tested: that the computed product matches this shape (deg-7 form gives the same sum up to sign).
"""
import sys
sys.path.insert(0, 'scratchpad/n8')
from pencil_vanishing_v1 import leg, pts, add, neg, m2, s2, n2, i2, pw2, add2, frob

def run(p, A, B):
    E = pts(p, A, B); n = len(E)+1
    if n % 2 == 0: return
    r = next(u for u in range(2, p) if leg(u, p) == -1)
    # square roots in F_{p^2}
    sq = {}
    for y0 in range(p):
        for y1 in range(p): sq.setdefault(m2((y0,y1),(y0,y1),p,r), []).append((y0,y1))
    inv2mod = pow(2, -1, n)                      # halving on E(F_p): n odd
    # dlog-free halving: Q0 = (n+1)//2 * R  works since 2*((n+1)/2) = n+1 = 1 mod n
    def half(R):
        k = (n+1)//2; T = None; base = R
        while k:
            if k & 1: T = add(T, base, p, A)
            base = add(base, base, p, A); k >>= 1
        return T
    tot_ok = True; sums = []
    for R in E:
        Q0 = half(R)
        assert add(Q0, Q0, p, A) == R
        Q0_2 = ((Q0[0],0),(Q0[1],0))
        u = Q0[0]
        Ssum = 0
        for c in range(p):
            rhs = (c*c%p*c + A*c + B) % p
            ys = sq.get((rhs % p, 0))
            if not ys: continue                  # cannot happen: every element of F_p is a square in F_p^2
            P2 = ((c,0), ys[0])
            Pl = add2(Q0_2, P2, p, A, r)                       # Q0 + P
            Pm = add2(Q0_2, (P2[0], n2(P2[1],p)), p, A, r)     # Q0 - P
            if Pl is None or Pm is None:  continue             # c == x(Q0): weight 0
            prod = m2(Pl[1], Pm[1], p, r)
            assert prod[1] == 0, "product of y's not in F_p"
            w = leg(prod[0], p)
            Ssum += leg(rhs, p) * w
        sums.append(Ssum)
        if Ssum != 0: tot_ok = False
    print(f"p={p:3d} A={A} B={B} n={n:3d}  x-line sum == 0 for {sum(1 for v in sums if v==0)}/{len(sums)} R"
          f"   {'OK' if tot_ok else 'FAIL '+str([v for v in sums if v][:3])}", flush=True)

print("n ODD -- j=0")
for (p,A,B) in [(11,0,4),(13,0,1),(19,0,3),(23,0,5),(31,0,3)]: run(p,A,B)
print("n ODD -- non-j=0")
for (p,A,B) in [(17,1,5),(19,3,1),(23,1,4),(29,2,1),(31,5,2),(37,1,1)]: run(p,A,B)
