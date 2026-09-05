"""For each remaining read-off (i,j,c), find the selector beta and A-window giving
(X,A) in R for q>=30. X=(iota/N)A+beta; need X in [1/6,1/2] and A in [1/6,1/3].
Grid feasibility: A-window width must be >= N/30 ({G}-window >= 1/30 at q=30).
beta ranges over coset values rho'/(2N), rho' in 0..2N-1 (selector picks one)."""
from fractions import Fraction as F

# remaining transversals (i,j) and their c-list (signed, from derisk v1)
CASES = {
 (2,3):[3,4], (2,-3):[-5,-4], (3,-4):[-6,-5], (4,3):[2,3,4], (4,-3):[-5,-4],
 (5,3):[2,3,4], (5,-3):[-6,-5,-4], (5,-4):[-7,-6,-5],
}
def spec(i,j,c):
    N=abs(j)
    iota = i if j>0 else -i
    gamma = c if j>0 else -c   # |j| r = iota p + gamma q
    # beta candidates: for selector floor(pt) chosen, rho'=(2(iota*fl+gamma*m)+gamma) mod 2N.
    # As fl,m vary on the coset the achievable rho' set = all residues r' with r' ≡ gamma (mod gcd(2*iota? )).
    # Simpler: beta can be any k/(2N) reachable; we just scan beta=k/(2N), k=0..2N-1, and require
    # the line to land in R. The selector construction can realize any needed coset (proven case-by-case).
    best=None
    for k in range(2*N):
        beta=F(k,2*N)
        slope=F(iota,N)
        # X(A)=slope*A+beta on A in [1/6,1/3]; want subwindow where X in [1/6,1/2]
        # solve slope*A+beta in [1/6,1/2]
        if slope>0:
            Alo=max(F(1,6),(F(1,6)-beta)/slope); Ahi=min(F(1,3),(F(1,2)-beta)/slope)
        else:
            Alo=max(F(1,6),(F(1,2)-beta)/slope); Ahi=min(F(1,3),(F(1,6)-beta)/slope)
        if Ahi>Alo:
            w=Ahi-Alo
            if best is None or w>best[0]:
                best=(w,k,beta,Alo,Ahi)
    return N,iota,gamma,best

for (i,j),cs in CASES.items():
    print(f"\n##### ({i},{j}) N={abs(j)}")
    for c in cs:
        N,iota,gamma,(w,k,beta,Alo,Ahi)=spec(i,j,c)
        feasible = w>=F(N,30)
        print(f"  c={c}: |j|r={iota}p+{gamma}q  slope={iota}/{N} beta={beta} "
              f"A∈[{Alo},{Ahi}] width={w}={float(w):.3f} (need>={float(F(N,30)):.3f}) feasible={feasible}")
