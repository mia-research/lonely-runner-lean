from fractions import Fraction as F
n=8
def Sol(e,j,m): return frozenset(r for r in range(m) if (e*r-j)%m==0)
def bad(e,t,m): return Sol(e,(-t)%m,m)|Sol(e,(-(t+1))%m,m)
print("t_rho on each CELL of the two windows, and bad(rho,t):")
for win,cells in (("[3/5,5/7)",[(F(3,5),F(2,3)),(F(2,3),F(5,7))]),
                  ("[2/7,2/5)",[(F(2,7),F(1,3)),(F(1,3),F(2,5))])):
    print(" window",win)
    for rho in (2,4,6):
        out=[]
        for a,b in cells:
            x=(a+b)/2; t=(rho*x).numerator//(rho*x).denominator
            out.append((str(a)+".."+str(b), t, sorted(bad(rho,t,n))))
        same = len({tuple(o[2]) for o in out})==1
        print(f"   rho={rho}: " + " | ".join(f"[{c}] t={t} bad={B}" for c,t,B in out)
              + f"   bad constant across cells: {same}")
print("\nNOTE: for rho=6, t_6 is NOT constant on either window (it jumps at 2/3 resp. 1/3),")
print("but bad(6,3)==bad(6,4)=={2,6} and bad(6,1)==bad(6,2)=={1,5}, so the conclusion is unaffected.")
