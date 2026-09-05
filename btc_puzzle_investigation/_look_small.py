import csv
from math import gcd
from fractions import Fraction
def d_recursion(N,e):
    s=[]; e=abs(e)
    while e>0:
        D=N//e
        if D==0: break
        s.append(D); e=abs(e-N//D)
    return s
rows=sorted([(int(r["bits"]),int(r["private_key"],16),r["puzzle"]) for r in csv.DictReader(open("puzzles_verified.csv"))])
print(f"{'pz':>3} {'P':>3} {'d':>12} {'d/2^P reduced':>16} {'sig(full N=2^P)':<26} {'sig(offset)':<20}")
for P,d,pz in rows:
    fr=Fraction(d,1<<P)
    N=1<<P; sig=d_recursion(N,d)
    off=d-(1<<(P-1)); soff=d_recursion(1<<(P-1),off) if off>0 else []
    print(f"{pz:>3} {P:>3} {d:>12} {str(fr):>16} {str(sig):<26} {str(soff):<20}")
