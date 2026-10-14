import random, math
from math import gcd
random.seed(5)
# The window rule, stated over the REALS (it is a ratio condition; integrality is never used):
#   flank e exempt; the others must lie in [e/A, 7e/A] for some A = 1 mod 8.
def R2_real(ds):
    for e in sorted(ds, reverse=True):
        o=[d for d in ds if d!=e]
        lo,hi=min(o),max(o)
        Amin=e/lo; Amax=7*e/hi
        A=1
        while A<Amin: A+=8
        if A<=Amax: return True
    return False

def gen_int(H):
    while True:
        c=sorted(random.sample(range(1,H+1),7))
        g=0
        for x in c: g=gcd(g,x)
        if g==1: return [float(x) for x in c]
def gen_unif(hi):    return sorted(random.uniform(1,hi) for _ in range(7))
def gen_logunif(hi): return sorted(math.exp(random.uniform(0,math.log(hi))) for _ in range(7))
def gen_ap_pert(eps):
    return sorted(max(0.01,(i+1)*(1+random.uniform(-eps,eps))) for i in range(7))
def gen_clustered():
    base=sorted(random.uniform(1,10) for _ in range(7))
    return sorted(b*random.choice([1,1,1,8,20]) for b in base)

schemes=[
 ("integers [1,20]",       lambda: gen_int(20)),
 ("integers [1,40]",       lambda: gen_int(40)),
 ("integers [1,200]",      lambda: gen_int(200)),
 ("uniform reals [1,10]",  lambda: gen_unif(10)),
 ("uniform reals [1,100]", lambda: gen_unif(100)),
 ("log-uniform [1,1000]",  lambda: gen_logunif(1000)),
 ("AP +/-10%",             lambda: gen_ap_pert(0.10)),
 ("AP +/-50%",             lambda: gen_ap_pert(0.50)),
 ("clustered w/ outliers",  gen_clustered),
]
print("Window-rule coverage under different sampling schemes on the SAME rule.")
print("The conjecture ranges over Fin 8 -> R.  There is no canonical measure there,")
print("so any 'fraction covered' is a property of the scheme, not of the problem.\n")
print(f"  {'sampling scheme':26} {'n':>7} {'covered %':>10}")
for nm,g in schemes:
    n=4000; c=0
    for _ in range(n):
        ds=g()
        if len(set(ds))<7: continue
        c+=R2_real(ds)
    print(f"  {nm:26} {n:>7} {100*c/n:>9.2f}%")
print("\nspread across schemes is the answer: if the number moves, it is not a")
print("fraction of the conjecture -- it is a pass rate on one enumeration.")
