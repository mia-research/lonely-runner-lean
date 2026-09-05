import numpy as np, random, math
from fractions import Fraction
from sympy import isprime, totient
random.seed(0)
N=160; A=1<<(N-1)
def dec(d): return Fraction(d-A,A).limit_denominator(256)
# --- empirical P(n|N=160) over cells (n,k) ---
cellcount={}; ncount=np.zeros(257)
DR=80000
for _ in range(DR):
    f=dec(random.randrange(A,1<<N)); n,k=f.denominator,f.numerator
    ncount[n]+=1; cellcount[(n,k)]=cellcount.get((n,k),0)+1
pn=ncount/ncount.sum()
Hn=-(pn[pn>0]*np.log2(pn[pn>0])).sum()
ncells=len(cellcount)
print(f"=== puzzle 160: range of d = [2^159,2^160), width 2^159 (159 bits) ===")
print(f"  # distinct (n,k) cells seen in {DR} draws: {ncells} (theory ~sum phi(n)~20000)")
print(f"  H(n|N)={Hn:.2f} bits")

# --- guessing entropy of (n,k): expected # cells tried under prior-optimal order ---
def guessG(weights):
    # weights: dict cell->prob (unnormalized). G = sum_i i*p_(i) over descending order
    items=sorted(weights.values(), reverse=True); s=sum(items); 
    p=np.array(items)/s; return np.sum((np.arange(1,len(p)+1))*p)
# empirical cell prior (as-sampled = proportional to cell width = natural P(cell|N))
G_emp=guessG(cellcount)
# blind: uniform over the ~20000 possible cells
Mtot=sum(totient(n) for n in range(1,257))
G_blind=(Mtot+1)/2
print(f"\n=== (n,k) GUESSING cost (expected # cells before hitting true) ===")
print(f"  blind (uniform over {Mtot} cells):         G={G_blind:.0f}  = {math.log2(G_blind):.2f} bits")
print(f"  knowing N (natural P(cell|N=160)):         G={G_emp:.0f}  = {math.log2(G_emp):.2f} bits")

# --- add selection lean, DRIFT-ADJUSTED for a high puzzle (n>=250 boost weakened) ---
def lr(n):
    w=1.0
    if isprime(int(n)): w*=0.60
    if n%2==0: w*=1.27
    if float(totient(int(n)))/int(n)<0.6: w*=1.25
    if n>=250: w*=1.20   # drift-adjusted DOWN from pooled 1.93 for high puzzle 160
    return w
w2={c:cnt*lr(c[0]) for c,cnt in cellcount.items()}
G_sel=guessG(w2)
print(f"  knowing N + selection lean (drift-adj):    G={G_sel:.0f}  = {math.log2(G_sel):.2f} bits")
print(f"\n  REDUCTION vs blind: N alone = {math.log2(G_blind/G_emp):+.2f} bits ({G_blind/G_emp:.2f}x)")
print(f"                      N+selection = {math.log2(G_blind/G_sel):+.2f} bits ({G_blind/G_sel:.2f}x)")

# --- the d-RANGE each (n,k) hypothesis bounds ---
print(f"\n=== per-hypothesis d-RANGE bound (scope reduction WITHIN a chosen cell) ===")
# cell width w(n,k) ~ 1/(n*n_next); use median over sampled cells' actual D-window
import statistics
# width in d-space = A * (u-cell width); approximate by 1/(n*(n+1))*A upper bound
for nn in (256,200,150,100):
    w=A//(nn*(nn+1))
    print(f"  if n={nn}: d confined to base +/- ~{w.bit_length()} bits  => pins top ~{159-w.bit_length()} bits of d")
print(f"\n  => picking a cell reduces d-scope from 159 bits to ~(159 - {159-A.bit_length()+ (A//(256*257)).bit_length()}) ... i.e. ~top 16 bits pinned per hypothesis;")
print(f"     the PRIOR makes finding the right cell ~{G_blind/G_sel:.1f}x cheaper (the genuine fractional reduction).")
print("\nDONE")
