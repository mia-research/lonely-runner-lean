from sage.schemes.cyclic_covers.constructor import CyclicCover
import math

def entropy_bits(counts):
    # H(a | signature) in bits: a is uniform on N=sum(counts) values; given signature s
    # with class size c_s, residual entropy sum_s (c_s/N)*log2(c_s)
    N = sum(counts)
    return sum( (c/N)*math.log2(c) for c in counts if c>0 )

def run(p):
    F = GF(p); R = PolynomialRing(F,'x'); x = R.gen()
    sigs = {}
    for a in range(1,p):
        Lf = CyclicCover(4, x^3 + F(a)).frobenius_polynomial()
        key = tuple(ZZ(c) for c in Lf.change_ring(ZZ).list())
        sigs.setdefault(key, 0); sigs[key]+=1
    counts = list(sigs.values())
    Nsig = len(sigs); Hcond = entropy_bits(counts); Htot = math.log2(p-1)
    return Nsig, max(counts), Hcond, Htot

print("=== CONTROLS (p=67) ===")
p=67; F=GF(p)
# positive: feature = a
pos = len(set(range(1,p)))
# negative: feature = a mod 12
from collections import Counter
neg = Counter(a%12 for a in range(1,p))
print("positive control (feature=a):   N_sig=%d  (expect %d)  frac=%.3f (expect 1.0)"
      % (pos, p-1, math.log2(pos)/math.log2(p-1)))
print("negative control (feature=a%%12): N_sig=%d  (expect <=12) frac=%.3f"
      % (len(neg), math.log2(len(neg))/math.log2(p-1)))

print("\n=== REAL FEATURE: full Frobenius signature of C_a ===")
print(" p (mod12) | N_sig | maxclass | recov_bits=log2(Nsig) | H(a) | frac_pinned")
for p in [7,19,31,43,67,79,103,127,163,199,211,283,331,439,571,691,919,1231,1699]:
    if not is_prime(p) or p%12!=7: continue
    Nsig,mx,Hc,Ht = run(p)
    recov = math.log2(Nsig)
    print(" %5d (7)  | %4d  | %6d   | %6.3f              | %5.2f | %.4f"
          % (p, Nsig, mx, recov, Ht, recov/Ht))
