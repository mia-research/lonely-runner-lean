"""Intrinsic secp256k1 structure — measure and CHARACTERIZE, report any regularity.
Not a key attack: the goal is to reveal structure of the curve itself, exactly.
All integer. p, n from the curve constants."""
import hashlib
from puzzle_kangaroo_distributed import P, add, mul, G
p = P
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

def legendre(a):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p-1)//2, p) == 1 else -1

print("=== A. Frobenius trace and the global character sum of y^2 = x^3 + 7 ===")
t = p + 1 - n                      # trace of Frobenius; #E = p+1-t = n
print(f"  trace t = p+1-n = {t}")
print(f"  |t| bit-length = {t.bit_length()}  (Hasse: |t| <= 2*sqrt(p) ~ 2^128.5)")
print(f"  t = {'%+d' % t}   -> sum_x chi(x^3+7) = t - 1 = {t-1} (points with x, minus the 0 handling)")
print(f"  so mean of chi(x^3+7) over x in F_p  =  (t-1)/p  ~  {(t-1)/p:.3e} (tiny, sets valid-x density)")

print("\n=== B. valid-x density per residue class mod m (is the QR bias uniform in x mod m?) ===")
import random
rng = random.Random(12345)
S = 200000
for m in (3, 4, 7, 8, 16):
    cnt = [0]*m; val = [0]*m
    for _ in range(S):
        x = rng.randrange(p)
        c = x % m; cnt[c] += 1
        if legendre((x*x % p * x + 7)) >= 0: val[c] += 1   # valid (QR or zero)
    fr = [val[i]/cnt[i] for i in range(m)]
    # z-score of each class fraction vs 0.5
    import math
    zs = [ (fr[i]-0.5)/ (0.5/math.sqrt(cnt[i])) for i in range(m)]
    print(f"  m={m:2d}: valid-fraction/class = {[round(f,4) for f in fr]}")
    print(f"        z vs 0.5             = {[round(z,2) for z in zs]}   max|z|={max(abs(z) for z in zs):.2f}")

print("\n=== C. top-bit structure of X(dG): the p != 2^256 deficit, measured ===")
# X in [0,p). Empty band [p, 2^256) has width 2^256-p = 2^32+977. Tiny relative deficit.
gap = (1<<256) - p
print(f"  empty top band width 2^256 - p = {gap} ~ 2^{gap.bit_length()-1}")
print(f"  => P(X in top band) deficit ~ {gap/2**256:.3e} per random X; detectable only at >~2^64 samples")
# measure top byte distribution of X(dG) for a sample of random d
S2 = 100000
topbyte = [0]*256
acc = None
d0 = rng.randrange(n)
Ppt = mul(d0)
step = mul(1)  # +G each time: consecutive multiples (Weyl) -- structured sample
for _ in range(S2):
    Ppt = add(Ppt, step)
    topbyte[Ppt[0] >> 248] += 1
import statistics
exp = S2/256
chi = sum((c-exp)**2/exp for c in topbyte)
print(f"  consecutive-multiple X top-byte chi^2 = {chi:.1f} (dof 255, expect ~255+-22.6)")
print(f"    -> {'UNIFORM' if abs(chi-255)<3*22.6 else 'DEVIATION'} (Weyl equidistribution of kG)")

print("\n=== D. does the nonce leak the key? bit-correlation d_i vs k_i (14 recovered) ===")
import pickle
recs = pickle.load(open('sweep2019_recs.pkl','rb'))
known = [r for r in recs if 'k' in r]
# per bit position, count agreement d bit == k bit across the 14; look for a biased position
import collections
agree = collections.Counter()
for r in known:
    d, k = r['d'], r['k']
    for b in range(0, 128):
        if ((d>>b)&1) == ((k>>b)&1): agree[b]+=1
extreme = sorted(agree.items(), key=lambda kv: abs(kv[1]-7), reverse=True)[:5]
print(f"  14 sigs: per-bit d==k agreement (expect ~7/14). most extreme bits: {extreme}")
print("  (all near 7 => no key-nonce correlation; the 4 RFC6979 ones DO mix d by design)")
