import knd_common as K
c=K.load_decomp(64); X=c["X"];Y=c["Y"];DS=c["d"];M=len(X)
h=M//2
def excl(a,b): return K.min_resid(a,b)[0]
print("(X*Y) mod 7 vs d mod 7 — decisive (exclusion), CSV-order split (low vs high N):")
for lab,sl in (("full",slice(0,M)),("half1",slice(0,h)),("half2",slice(h,M))):
    xy=[(X[i]*Y[i])%7 for i in range(M)][sl]; dq=[DS[i]%7 for i in range(M)][sl]
    o,p=K.perm_p(xy,dq,excl,B=1000,worse="le")
    print(f"  {lab:6s}: min-resid={o:+.2f} exclusion perm p={p:.3f}")
import random; rnd=random.Random(1)
idx=list(range(M)); rnd.shuffle(idx); a=idx[:h]; b=idx[h:]
for lab,ids in (("randA",a),("randB",b)):
    xy=[(X[i]*Y[i])%7 for i in ids]; dq=[DS[i]%7 for i in ids]
    o,p=K.perm_p(xy,dq,excl,B=1000,worse="le")
    print(f"  {lab:6s}: min-resid={o:+.2f} exclusion perm p={p:.3f}")
