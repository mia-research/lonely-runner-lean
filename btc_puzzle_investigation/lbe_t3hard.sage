import math
from collections import Counter
p,b,n,beta,lam = load("/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/a2e97e4b-0256-4ffa-8e2a-5d92f74d8482/scratchpad/curvedata.sobj")
F=GF(p); E=EllipticCurve(F,[0,b]); G=E.gens()[0]
pts=[None]*n; cur=E(0)
for d in range(n): pts[d]=cur; cur=cur+G
def mi(feat,tgt):
    j=Counter(zip(feat,tgt)); fx=Counter(feat); fy=Counter(tgt); N=len(feat); I=0.0
    for (a,c),k in j.items():
        I+=(k/N)*math.log2((k/N)/((fx[a]/N)*(fy[c]/N)))
    return I
d0=54321
# POSITIVE CONTROL: a feature that DOES know the carry (d itself bucketed by threshold)
# NEGATIVE (real) features: every reasonable point-coordinate readout of P_d, P_{d0}, and their sum
carry=[]; f={}
names=["hi(x_sum)","lo(x_sum)","hi(y_sum)","hi(x_tgt)","lo(x_tgt)","hi(y_tgt)","x_sum%97","x_tgt%97","POSCTRL[d>=n-d0]"]
for nm in names: f[nm]=[]
for d in range(1,n):
    eps=1 if d+d0>=n else 0
    Q=pts[d]+pts[d0]
    if Q==E(0): continue
    xQ,yQ=map(Integer,Q.xy()); xT,yT=map(Integer,pts[d].xy())
    carry.append(eps)
    f["hi(x_sum)"].append(xQ>>10); f["lo(x_sum)"].append(xQ&1023); f["hi(y_sum)"].append(yQ>>10)
    f["hi(x_tgt)"].append(xT>>10); f["lo(x_tgt)"].append(xT&1023); f["hi(y_tgt)"].append(yT>>10)
    f["x_sum%97"].append(xQ%97); f["x_tgt%97"].append(xT%97)
    f["POSCTRL[d>=n-d0]"].append(1 if d>=n-d0 else 0)
print("H(carry)=%.4f bit.  MI of each point-readout with the true carry:"%mi(carry,carry))
# MI-bias baseline: shuffle carry, recompute, to show finite-sample floor per feature cardinality
import random; random.seed(int(0)); shuf=carry[:]; random.shuffle(shuf)
for nm in names:
    print("  %-18s MI=%.5f bit   (shuffled-baseline=%.5f)"%(nm, mi(f[nm],carry), mi(f[nm],shuf)))
