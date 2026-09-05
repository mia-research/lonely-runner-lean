import math
from collections import defaultdict
p,b,n,beta,lam = load("/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/a2e97e4b-0256-4ffa-8e2a-5d92f74d8482/scratchpad/curvedata.sobj")
F=GF(p); E=EllipticCurve(F,[0,b]); G=E.gens()[0]
omega=beta  # primitive cube root of 1 in F_p
# precompute discrete-log table d -> P_d  and inverse
P=E(0); pts=[None]*n
cur=E(0)
for d in range(n):
    pts[d]=cur; cur=cur+G
def chi3(xv):
    if xv==0: return 0
    v=xv**((p-1)//3)   # in {1,omega,omega^2}
    if v==1: return 0
    if v==omega: return 1
    return 2
def jphase(d):
    x,y=pts[d].xy(); return chi3(x)
def sparity(d):
    x,y=pts[d].xy(); return 1 if Integer(y)>p//2 else 0

# ---------- T1: the congruence law  d ≡ d0*(-1)^j - floor(d0*lam^j/n) (mod 3) ----------
print("=== T1: congruence law d ≡ d0*(-1)^j - floor(d0*lam^j/n) (mod 3) ===")
import random
random.seed(int(1))
ok=0; tot=0
for _ in range(2000):
    d=random.randrange(1,n); d0=random.randrange(1,n)
    j=jphase(d)
    rhs=(d0*(-1)**j - (d0*lam**j)//n) % 3
    tot+=1; ok+= (rhs==d%3)
print("  law holds for %d/%d  (chance=1/3=%.3f)"%(ok,tot,tot/3.0))

# ---------- T2: orbit-conditioned correlation ±0.58 (=1/sqrt3?) ----------
print("=== T2: orbit-conditioned correlation of a readout vs d mod 3 ===")
# reproduce a +-0.58 style number: condition on j, correlate s (or chi3) sign with d%3
for cond_j in [0,1,2]:
    xs=[]; ys=[]
    for d in range(1,n):
        if jphase(d)!=cond_j: continue
        xs.append(1 if sparity(d)==0 else -1)
        ys.append(1 if (d%3==0) else -1)
    mx=sum(xs)/len(xs); my=sum(ys)/len(ys)
    num=sum((a-mx)*(c-my) for a,c in zip(xs,ys))
    den=math.sqrt(sum((a-mx)**2 for a in xs)*sum((c-my)**2 for c in ys))
    print("  j=%d : corr(s, d%%3) = %.3f   (n=%d)   [1/sqrt3=%.3f]"%(cond_j, (num/den if den else 0),len(xs),1/math.sqrt(3)))

# ---------- T3: is the Semaev 'carry' epsilon = [d+d0>=n] OBSERVABLE from points? ----------
print("=== T3: carry observability. true carry eps(d)=[d+d0>=n]; can any point-readout recover it? ===")
d0=54321
def mi_bits(feat_vals, target_vals):
    # mutual information I(feat;target) in bits
    from collections import Counter
    joint=Counter(zip(feat_vals,target_vals)); fx=Counter(feat_vals); fy=Counter(target_vals)
    N=len(feat_vals); I=0.0
    for (a,c),cnt in joint.items():
        pxy=cnt/N; px=fx[a]/N; py=fy[c]/N
        I+=pxy*math.log2(pxy/(px*py))
    return I
carry=[]; feat_jQ=[]; feat_sQ=[]; feat_jP=[]; feat_par=[]
for d in range(1,n):
    eps=1 if d+d0>=n else 0
    Q=pts[d]+pts[d0]
    if Q==E(0): continue
    xQ,yQ=Q.xy()
    carry.append(eps)
    feat_jQ.append(chi3(xQ))                      # cubic char of sum's x
    feat_sQ.append(1 if Integer(yQ)>p//2 else 0)  # sign of sum's y
    feat_jP.append(jphase(d))                     # cubic char of target's x
    feat_par.append((chi3(xQ), 1 if Integer(yQ)>p//2 else 0, jphase(d)))  # ALL readouts jointly
print("  H(carry)=%.4f bit ; MI with:"%(mi_bits(carry,carry)))
print("    chi3(x_sum)         : %.5f bit"%mi_bits(feat_jQ,carry))
print("    sign(y_sum)         : %.5f bit"%mi_bits(feat_sQ,carry))
print("    chi3(x_target)      : %.5f bit"%mi_bits(feat_jP,carry))
print("    ALL joint readouts  : %.5f bit   (if ~0 -> carry NOT observable)"%mi_bits(feat_par,carry))

# ---------- T4: the COLLAPSE. all readouts + K anchors -> candidate set size vs claimed 1-3 ----------
print("=== T4: actual candidate collapse. Readout vector R(d)=(j,s, carries vs K anchors) ===")
random.seed(int(7))
for K in [1, 8, 32, 64]:
    anchors=[random.randrange(1,n) for _ in range(K)]
    classes=defaultdict(list)
    for d in range(1,n):
        rv=(jphase(d), sparity(d)) + tuple(1 if d+a0>=n else 0 for a0 in anchors)
        classes[rv].append(d)
    sizes=[len(v) for v in classes.values()]
    # pick a random target, how many candidates share its readout?
    tgt=random.randrange(1,n)
    trv=(jphase(tgt),sparity(tgt))+tuple(1 if tgt+a0>=n else 0 for a0 in anchors)
    print("  K=%2d anchors: #classes=%d  max_class=%d  median_class=%d  candidates_for_target=%d  (claim:1-3)"
          %(K, len(classes), max(sizes), sorted(sizes)[len(sizes)//2], len(classes[trv])))
