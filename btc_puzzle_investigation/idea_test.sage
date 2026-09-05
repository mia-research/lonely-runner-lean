# IDEA-level test: does ANY algebraic readout of the public point P_d leak the secret d?
# Include orbit-stratified conditioning (their explicit "cancels globally, spikes locally" claim).
import math
from collections import Counter
p,b,n,beta,lam = load("/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/a2e97e4b-0256-4ffa-8e2a-5d92f74d8482/scratchpad/curvedata.sobj")
F=GF(p); E=EllipticCurve(F,[0,b]); G=E.gens()[0]
pts=[None]*n; cur=E(0)
for d in range(n): pts[d]=cur; cur=cur+G
def leg(v): 
    v=Integer(v)%p
    return 0 if v==0 else (1 if power_mod(v,(p-1)//2,p)==1 else -1)
def c3(v):
    v=Integer(v)%p
    if v==0: return 0
    t=power_mod(v,(p-1)//3,p); return 0 if t==1 else (1 if t==beta else 2)
def MI(feat,tgt):
    j=Counter(zip(feat,tgt)); fx=Counter(feat); fy=Counter(tgt); N=len(feat); I=0.0
    for (a,c),k in j.items(): I+=(k/N)*math.log2((k/N)/((fx[a]/N)*(fy[c]/N)))
    return I

anchors=[11111,22222,33333]
# ----- build features (all computable from the PUBLIC point P_d) -----
feats={k:[] for k in ["chi3(x)","chi2(x)","chi2(y)","x%2","y%2","x%3","x%5","x%7",
                      "F=chi3(x)*y sign","x*y %7","x+y %7", "anchorF0","anchorF1","anchorF2",
                      "POSCTRL d%3"]}
# targets = bits of the SECRET d
tgts={k:[] for k in ["d%2","d%3","d%5","d%7","halfplane[d<n/2]","top3bits"]}
orbitclass=[]
for d in range(1,n):
    x,y=map(Integer,pts[d].xy())
    feats["chi3(x)"].append(c3(x)); feats["chi2(x)"].append(leg(x)); feats["chi2(y)"].append(leg(y))
    feats["x%2"].append(x%2); feats["y%2"].append(y%2); feats["x%3"].append(x%3)
    feats["x%5"].append(x%5); feats["x%7"].append(x%7)
    feats["F=chi3(x)*y sign"].append((c3(x), 1 if y>p//2 else 0))
    feats["x*y %7"].append((x*y)%7); feats["x+y %7"].append((x+y)%7)
    for i,a0 in enumerate(anchors):
        Q=pts[d]+pts[a0]
        if Q==E(0): feats["anchorF%d"%i].append(-1)
        else:
            xq,yq=map(Integer,Q.xy()); feats["anchorF%d"%i].append(c3(xq))
    feats["POSCTRL d%3"].append(d%3)
    tgts["d%2"].append(d%2); tgts["d%3"].append(d%3); tgts["d%5"].append(d%5); tgts["d%7"].append(d%7)
    tgts["halfplane[d<n/2]"].append(1 if d<n//2 else 0)
    tgts["top3bits"].append(d>>(n.nbits()-3))
    orbitclass.append(c3(x))  # GLV orbit branch

# shuffle baseline
import random; random.seed(int(0))
print("=== IDEA TEST: MI(algebraic readout ; secret bit) in bits.  Baseline col = shuffled target ===")
print("Positive control 'POSCTRL d%3' vs 'd%3' should light up; everything else vs everything: ~baseline?")
hdr="%-20s"%"feature \\ target" + "".join("%14s"%t for t in tgts)
print(hdr)
maxreal=0.0
for fn,fv in feats.items():
    row="%-20s"%fn
    for tn,tv in tgts.items():
        mi=MI(fv,tv)
        if fn!="POSCTRL d%3": maxreal=max(maxreal,mi)
        row+="%14.5f"%mi
    print(row)
# baseline scale: shuffle one target and show floor for the highest-cardinality feature
sh=tgts["d%7"][:]; random.shuffle(sh)
print("\nshuffle-baseline (x%%7 vs shuffled d%%7): %.5f bit  [MI estimator floor]"%MI(feats["x%7"],sh))
print("MAX MI over all REAL algebraic features x all secret bits = %.5f bit"%maxreal)

# ----- orbit-stratified: their explicit claim (flat globally, spikes within orbit) -----
print("\n=== ORBIT-STRATIFIED: does conditioning on GLV branch reveal signal that cancels globally? ===")
for tn in ["d%3","halfplane[d<n/2]"]:
    tv=tgts[tn]
    glob=MI(feats["chi2(y)"],tv)
    # within each orbit branch, MI of chi2(y) with target
    perorbit=[]
    for oc in [0,1,2]:
        idx=[i for i in range(len(orbitclass)) if orbitclass[i]==oc]
        perorbit.append(MI([feats["chi2(y)"][i] for i in idx],[tv[i] for i in idx]))
    print("  target=%-16s global MI=%.5f  | per-orbit MI=%s"%(tn,glob,["%.5f"%x for x in perorbit]))
