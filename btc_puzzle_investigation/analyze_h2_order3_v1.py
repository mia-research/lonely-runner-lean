#!/usr/bin/env python3
# analyze_h2_order3_v1.py -- H2 order-3 control, per PREREG decision rules.
# W_obs = signed-win of beta-orbit quo vs generic order-3 (Mobius) quo; map-label permutation null.
import json, math, random
from collections import defaultdict

recs=[json.loads(l) for l in open("h2_order3_results_v1.jsonl")]
anchors=[r for r in recs if r.get("kind")=="anchor"]
main=[r for r in recs if "q_inv" in r]

print("="*90); print("PRECONDITIONS"); print("="*90)
# R2 reproduction
print("R2 reproduction (anchors): R2 = log quo(betaInv) - log quo(rnd)  [target ~1.6-2.2, or clear boost]")
for a in anchors:
    if a["qb"] and a["qr"]:
        print("  p=%-5d quo(betaInv)=%3d quo(rnd)=%3d  R2=%.3f" % (a["p"],a["qb"],a["qr"],math.log(a["qb"]/a["qr"])))
# P-b
print("\nP-b (quo vs #relation-triples, must be non-flat/rising):")
pb_ok=0
for a in anchors:
    pb=a.get("pb")
    if pb and None not in pb:
        rising = pb[-1] > pb[0]
        pb_ok += rising
        print("  p=%-5d P-b sweep=%s  rising=%s" % (a["p"],pb,rising))
print("  P-b non-flat/rising on %d/%d primes" % (pb_ok,len([a for a in anchors if a.get('pb')])))
# P-a exactness
pa_bad=[r for r in main if r["pa"]!=[r["q_inv"],r["q_inv"]]]
print("\nP-a (phi=beta,beta^2 must equal quo(Vinv) EXACTLY): %d/%d instances exact  %s"
      % (len(main)-len(pa_bad), len(main), "OK" if not pa_bad else "BROKEN"))

def signed_win(d, others):
    return sum((1 if d>o else (-1 if d<o else 0)) for o in others)

print("\n"+"="*90); print("PRIMARY STATISTIC per |V|-arm (signed-win, map-label permutation null, B=999)"); print("="*90)
print("%-6s %-4s %-8s %-8s %-9s %-9s %-9s %-9s"
      % ("n_orb","S","W_obs","tie_rate","perm_p","R3_med","x_ratio","verdict"))
for n_orb in sorted({r["n_orb"] for r in main}):
    arm=[r for r in main if r["n_orb"]==n_orb]
    W_obs=0; n_tie=0; n_cmp=0; logdiffs=[]
    pools=[]
    for r in arm:
        qi=r["q_inv"]; qs=r["q_phis"]
        W_obs+=signed_win(qi,qs)
        n_tie+=sum(1 for q in qs if q==qi); n_cmp+=len(qs)
        for q in qs:
            if q>0 and qi>0: logdiffs.append(math.log(qi)-math.log(q))
        pools.append([qi]+qs)
    tie_rate=n_tie/n_cmp if n_cmp else float("nan")
    # permutation null: per instance pick a random designated element from the pool
    random.seed(20260824); B=999; ge=0
    for b in range(B):
        Wp=0
        for pool in pools:
            mstar=random.randrange(len(pool))
            d=pool[mstar]; others=pool[:mstar]+pool[mstar+1:]
            Wp+=signed_win(d,others)
        if Wp>=W_obs: ge+=1
    pv=(1+ge)/(1+B)
    R3_med=sorted(logdiffs)[len(logdiffs)//2] if logdiffs else float("nan")
    xr=math.exp(R3_med) if logdiffs else float("nan")
    # verdict per tie-guard + decision rule
    if tie_rate>=0.5: verdict="ABSTAIN(ties)"
    elif pv<=0.01 and R3_med>0: verdict="CM-SPECIFIC"
    elif pv>0.05: verdict="generic"
    elif pv<=0.05: verdict="suggestive"
    else: verdict="?"
    print("%-6d %-4d %-8d %-8.2f %-9.4f %-9.3f %-9.2f %-9s"
          % (n_orb,len(arm),W_obs,tie_rate,pv,R3_med,xr,verdict))

# pooled across arms with tie-rate < 0.5
print("\n"+"="*90); print("POOLED (arms with tie_rate<0.5)"); print("="*90)
pools=[]; W_obs=0; n_tie=0; n_cmp=0; logdiffs=[]
for n_orb in sorted({r["n_orb"] for r in main}):
    arm=[r for r in main if r["n_orb"]==n_orb]
    nt=sum(sum(1 for q in r["q_phis"] if q==r["q_inv"]) for r in arm)
    nc=sum(len(r["q_phis"]) for r in arm)
    if nc and nt/nc>=0.5:
        print("  arm n_orb=%d EXCLUDED (tie_rate=%.2f>=0.5)"%(n_orb,nt/nc)); continue
    for r in arm:
        qi=r["q_inv"]; qs=r["q_phis"]
        W_obs+=signed_win(qi,qs); n_tie+=sum(1 for q in qs if q==qi); n_cmp+=len(qs)
        for q in qs:
            if q>0 and qi>0: logdiffs.append(math.log(qi)-math.log(q))
        pools.append([qi]+qs)
random.seed(1); B=999; ge=0
for b in range(B):
    Wp=0
    for pool in pools:
        ms=random.randrange(len(pool)); Wp+=signed_win(pool[ms],pool[:ms]+pool[ms+1:])
    if Wp>=W_obs: ge+=1
pv=(1+ge)/(1+B)
print("  W_obs=%d  tie_rate=%.3f  perm_p=%.4f  R3_med=%.3f (x%.2f)  n_win/n_cmp: %d/%d"
      % (W_obs,n_tie/n_cmp,pv,sorted(logdiffs)[len(logdiffs)//2],
         math.exp(sorted(logdiffs)[len(logdiffs)//2]),
         sum(1 for r in main for q in r['q_phis'] if r['q_inv']>q), n_cmp))

# mechanistic readout: does quo track n_rel? (beta n_rel=3/4 high quo; generic phi n_rel~0)
print("\n"+"="*90); print("MECHANISTIC READOUT: does quo track n_rel (relation-triple count)?"); print("="*90)
pairs=[]
for r in main:
    pairs.append((r["nrel_inv"], r["q_inv"]))
    for nr,q in zip(r["nrel_phis"], r["q_phis"]):
        pairs.append((nr,q))
byrel=defaultdict(list)
for nr,q in pairs: byrel[nr].append(q)
for nr in sorted(byrel):
    qs=byrel[nr]; print("  n_rel=%d : mean quo=%.2f  median=%d  n=%d" % (nr,sum(qs)/len(qs),sorted(qs)[len(qs)//2],len(qs)))
# Pearson quo vs n_rel
xs=[a for a,_ in pairs]; ys=[b for _,b in pairs]
mx=sum(xs)/len(xs); my=sum(ys)/len(ys)
sxy=sum((a-mx)*(b-my) for a,b in pairs); sxx=sum((a-mx)**2 for a in xs); syy=sum((b-my)**2 for b in ys)
print("  Pearson(quo, n_rel) = %.3f  (n=%d)" % (sxy/math.sqrt(sxx*syy), len(pairs)))
print("  # generic phi-orbits that ARE relation-triples: %d / %d"
      % (sum(1 for r in main for nr in r['nrel_phis'] if nr>0)*1, sum(len(r['nrel_phis']) for r in main)))
