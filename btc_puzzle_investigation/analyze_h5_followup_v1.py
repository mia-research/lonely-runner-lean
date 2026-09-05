#!/usr/bin/env python3
# analyze_h5_followup_v1.py -- analyze h5_followup_results_v1.jsonl per PREREG decision rules.
# Exact ints for quo/orbit; float only in logmean, ranked against the harness sign-flip null.
import json, math, random
from collections import defaultdict

recs = [json.loads(l) for l in open("h5_followup_results_v1.jsonl")]

# index: (arm,p,V) -> list of records
idx = defaultdict(list)
for r in recs:
    idx[(r["arm"], r["p"], r["V"])].append(r)
Vs = sorted({r["V"] for r in recs})
Ps = sorted({r["p"] for r in recs})

def logmean(qs): return math.log(sum(qs)/len(qs)) if qs else None

def signflip(deltas, R=20000, seed=12345, two_sided=False):
    if not deltas: return None, None
    obs = sum(deltas)/len(deltas); random.seed(seed); ge = 0
    for _ in range(R):
        s = sum(d*random.choice((1,-1)) for d in deltas)/len(deltas)
        ge += 1 if ((abs(s) >= abs(obs)-1e-12) if two_sided else (s >= obs-1e-12)) else 0
    return obs, (ge+1.0)/(R+1.0)

def base_curves(p, V):
    d = {}
    for r in idx[("baseline", p, V)]:
        key = "j0" if r["lab"]=="j0" else ("ctrl" if r.get("is_ctrl") else ("j1728" if r["lab"]=="j1728" else "nonCM_%d_%d"%(r["A"],r["B"])))
        d.setdefault(key, []).append(r)
    return d

# ---------------- C6 pipeline plant ----------------
print("="*94); print("C6 PIPELINE PLANT — reproduce the leaky log's T1_j0 (baseline j0 vs nearest-#E ctrl)"); print("="*94)
log_ref = {4:0.2074, 5:0.4094, 6:0.5668}
for V in Vs:
    deltas=[]
    for p in Ps:
        bc = base_curves(p,V)
        j0=[r for r in idx[("baseline",p,V)] if r["lab"]=="j0"]
        ct=[r for r in idx[("baseline",p,V)] if r.get("is_ctrl")]
        if j0 and ct:
            deltas.append(logmean(j0[0]["quos"]) - logmean(ct[0]["quos"]))
    obs,_=signflip(deltas)
    ref=log_ref.get(V)
    ok = (ref is not None and abs(obs-ref)<0.02)
    print("  |V|=%d  T1_j0(mine)=%.4f   log=%.4f   diff=%.4f   %s"
          % (V, obs, ref if ref else float('nan'), (obs-ref) if ref else float('nan'), "OK" if ok else "CHECK"))

# ---------------- C4 negative control + baseline T1 pos count ----------------
print("\n"+"="*94); print("C4 negative control (nonCM-vs-nonCM must stay null)"); print("="*94)
for V in Vs:
    c4=[]
    for p in Ps:
        non=[r for r in idx[("baseline",p,V)] if r["lab"]=="nonCM" and not r.get("is_ctrl")]
        non=sorted(non, key=lambda r:r["order"])
        if len(non)>=2:
            c4.append(logmean(non[0]["quos"]) - logmean(non[1]["quos"]))
    obs,pv=signflip(c4, two_sided=True)
    print("  |V|=%d  C4=%.4f  perm_p=%.3f  (%s)" % (V, obs, pv, "null OK" if pv>0.1 else "FIRED - check"))

# ---------------- +0.5 injected plant ----------------
print("\n"+"="*94); print("+0.5 injected plant (paired sign-flip must detect a planted +0.5 shift on j0)"); print("="*94)
for V in [Vs[0]]:
    deltas=[]
    for p in Ps:
        j0=[r for r in idx[("baseline",p,V)] if r["lab"]=="j0"]
        ct=[r for r in idx[("baseline",p,V)] if r.get("is_ctrl")]
        if j0 and ct: deltas.append((logmean(j0[0]["quos"])+0.5) - logmean(ct[0]["quos"]))
    obs,pv=signflip(deltas)
    print("  |V|=%d  planted mean=%.4f (expect ~T1+0.5)  perm_p=%.4f  (%s)" % (V,obs,pv,"detected" if pv<0.001 else "MISS"))

# ================= EXPERIMENT 1 =================
print("\n"+"#"*94); print("# EXPERIMENT 1 — factor isolation"); print("#"*94)

# E_F1 : per prime  logmean(quo_B1) - mean_i logmean(quo_randB_i)  ; two-sided
print("\n--- E_F1 (twist: B=1 vs random j=0 twists; control-free within-class) ---")
for V in Vs:
    deltas=[]
    for p in Ps:
        j0=[r for r in idx[("baseline",p,V)] if r["lab"]=="j0"]
        rb=[r for r in idx[("F1",p,V)] if r["lab"]=="j0rand"]
        if j0 and rb:
            lm_b1=logmean(j0[0]["quos"])
            lm_rb=[logmean(r["quos"]) for r in rb]
            deltas.append(lm_b1 - sum(lm_rb)/len(lm_rb))
    obs,pv=signflip(deltas, two_sided=True)
    pos=sum(1 for d in deltas if d>0)
    print("  |V|=%d  E_F1=%.4f  perm_p=%.4f  (pos %d/%d)  R_B=%d" % (V,obs,pv,pos,len(deltas), len([r for r in idx[('F1',Ps[0],V)]])))

# E_F2a : bracket-interp vs nearest, bracketable primes only ; two-sided ; report nonzero count
print("\n--- E_F2a (matching rule: #E-interp bracket vs greedy nearest, P_brk only) ---")
for V in Vs:
    deltas=[]; nz=0
    for p in Ps:
        recsV=idx[("baseline",p,V)]
        j0=[r for r in recsV if r["lab"]=="j0"][0]
        non=[r for r in recsV if r["lab"]=="nonCM"]
        oj0=j0["order"]
        lower=[r for r in non if r["order"]<=oj0]; upper=[r for r in non if r["order"]>=oj0]
        if not lower or not upper: continue  # not bracketable
        lo=max(lower,key=lambda r:r["order"]); up=min(upper,key=lambda r:r["order"])
        ct=[r for r in recsV if r.get("is_ctrl")][0]
        dlo=abs(lo["order"]-oj0); dup=abs(up["order"]-oj0)
        if lo["order"]==up["order"]:
            qb=logmean(lo["quos"])
        else:
            wlo=1.0/(dlo+1e-9); wup=1.0/(dup+1e-9)
            qb=(wlo*logmean(lo["quos"])+wup*logmean(up["quos"]))/(wlo+wup)
        d=qb-logmean(ct["quos"])
        deltas.append(d); nz+= (abs(d)>1e-9)
    obs,pv=signflip(deltas, two_sided=True)
    print("  |V|=%d  E_F2a=%.4f  perm_p=%.4f  n=%d nonzero=%d" % (V,obs,pv,len(deltas),nz))

print("\n--- E_F2b (prime-drop) : see analyze_h5_F2b_primedrop_v1.py (FREE arm; -0.05/-0.11/-0.13, non-sig, negative) ---")

# E_F8 : per prime logmean(quo_j0_gens) - logmean(quo_j0_randpoint) ; and paired T1 flip ; |V| in {4,5}
print("\n--- E_F8 (sampling: gens-mult vs random_point) ---")
for V in Vs:
    if not idx[("F8",Ps[0],V)]:
        print("  |V|=%d  (F8 not run)"%V); continue
    d_j0=[]; d_t1=[]
    for p in Ps:
        bj0=[r for r in idx[("baseline",p,V)] if r["lab"]=="j0"]
        fj0=[r for r in idx[("F8",p,V)] if r["lab"]=="j0"]
        bct=[r for r in idx[("baseline",p,V)] if r.get("is_ctrl")]
        fct=[r for r in idx[("F8",p,V)] if r.get("is_ctrl")]
        if bj0 and fj0: d_j0.append(logmean(bj0[0]["quos"]) - logmean(fj0[0]["quos"]))
        if fj0 and fct: d_t1.append(logmean(fj0[0]["quos"]) - logmean(fct[0]["quos"]))
    o1,p1=signflip(d_j0, two_sided=True); o2,p2=signflip(d_t1)
    # cyclic fraction of j0
    ncyc=sum(1 for r in recs if r["arm"]=="baseline" and r["lab"]=="j0" and r["V"]==V and r.get("cyclic")==False)
    print("  |V|=%d  E_F8(j0 gens-rand)=%.4f perm_p=%.3f | T1_underF8=%.4f perm_p=%.3f | j0 noncyclic:%d/%d"
          % (V,o1,p1,o2,p2, ncyc, len(Ps)))

# reconstruction check
print("\n--- reconstruction check: E_F1 + E_F2a + E_F2b + E_F8  vs  T1_leaky_full ---")
F2b_ref={4:-0.0515,5:-0.1100,6:-0.1321}
for V in Vs:
    # recompute the four (quick)
    # T1 full
    t1=[]; f1=[]; f2a=[]; f8=[]
    for p in Ps:
        j0=[r for r in idx[("baseline",p,V)] if r["lab"]=="j0"]
        ct=[r for r in idx[("baseline",p,V)] if r.get("is_ctrl")]
        if j0 and ct: t1.append(logmean(j0[0]["quos"])-logmean(ct[0]["quos"]))
        rb=[r for r in idx[("F1",p,V)] if r["lab"]=="j0rand"]
        if j0 and rb:
            f1.append(logmean(j0[0]["quos"]) - sum(logmean(r["quos"]) for r in rb)/len(rb))
    T1=sum(t1)/len(t1); F1=sum(f1)/len(f1)
    print("  |V|=%d  T1_full=%.4f  E_F1=%.4f  (E_F2b=%.4f)  [E_F2a,E_F8 above]" % (V,T1,F1,F2b_ref.get(V,float('nan'))))

# ================= EXPERIMENT 2 =================
print("\n"+"#"*94); print("# EXPERIMENT 2 — orbit-reduced quo (S_m); D2 = log rho_j0 - log rho_ctrl"); print("#"*94)
print("%-4s %-9s %-9s %-9s | %-9s %-9s %-9s %-8s | %-8s"
      % ("|V|","T1(quo)","T2(orbit)","D2","perm_p(D2)","rho_j0","rho_ctrl","nonrad","dup%_j0"))
for V in Vs:
    t1=[]; t2=[]; d2=[]; rj=[]; rc=[]; nonrad=0; totcells=0
    for p in Ps:
        j0=[r for r in idx[("baseline",p,V)] if r["lab"]=="j0"]
        ct=[r for r in idx[("baseline",p,V)] if r.get("is_ctrl")]
        if not (j0 and ct and j0[0]["orbits"] and ct[0]["orbits"]): continue
        qj=j0[0]["quos"]; oj=j0[0]["orbits"]; qc=ct[0]["quos"]; oc=ct[0]["orbits"]
        # non-radical detection
        for r in (j0[0],ct[0]):
            if r["vsizes"]:
                for q,vs in zip(r["quos"],r["vsizes"]):
                    totcells+=1; nonrad += (q!=vs)
        lm_qj=logmean(qj); lm_oj=logmean(oj); lm_qc=logmean(qc); lm_oc=logmean(oc)
        t1.append(lm_qj-lm_qc); t2.append(lm_oj-lm_oc)
        d2.append((lm_qj-lm_oj)-(lm_qc-lm_oc))
        rj.append(lm_qj-lm_oj); rc.append(lm_qc-lm_oc)
    T1=sum(t1)/len(t1); T2=sum(t2)/len(t2)
    D2obs,D2p=signflip(d2)  # one-sided >=0
    print("%-4d %-9.4f %-9.4f %-9.4f | %-9.4f %-9.4f %-9.4f %-8s | %.1f%%"
          % (V,T1,T2,D2obs,D2p, math.exp(sum(rj)/len(rj)), math.exp(sum(rc)/len(rc)),
             "%d/%d"%(nonrad,totcells), 100*(1-math.exp(-sum(rj)/len(rj)))))
print("\nreading: D2~0 & T2~T1 -> excess SURVIVES orbit reduction (distinct usable relations, real lever).")
print("         D2~T1 & T2~0 -> excess is S_m permutation DUPLICATES (no lever).")
