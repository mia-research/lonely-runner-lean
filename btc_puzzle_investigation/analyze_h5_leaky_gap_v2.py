#!/usr/bin/env python3
# analyze_h5_leaky_gap_v2.py
#
# Move 7 / do-not-close #5: on the LEAKY headline run (semaev_cm_relation_yield_v4.log,
# fixed B=1 design, T1_j0 = 0.207->0.834), test DIRECTLY whether the one-sided #E-leak
# drives the lever, using the per-prime #Egap the log prints.
#
# Leak model: T1_leak(p) ~ (const)*#Egap(p), with #Egap FROZEN across |V|.
# If the leak drives T1_j0, then across primes T1_j0(p) must rise with #Egap(p),
# and the fitted slope*mean(#Egap) must reproduce the level 0.207..0.834.
#
# Decision (pre-stated):
#   The leak explains the growth ONLY IF, at each |V|, the #Egap-explained part
#   (slope*mean#Egap) is a large fraction of T1_j0 AND grows across |V|.
#   Since #Egap is frozen across |V|, growth can come from the leak ONLY via a
#   growing slope; the residual INTERCEPT is by construction #E-gap-independent
#   (= the non-leak baseline).  If the intercept carries the 0.207->0.834 growth,
#   the #E-leak does NOT explain the lever.

import re, math
from collections import defaultdict

LOG = "semaev_cm_relation_yield_v4.log"
row_re = re.compile(r"p=(\d+)\s+T1_j0=(-?[\d.]+)\s+T1_j1728=(-?[\d.]+)\s+R2=(-?[\d.]+)\s+#Egap=(-?[\d.]+)")

cur_V = None
data = defaultdict(list)   # V -> list of (p, T1_j0, egap)
with open(LOG) as fh:
    for line in fh:
        mtag = re.search(r"tag=V=(\d+)\s", line)
        if mtag:
            cur_V = int(mtag.group(1)); continue
        m = row_re.search(line)
        if m and cur_V is not None:
            p = int(m.group(1)); t1 = float(m.group(2)); eg = float(m.group(5))
            data[cur_V].append((p, t1, eg))

def ols(xs, ys):
    n = len(xs); mx = sum(xs)/n; my = sum(ys)/n
    sxx = sum((x-mx)**2 for x in xs); sxy = sum((x-mx)*(y-my) for x,y in zip(xs,ys))
    b = sxy/sxx if sxx else float("nan")
    a = my - b*mx
    ss_tot = sum((y-my)**2 for y in ys)
    ss_res = sum((y-(a+b*x))**2 for x,y in zip(xs,ys))
    r2 = 1 - ss_res/ss_tot if ss_tot else float("nan")
    # Pearson r
    syy = sum((y-my)**2 for y in ys)
    r = sxy/math.sqrt(sxx*syy) if sxx and syy else float("nan")
    return a, b, r, r2

def spearman(xs, ys):
    def ranks(v):
        order = sorted(range(len(v)), key=lambda i: v[i])
        rk = [0]*len(v)
        for pos, i in enumerate(order): rk[i] = pos
        return rk
    rx, ry = ranks(xs), ranks(ys)
    _,_,r,_ = ols([float(x) for x in rx],[float(y) for y in ry])
    return r

print("="*100)
print("LEAKY headline run: does T1_j0(p) track the frozen #Egap(p)?  (the one-sided #E-leak test)")
print("="*100)
print("%-4s %-4s %-8s %-8s | %-9s %-9s %-8s %-8s | %-10s %-10s %-10s"
      % ("|V|","n","T1_j0","mean_gap","slope","intercept","Pears_r","Spear","leak=slope*gap","intercept","resid_growth"))
Vs = sorted(data)
base_intercept = None
for V in Vs:
    rows = data[V]
    ps = [r[0] for r in rows]; t1 = [r[1] for r in rows]; eg = [r[2] for r in rows]
    a, b, r, r2 = ols(eg, t1)
    sp = spearman(eg, t1)
    mean_gap = sum(eg)/len(eg); mean_t1 = sum(t1)/len(t1)
    leak_part = b*mean_gap                      # part of mean T1 attributable to #Egap
    print("%-4d %-4d %-8.4f %-8.4f | %-9.3f %-9.4f %-8.3f %-8.3f | %-10.4f %-10.4f %-10s"
          % (V, len(rows), mean_t1, mean_gap, b, a, r, sp, leak_part, a, ""))

print()
print("Interpretation columns: 'leak=slope*gap' = mean T1 explained by the #E-gap channel;")
print("'intercept' = mean T1 with #E-gap set to 0 (the NON-leak baseline).")
print()

# Growth decomposition: how much of the 0.207->0.834 rise is in the gap-channel vs the intercept?
a4,b4,_,_ = ols([r[2] for r in data[Vs[0]]],[r[1] for r in data[Vs[0]]])
aL,bL,_,_ = ols([r[2] for r in data[Vs[-1]]],[r[1] for r in data[Vs[-1]]])
mg = sum(r[2] for r in data[Vs[0]])/len(data[Vs[0]])   # frozen, same each level
mgL = sum(r[2] for r in data[Vs[-1]])/len(data[Vs[-1]])
leak4 = b4*mg; leakL = bL*mgL
print("="*100)
print("GROWTH DECOMPOSITION  (|V|=%d -> |V|=%d)" % (Vs[0], Vs[-1]))
print("="*100)
mt4 = sum(r[1] for r in data[Vs[0]])/len(data[Vs[0]])
mtL = sum(r[1] for r in data[Vs[-1]])/len(data[Vs[-1]])
print("  T1_j0:            %.4f -> %.4f   (span %.4f)" % (mt4, mtL, mtL-mt4))
print("  #E-gap channel:   %.4f -> %.4f   (span %.4f)" % (leak4, leakL, leakL-leak4))
print("  intercept (base): %.4f -> %.4f   (span %.4f)" % (a4, aL, aL-a4))
span = mtL - mt4
print("  --> #E-gap channel explains %.1f%% of the |V|-growth; baseline explains %.1f%%"
      % (100*(leakL-leak4)/span, 100*(aL-a4)/span))
print("  --> #E-gap channel explains %.1f%% of the |V|=%d LEVEL (0.207-class)"
      % (100*leak4/mt4, Vs[0]))

# Also: mean #Egap magnitude vs the level -- even a MAXIMAL sensitivity check.
print()
print("="*100)
print("MAGNITUDE CEILING: even if quo were EXACTLY ~1/#E (beta=-1), the leak is bounded by")
print("  |T1_leak| <= |log(#E_ctrl/#E_j0)| ~ #Egap (relative). Compare to T1_j0:")
print("="*100)
for V in Vs:
    rows = data[V]
    mean_gap = sum(r[2] for r in rows)/len(rows)
    mean_t1 = sum(r[1] for r in rows)/len(rows)
    print("  |V|=%d: mean #Egap=%.4f  (ceiling on |T1_leak| at beta=-1)   vs   T1_j0=%.4f   ratio T1/ceiling=%.1fx"
          % (V, mean_gap, mean_t1, mean_t1/mean_gap if mean_gap else float("nan")))
