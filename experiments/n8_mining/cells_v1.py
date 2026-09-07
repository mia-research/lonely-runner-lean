#!/usr/bin/env python3
"""Stage 4 — evaluate PREREG_v1 section 3 outcome cells on the n=8 scan."""
import pickle, os
from collections import Counter
OUT = os.path.dirname(os.path.abspath(__file__))
rows = pickle.load(open(os.path.join(OUT, "n8_rows.pkl"), "rb"))
n = 8
STRICT = [r for r in rows if r["lrc_class"] in ("DI", "ModDI")]
DELTA0 = [r for r in rows if r["delta"] == 0]
print(f"n=8 rows {len(rows)}   LRCSHAPE_STRICT {len(STRICT)} "
      f"(pre-committed 66044)   DELTA0 {len(DELTA0)} (pre-committed 69387)")
print("  lrc_class:", dict(Counter(r['lrc_class'] for r in rows)))
print("  delta    :", dict(sorted(Counter(r['delta'] for r in rows).items())))

def cells(name, S):
    print("\n" + "=" * 74); print(f"STRATUM {name}   N = {len(S)}"); print("=" * 74)
    A = [r for r in S if r["N_joint"] == 0]
    print(f"CELL A  LRC-shape with N_joint = 0 : {len(A)}  -> "
          f"{'FIRES -- Conjecture 5.2-H FALSE as stated' if A else 'does not fire'}")
    if A:
        for r in A[:10]: print("   ", r)
    fails = [r for r in S if not r["pigeon"]]
    print(f"CELL B  all satisfy the pigeonhole : {'FIRES' if not fails else 'does not fire'}"
          f"   ({len(S)-len(fails)} hold, {len(fails)} fail)")
    print(f"CELL C  pigeonhole fails but N_joint >= 1 : "
          f"{len([r for r in fails if r['N_joint']>=1])}"
          f"  -> {'FIRES' if fails else 'does not fire'}")
    if fails:
        print(f"   residual rate {len(fails)}/{len(S)} = {100*len(fails)/len(S):.3f}%"
              f"   (n<=7 strict rate 53/5517 = 0.961%)")
        print("   p        :", dict(sorted(Counter(r['p'] for r in fails).items())))
        print("   (kG,kA)  :", dict(sorted(Counter((r['kG'],r['kA']) for r in fails).items())))
        print("   lrc_class:", dict(Counter(r['lrc_class'] for r in fails)))
        print("   cIG      : min %d max %d" % (min(r['cIG'] for r in fails), max(r['cIG'] for r in fails)))
        print("   all-missed mechanism:", dict(Counter(r['targets_all_missed_LA'] for r in fails)))
        print("   N_joint  : min", min(r['N_joint'] for r in fails))
    # mandatory Cell B readout: slack margins
    sm = min(r["slack"] for r in S)
    print(f"   slack_min over stratum = {sm};  counts at slack in 1,2,3: "
          f"{ {k: sum(1 for r in S if r['slack']==k) for k in (1,2,3)} }")
    by_p = {p: min(r['slack'] for r in S if r['p']==p) for p in sorted({r['p'] for r in S})}
    print("   slack_min by p       :", by_p)
    by_v = {v: min(r['slack'] for r in S if r['vmax_all']==v)
            for v in sorted({r['vmax_all'] for r in S})}
    print("   slack_min by vmax_all:", by_v)
    for s in (8, 9, 10):
        sub = [r for r in S if r["vmax_all"] <= s]
        f2 = [r for r in sub if not r["pigeon"]]
        print(f"   slice S<={s}: N={len(sub):>6}  pigeon-fail={len(f2):>4}  "
              f"CE={sum(1 for r in sub if r['N_joint']==0)}  slack_min={min(r['slack'] for r in sub)}")

cells("LRCSHAPE_STRICT (lrc_class in {DI,ModDI})", STRICT)
cells("DELTA0 (delta = 0)", DELTA0)

print("\n" + "=" * 74); print("CELL D — the delta discriminator at n = 8"); print("=" * 74)
CE = [r for r in rows if r["N_joint"] == 0]
print(f"  all n=8 counterexamples (N_joint = 0): {len(CE)}")
print("  delta-histogram:", dict(sorted(Counter(r['delta'] for r in CE).items())),
      "   (n<=7: {1:69, 2:333, 3:279})")
d1 = [r for r in rows if r["delta"] >= 1]
print(f"  delta >= 1 stratum: {len(d1)} rows (pre-committed 67144), "
      f"of which N_joint = 0: {sum(1 for r in d1 if r['N_joint']==0)}")
if not any(r["N_joint"] == 0 for r in d1):
    print("  -> D3 (vacuous): the delta discriminator is UNTESTED at n = 8")
elif not CE or all(r["delta"] >= 1 for r in CE):
    print("  -> D1: every n=8 counterexample has delta >= 1")
print("\nCELL E  pigeon AND N_joint=0 anywhere:",
      sum(1 for r in rows if r["pigeon"] and r["N_joint"] == 0), "(must be 0)")
