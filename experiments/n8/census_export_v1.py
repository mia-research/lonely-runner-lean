"""Machine-readable export of the census families, recomputed and cross-checked.

The batch machine (~/ZCodeProject/lrc-n8/scripts/batch_machine_v1.py) writes a Python-repr dump that
gives |U| but not U itself, so it cannot drive Lean emission. This recomputes every family from its
cover -- independently, exact rationals -- emits JSON, and CROSS-CHECKS |U| and K against that dump.
The parallel repo is read, never written.

Scaling: a cover pins ratios b/c of the largest difference. With M = lcm of the denominators, the
family is {M*b/c ...} together with M itself and the free x. The flank e is M times its fraction.

Per flank it records: e, the period P (= lcm of the denominators of fract(d/e), which divides e),
the uncovered residues U, q = e/P (on-lattice x are the multiples of q), and the killers K.
"""
import ast, json, os, sys
from fractions import Fraction as F
from math import lcm, gcd

n = 8; INV = F(1, n)
SRC = os.path.expanduser("~/ZCodeProject/lrc-n8/results/batch_machine_v1.out")

def fract(z): return z - (z.numerator // z.denominator)
def cd(z):    return min(fract(z), 1 - fract(z))
def clear(d, e, k): return cd(d * ((F(k) + INV) / e)) >= INV

def analyse(cover):
    pinned = sorted(F(b, c) for (c, b) in cover)
    M = 1
    for p in pinned: M = lcm(M, p.denominator)
    diffs = sorted({int(p * M) for p in pinned} | {M})
    out = {"cover": [list(c) for c in cover], "M": M, "differences": diffs, "flanks": []}
    for ef in pinned:
        e = int(ef * M)
        if e == 0: continue
        fixed = [F(d) for d in diffs]
        P = 1
        for d in fixed:
            f = fract(d / e)
            if f != 0: P = lcm(P, f.denominator)
        dead = any((d / e).denominator == 1 and (d / e).numerator % n == 0 for d in fixed)
        U = [] if dead else [r for r in range(P) if all(clear(d, e, r) for d in fixed)]
        q = e // P
        K = []
        if U:
            t = 1
            while q * t < M:
                xv = F(q * t)
                if all(any(clear(xv, e, r + j * P) for j in range(1)) is False for r in U):
                    pass
                # x kills the flank iff it blocks EVERY residue class in U
                kills = all(not any(clear(xv, e, r + j * P) for j in range(P + 2)) for r in U)
                if kills: K.append(str(F(q * t, M)))
                t += 1
        out["flanks"].append({"e": e, "e_frac": str(ef), "P": P, "q": q,
                              "U": U, "U_size": len(U), "dead": dead, "K": K,
                              "always_free": (not dead) and bool(U) and not K})
    out["settled_by_free_flank"] = any(f["always_free"] for f in out["flanks"])
    return out

lines = [l for l in open(SRC) if l.strip().startswith("(((")]
print(f"source rows: {len(lines)}")
fams = []; mism = []
for l in lines:
    cover, rep = ast.literal_eval(l.strip())
    a = analyse(cover)
    a["machine_verdict"] = rep["verdict"]
    # cross-check |U| and K against the machine's own row
    for f in a["flanks"]:
        m = rep["flanks"].get(f["e_frac"])
        if m is None: continue
        if m[0] == "DEAD":
            if not f["dead"] and f["U"]: mism.append((cover, f["e_frac"], "machine DEAD, ours live"))
        else:
            if m[1] != f["U_size"]:
                mism.append((cover, f["e_frac"], f"|U| machine {m[1]} ours {f['U_size']}"))
            if sorted(m[3]) != sorted(f["K"]):
                mism.append((cover, f["e_frac"], f"K machine {m[3]} ours {f['K']}"))
    fams.append(a)

print(f"families exported: {len(fams)}")
print(f"cross-check mismatches against the machine: {len(mism)}")
for m in mism[:8]: print("   ", m)
out = "experiments/n8/census_families_v1.json"
json.dump(fams, open(out, "w"), indent=1)
print(f"written {out}")
free = [f for f in fams if f["settled_by_free_flank"]]
print(f"families with an always-free flank (Version A route): {len(free)}/{len(fams)}")
qs = {}
for f in free:
    for fl in f["flanks"]:
        if fl["always_free"]: qs[fl["q"]] = qs.get(fl["q"], 0) + 1
print(f"q = e/P over always-free flanks (q = 1 means on-lattice x are the integers): {dict(sorted(qs.items()))}")
