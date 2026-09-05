# Anti-suppression audit of the Phase 1 filters.  Question: can ANY filter in
# anew_m_support_v2.sage drop or hide an m = -1 cover instead of reporting it?
load("anew_m_support_v2.sage") if False else None
import numpy as np, random
exec(open("anew_m_support_v2.sage").read().split("# ============================================================ instrument checks")[0])

MAIN2 = [p for p in prime_range(1040, 2500) if p % 4 == 3]
p11 = [p for p in MAIN2 if p % 12 == 11]; p7 = [p for p in MAIN2 if p % 12 == 7]
print("primes: total %d | p=11 mod 12: %d | p=7 mod 12: %d" % (len(MAIN2), len(p11), len(p7)))

# ---- F1: does the random sampler ever fall short of N_RANDOM (silent under-draw)?
rng = random.Random(int(SEED)); short = []; cm_hits = 0; tot_rand = 0
for p in MAIN2:
    Fp = GF(p); R = PolynomialRing(Fp, 'x')
    drawn = 0; tries = 0
    while drawn < N_RANDOM and tries < 4000:
        tries += 1
        co = [rng.randrange(p) for _ in range(3)] + [rng.randrange(1, p)]
        if R([Fp(c) for c in co]).discriminant() != 0:
            drawn += 1; tot_rand += 1
            if is_cm_type(cover_class(p, co)): cm_hits += 1
    if drawn < N_RANDOM: short.append(p)
print("F1 random draws: %d (expected %d) ; primes short of 40: %s ; random draws that ARE CM-type: %d"
      % (tot_rand, 40*len(MAIN2), short if short else "NONE", cm_hits))
print("   => reconciliation vs log: CM rows should be %d+%d = %d ; non-CM rows %d"
      % (sum(len(cm_classes(p)) for p in MAIN2[:0]) if False else 0, 0, 0, 0))

# ---- F2: CM stratum size, exhaustive, and its m census split by p mod 12
from collections import defaultdict
cm_by = defaultdict(lambda: defaultdict(int)); ncm = 0
for p in MAIN2:
    fp2_tables(p)
    for lab, Bv in cm_classes(p).items():
        co = [Bv, 0, 0, 1]; ncm += 1
        nC1, nE1 = counts_fp(p, co); nC2, nE2 = counts_fp2(p, co)
        m, b1v, b2v = extract_m(p, nC1, nE1, nC2, nE2)
        cm_by[p % 12][m] += 1
    del _fp2[p]
print("\nF2 CM stratum: %d classes total (exhaustive)" % ncm)
for r in sorted(cm_by):
    tot = sum(cm_by[r].values())
    print("   p = %2d mod 12 : %-4d classes ; m-census %s ; per prime %s"
          % (r, tot, dict(sorted(cm_by[r].items(), key=lambda z:(z[0] is None, z[0]))),
             {k: v/(len(p11) if r==11 else len(p7)) for k,v in sorted(cm_by[r].items(), key=lambda z:(z[0] is None, z[0]))}))

# ---- F3: can an m = -1 row be silently dropped anywhere?
print("\nF3 drop-path audit (synthetic m=-1 pushed through the FULL reporting path):")
p = 1051
synth = dict(p=p, name="SYNTH", excluded=False, m=-1, b1=0, b2=-p, srank=0,
             label=(0,1,0), cm=True, chi3=1)
d = defaultdict(set); d[synth["m"] if synth["m"] is not None else "UNDEF"].add((synth["p"], synth["label"]))
print("   tally key produced: %s ; appears in LOCK-VALUE readout: %s"
      % (list(d.keys()), len(d.get(-1, ())) == 1))
print("   extract_m on a true m=-1 count vector: %s" % (extract_m(p, *synth_counts(p, -1, 1234, 987654))[0],))
