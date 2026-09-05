#!/usr/bin/env python3
"""Seed the campaign's planted controls (gate §4). 24 positive + 12 negative.
Positions drawn deterministically from a recorded seed so the draw is auditable
after the fact without being predictable during the run."""
import json, random, hashlib
SEED = 20260905
rows = [r for r in json.load(open("null_population_v2.json")) if r["status"] == "PENDING"]
rng = random.Random(SEED)
idx = rng.sample(range(len(rows)), 36)
POS = ([("P1","value error — reported value perturbed in the payload; A/A2 must diverge")]*6 +
       [("P2","forced by construction — statistic fixed by a convention; C check 1/3 must fire")]*6 +
       [("P3","inert control — matched null rewired so it cannot change verdict; C check 2 = no")]*4 +
       [("P4","power floor — detectable threshold set above the effect ceiling; C check 4 = fail")]*4 +
       [("P5","object substitution — script computes a correlate; C check 5 must fire")]*4)
NEG = [("N0","sound by construction — exact statistic, live control, adequate power, right object")]*12
plants = []
for pos, (cls, desc) in zip(idx, POS + NEG):
    plants.append(dict(row=rows[pos]["doc"], klass=cls, expect=("FIRE" if cls!="N0" else "CLEAN"), desc=desc))
# the two ground-truth anchors named in CLAIMS.md / the open-repro package
plants.append(dict(row="ANCHOR:rho_p", klass="P2", expect="FIRE",
  desc="rho_p = chi2(-1), forced by e4=p^2 composed with canon()'s lex sort. Known FORCED."))
plants.append(dict(row="ANCHOR:F_p3_divisibility", klass="P2", expect="FIRE",
  desc="'3 | the F_p^3 sum corroborates three blocks' — forced by s1=s2=0 via e3=S3/3. Known FORCED."))
blob = json.dumps(plants, indent=1, sort_keys=True)
open("PLANT_MANIFEST_SEALED_v1.json","w").write(blob)
h = hashlib.sha256(blob.encode()).hexdigest()
open("PLANT_MANIFEST_SEALED_v1.sha256","w").write(h + "\n")
print(f"plants seeded: {len(plants)}  (24 positive + 12 negative + 2 ground-truth anchors)")
print(f"seed: {SEED}")
print(f"manifest sha256: {h}")
print("\nfiring rule (pre-committed): if fewer than 20/24 positive plants fire,")
print("the campaign null is UNINFORMATIVE and no row may be reported RECHECKED.")
