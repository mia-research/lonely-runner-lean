#!/usr/bin/env python3
# PRE-REG PREREG_anew_direct_invariant_partialinfo_v1 -- p-ladder VALIDATION statistics (int-only).
# Confirms: pipeline runs; COLLAPSE null at floor; MATCHED S_closed d-independent; FIRING PLANT
# detection floor; reproduces N14. NOT a verdict run (underpowered by construction, per pre-reg S4).
# Signal/decision path is integer-only: verdict decided by exceedance count E (fire <=> E==0);
# p-values reported as the integer pair (1+E, 1+K). No float anywhere. Randomness = sha256 stream.
import json, sys, hashlib

K_PERM = 9999   # permutation-null draws; fire <=> E==0 <=> perm p = 1/(K+1) < 1e-4

def rints(key, bound, count):
    # deterministic integer stream in [0,bound) from a keyed sha256 counter (no float).
    # Batches several ints per 32-byte digest for speed; same sha256-stream family.
    out = []
    i = 0
    nbytes = max(8, (bound.bit_length() + 7) // 8 + 1)
    per = max(1, 32 // nbytes)
    while len(out) < count:
        h = hashlib.sha256(("%s|%d" % (key, i)).encode()).digest()
        for j in range(per):
            if len(out) >= count: break
            out.append(int.from_bytes(h[j*nbytes:(j+1)*nbytes], "big") % bound)
        i += 1
    return out

def fisher_yates(labels, key):
    a = list(labels); nloc = len(a)
    if nloc < 2: return a
    r = rints(key, 1 << 40, nloc)  # ample entropy per slot
    for j in range(nloc - 1, 0, -1):
        k = r[nloc - 1 - j] % (j + 1)
        a[j], a[k] = a[k], a[j]
    return a

def map_decoder(train_feats, train_labels, m):
    # g(a) = argmax_b #{train: f=a, label=b}; ties -> smallest b. Unseen a -> train marginal majority.
    counts = {}
    marg = {}
    for f, b in zip(train_feats, train_labels):
        counts.setdefault(f, {}); counts[f][b] = counts[f].get(b, 0) + 1
        marg[b] = marg.get(b, 0) + 1
    g = {}
    for f, cd in counts.items():
        best_b, best_c = None, -1
        for b in range(m):
            c = cd.get(b, 0)
            if c > best_c: best_c, best_b = c, b
        g[f] = best_b
    maj = None; majc = -1
    for b in range(m):
        c = marg.get(b, 0)
        if c > majc: majc, maj = c, b
    return g, maj

def T_stat(train_feats, train_labels, test_feats, test_labels, m):
    g, maj = map_decoder(train_feats, train_labels, m)
    return sum(1 for f, b in zip(test_feats, test_labels)
               if g.get(f, maj) == b)

def perm_null(train_feats, train_labels, test_feats, test_labels, m, T_obs, key):
    # frozen decoder from TRAIN; permute TEST labels K times; E = #{T_perm >= T_obs}
    g, maj = map_decoder(train_feats, train_labels, m)
    preds = [g.get(f, maj) for f in test_feats]
    E = 0
    for t in range(K_PERM):
        perm = fisher_yates(test_labels, "%s|perm|%d" % (key, t))
        Tp = sum(1 for p_, b in zip(preds, perm) if p_ == b)
        if Tp >= T_obs: E += 1
    return E

def split_train_test(n, seed):
    idx = list(range(n))
    idx = fisher_yates(idx, "split|%d" % seed)
    half = n // 2
    return idx[:half], idx[half:]

def run_channel(feats, labels, m, seed, key):
    n = len(feats)
    tr, te = split_train_test(n, seed)
    if len(tr) < 1 or len(te) < 1: return None
    trf = [feats[i] for i in tr]; trl = [labels[i] for i in tr]
    tef = [feats[i] for i in te]; tel = [labels[i] for i in te]
    T = T_stat(trf, trl, tef, tel, m)
    E = perm_null(trf, trl, tef, tel, m, T, key)
    return {"N": n, "N_test": len(te), "T": T, "E": E, "fires": (E == 0),
            "pnum": 1 + E, "pden": 1 + K_PERM}

def is_prime(x):
    if x < 2: return False
    d = 2
    while d * d <= x:
        if x % d == 0: return False
        d += 1
    return True

def M_of_n(nE, lam):
    base = [m for m in (2, 5, 7, 11, 13) if (lam % m) not in (0, 1)]
    nm1 = nE - 1
    extra = []
    x = 5
    while len(extra) < 2 and x <= nm1:
        if is_prime(x) and nm1 % x == 0: extra.append(x)
        x += 2
    for e in extra:
        if e not in base: base.append(e)
    return sorted(base)

def plant_feature(labels_true, m, pi_num, pi_den, key):
    # f_plant = label corrupted (replaced by uniform in [0,m)) with prob (1-pi). Exact integer:
    # corrupt iff u < floor((1-pi)*D), D=pi_den, u in [0,D). pi = pi_num/pi_den (design constant).
    D = pi_den
    thr = ((pi_den - pi_num) * D) // pi_den   # floor((1-pi)*D)
    u = rints("%s|plantsel" % key, D, len(labels_true))
    rep = rints("%s|plantrep" % key, m, len(labels_true))
    out = []
    for i, b in enumerate(labels_true):
        out.append(rep[i] if u[i] < thr else b)
    return out

def main(path):
    data = json.load(open(path))
    p = data["p"]; nE = data["nE"]; lam = data["lam"]
    recs = data["records"]
    print("=== p=%d  nE=%d  lam=%d  A_new=%d (=%d*%d) ===" %
          (p, nE, lam, data["anew_order"], data["l0"], data["cof"]))
    n14 = data["n14"]
    if n14.get("hom_total") is not None:
        print("[N14 reproduction] k_multipliers=%s (expect p^2 mod A_new=%d) | affine %s/%s | hom %d/%d"
              % (n14["k_multipliers"], n14["k_expected_psq_mod_anew"],
                 n14["affine_violations"], n14["affine_total"], n14["hom_holds"], n14["hom_total"]))
    else:
        print("[N14 reproduction] not run at scale (no dlog table); f5 read DLP-free via torsion label")

    # ---- orbit-dedup: canonical rep = min{d, lam d, lam^2 d} ; keep liftable with f5 in {0,1,2} ----
    f5 = {r["d"]: r["f5_open"] for r in recs}
    f5c = {r["d"]: r["f5_closed"] for r in recs}
    seen = set(); reps = []
    for r in recs:
        d = r["d"]
        orb = tuple(sorted(((d) % nE, (lam * d) % nE, (lam * lam * d) % nE)))
        if orb in seen: continue
        seen.add(orb)
        cano = orb[0]
        if f5.get(cano) in (0, 1, 2):
            reps.append(cano)
    print("[sample] distinct liftable orbits (reps) = %d" % len(reps))

    # ---- matched-control premise: S_closed A_new-part d-independent? ----
    closed_strs = set(r["Sclosed_str"] for r in recs if r["Sclosed_str"] is not None)
    print("[matched premise] distinct S_closed A_new-parts across all d = %d  (1 => d-independent, control valid)"
          % len(closed_strs))
    f5c_vals = set(f5c.get(c) for c in reps)
    print("[matched premise] f5(S_closed) values on reps = %s  (singleton => constant => at floor)"
          % sorted(v for v in f5c_vals if v is not None))

    M = M_of_n(nE, lam)
    print("[moduli] M(n) = %s" % M)

    # ---- CONTROL (iii) COLLAPSE: shuffle Q<->d association, run real invariant f5_open ----
    print("\n-- COLLAPSE NULL (shuffle association; must sit at floor: fires=False) --")
    for m in M:
        labels = [reps_i % m for reps_i in reps]
        feats_true = [f5[c] for c in reps]
        feats_shuf = fisher_yates(feats_true, "collapse|%d|m%d" % (p, m))
        res = run_channel(feats_shuf, labels, m, seed=p, key="collapse|%d|m%d" % (p, m))
        if res: print("   m=%2d: N=%d N_test=%d T=%d E=%d fires=%s  p=%d/%d"
                      % (m, res["N"], res["N_test"], res["T"], res["E"], res["fires"], res["pnum"], res["pden"]))

    # ---- CONTROL (i) MATCHED: run real statistic on f5(S_closed) ----
    print("\n-- MATCHED CONTROL S_closed (must sit at floor: fires=False) --")
    for m in M:
        labels = [c % m for c in reps]
        feats = [f5c.get(c) if f5c.get(c) is not None else -1 for c in reps]
        res = run_channel(feats, labels, m, seed=p, key="matched|%d|m%d" % (p, m))
        if res: print("   m=%2d: N=%d N_test=%d T=%d E=%d fires=%s  p=%d/%d"
                      % (m, res["N"], res["N_test"], res["T"], res["E"], res["fires"], res["pnum"], res["pden"]))

    # ---- CONTROL (ii) FIRING PLANT: must fire at high pi, not at pi=0 ----
    print("\n-- FIRING PLANT (power calibration; MUST fire at pi=1, MUST NOT at pi=0) --")
    for m in M:
        labels = [c % m for c in reps]
        line = "   m=%2d:" % m
        for (pnum, pden) in [(1, 1), (1, 2), (1, 4), (1, 8), (1, 16), (0, 1)]:
            feats = plant_feature(labels, m, pnum, pden, "plant|%d|m%d|pi%d_%d" % (p, m, pnum, pden))
            res = run_channel(feats, labels, m, seed=p, key="plant|%d|m%d|pi%d_%d" % (p, m, pnum, pden))
            tag = "-" if res is None else ("FIRE" if res["fires"] else "n(E=%d)" % res["E"])
            line += "  pi=%d/%d:%s" % (pnum, pden, tag)
        print(line)

    # ---- VERDICT-ELIGIBLE: real invariant f5_open -> d mod m (Outcome A needs E=0 surviving matched) ----
    print("\n-- f5 REAL-INVARIANT RECOVERY (verdict-eligible; A needs E=0 AND matched null) --")
    for m in M:
        labels = [c % m for c in reps]
        feats = [f5[c] for c in reps]
        res = run_channel(feats, labels, m, seed=p, key="real|%d|m%d" % (p, m))
        if res: print("   m=%2d: N=%d N_test=%d T=%d E=%d fires=%s  p=%d/%d"
                      % (m, res["N"], res["N_test"], res["T"], res["E"], res["fires"], res["pnum"], res["pden"]))

    # ---- f6 (frozen menu): marginal readout of sqrt(y); collapse applies, S_closed does NOT ----
    f6 = {r["d"]: r.get("f6_open") for r in recs}
    if all(f6.get(c) is not None for c in reps):
        print("\n-- f6 COLLAPSE NULL (shuffle; must be at floor) --")
        for m in M:
            labels = [c % m for c in reps]
            feats = fisher_yates([f6[c] for c in reps], "f6col|%d|m%d" % (p, m))
            res = run_channel(feats, labels, m, seed=p, key="f6col|%d|m%d" % (p, m))
            if res: print("   m=%2d: T=%d E=%d fires=%s  p=%d/%d" % (m, res["T"], res["E"], res["fires"], res["pnum"], res["pden"]))
        print("-- f6 REAL RECOVERY (MARGINAL: a fire is a sqrt(y)->d marginal, not an A_new-structural result) --")
        for m in M:
            labels = [c % m for c in reps]
            feats = [f6[c] for c in reps]
            res = run_channel(feats, labels, m, seed=p, key="f6real|%d|m%d" % (p, m))
            if res: print("   m=%2d: N_test=%d T=%d E=%d fires=%s  p=%d/%d"
                          % (m, res["N_test"], res["T"], res["E"], res["fires"], res["pnum"], res["pden"]))

    # ---- multi-prime torsion channels f_ell (ell>3) per PREREG_anew_multiprime_torsion_v1 ----
    ells = data.get("small_ells", [])
    for ell in ells:
        fo = {r["d"]: (r.get("fell_open") or {}).get(str(ell)) for r in recs}
        if not all(fo.get(c) is not None for c in reps):
            continue
        print("\n-- f_%d TORSION CHANNEL (matched = premise-only; verdict rests on collapse + replication + OOS) --" % ell)
        for m in M:
            labels = [c % m for c in reps]
            fsh = fisher_yates([fo[c] for c in reps], "fell%dcol|%d|m%d" % (ell, p, m))
            rc = run_channel(fsh, labels, m, seed=p, key="fell%dcol|%d|m%d" % (ell, p, m))
            rr = run_channel([fo[c] for c in reps], labels, m, seed=p, key="fell%dreal|%d|m%d" % (ell, p, m))
            if rc and rr:
                print("   m=%2d: collapse E=%d(%s) | REAL T=%d E=%d fires=%s  p=%d/%d"
                      % (m, rc["E"], "floor" if not rc["fires"] else "FIRE!",
                         rr["T"], rr["E"], rr["fires"], rr["pnum"], rr["pden"]))


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "val_p43_data.json")
