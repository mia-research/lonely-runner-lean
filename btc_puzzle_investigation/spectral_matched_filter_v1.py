#!/usr/bin/env python3
"""
spectral_matched_filter_v1.py

The literal "interference" instrument: a SET-LEVEL coherent character sum. Per-key
readouts are null; a shadow could still hide as a COHERENT phase that only sums up
across the whole key set. For each modulus q we compute the matched filter

    S(a) = sum_i  chi6(X_i) * zeta_q^{ a * (d_i mod q) }        a = 0..q-1

= the length-q DFT of the chi6(X) phases bucketed by d mod q. A peak at some a != 0
means the point sextic phase is COHERENT with a linear phase in d mod q -- an
ECDLP-relevant resonance no single-key marginal (or even MI) would surface if the
phase is spread. Decision is EXACT: max nonzero |S(a)| vs a permutation null
(shuffle chi6 against d). The DFT itself is a ranked diagnostic (noqa float).

Sets: generated 256-bit (known d, non-degenerate). PLANT: chi6:=f(d mod 6) -> the
q=6 filter must light. Exact integers in the signal path except the ranked DFT stat.
"""
import numpy as np
from angular_interference_scaling_v1 import chi6

p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

def load256(cap=12000):
    z = np.load("constructed_keys_fullrange_v1.npz", allow_pickle=True)
    mask = np.array([int(v) == 256 for v in z["N"]])
    idx = np.where(mask)[0][:cap]
    d = [int(z["d"][i]) for i in idx]
    X = [int(z["X"][i]) for i in idx]
    return d, X

def matched_filter_maxpeak(phase_exp, dmodq, q):
    """phase_exp: int array in 0..5 (chi6 exponent). dmodq: int array in 0..q-1.
    Returns max_{a!=0} |sum_i zeta6^{phase_i} zeta_q^{a dmodq_i}| (float diagnostic)."""
    z6 = np.exp(2j * np.pi * phase_exp / 6)          # noqa: float (ranked DFT stat)
    # bucket the complex phases by residue, then DFT over the q buckets
    buck = np.zeros(q, dtype=complex)                # noqa: float
    np.add.at(buck, dmodq, z6)                       # noqa: float
    spec = np.abs(np.fft.fft(buck))                  # noqa: float
    return float(spec[1:].max())                     # noqa: float (exclude DC)

def test_q(phase, d, q, rng, Bperm=300):
    dmodq = np.array([x % q for x in d], dtype=np.int64)
    obs = matched_filter_maxpeak(phase, dmodq, q)
    null = np.empty(Bperm)                           # noqa: float
    ph = phase.copy()
    for b in range(Bperm):
        rng.shuffle(ph)
        null[b] = matched_filter_maxpeak(ph, dmodq, q)
    pval = (np.sum(null >= obs) + 1) / (Bperm + 1)   # noqa: float (rank p, integer counts)
    return obs, float(null.mean()), pval             # noqa: float (report)

def main():
    d, X = load256()
    phase = np.array([chi6(x) if chi6(x) is not None else 0 for x in X], dtype=np.int64)
    rng = np.random.default_rng(2026)
    qs = [5, 6, 7, 8, 9, 11, 12, 13, 16, 25, 42, 63, 64, 91, 127]
    print(f"SET-LEVEL SPECTRAL MATCHED FILTER  (chi6(X) vs d mod q, {len(d)} keys)")
    print(f"{'q':>5} {'maxpeak':>10} {'null_mean':>10} {'ratio':>7} {'rank_p':>8}  verdict")
    hits = []
    for q in qs:
        obs, nm, pv = test_q(phase, d, q, rng)
        ratio = obs / (nm + 1e-9)                     # noqa: float (report)
        v = "RESONANCE" if pv < 0.01 else "flat"      # noqa: float (verdict)
        if pv < 0.01:  # noqa: float (verdict threshold)
            hits.append((q, pv))
        print(f"{q:>5} {obs:>10.1f} {nm:>10.1f} {ratio:>7.2f} {pv:>8.4f}  {v}")

    # PLANT: chi6 := (d mod 6) mapped to a phase -> q=6 filter must fire
    print("\n[PLANT] chi6 := d mod 6 (exact leak):")
    planted = np.array([x % 6 for x in d], dtype=np.int64)
    obs, nm, pv = test_q(planted, d, 6, rng)
    print(f"  q=6: maxpeak={obs:.1f} null_mean={nm:.1f} ratio={obs/(nm+1e-9):.1f} "  # noqa: float (report)
          f"rank_p={pv:.4f}  (must be RESONANCE)")

    print(f"\n=> real chi6 resonances (p<0.01): {hits if hits else 'NONE across all q'}")

if __name__ == "__main__":
    main()
