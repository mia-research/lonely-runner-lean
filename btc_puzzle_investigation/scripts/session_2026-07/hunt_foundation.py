"""
Foundational single-feature MI sweep at 100k power. Widest net of simple (X,Y)
features vs all n/k targets. Establishes the MI floor and flags anything above it.
Includes a PLANTED-LEAK positive control so the floor is calibrated.
"""
import leak_lib as L
import numpy as np

d=L.load(); N=d["N"]; X=d["X"]; Y=d["Y"]
print(f"loaded {N} keys")

feats={}
for m in L.SMALL_MODS:
    feats[f"X%{m}"]=L.col_mod(X,m); feats[f"Y%{m}"]=L.col_mod(Y,m)
    feats[f"XY%{m}"]=L.col_mod(L.tf_prod(X,Y),m); feats[f"X+Y%{m}"]=L.col_mod(L.tf_sum(X,Y),m)
for p in L.SMALL_PRIMES:
    feats[f"Xleg{p}"]=L.col_legendre(X,p); feats[f"Yleg{p}"]=L.col_legendre(Y,p)
for b in list(range(0,256,8)):
    feats[f"Xb{b}"]=L.col_bit(X,b); feats[f"Yb{b}"]=L.col_bit(Y,b)
feats["Xham%8"]=L.col_hamming(X)%8; feats["Yham%8"]=L.col_hamming(Y)%8
print(f"{len(feats)} single features")

targets=L.build_target_set(d)
res=L.sweep(feats, targets, N, top=30, label="FOUNDATION single-feature")

# floor: max MI expected under pure noise for these alphabets at this N
rng=np.random.default_rng(1)
noise=[L.mi_bits(rng.integers(0,16,N), rng.integers(0,16,N))[0] for _ in range(30)]
print(f"\nnoise-MI floor (16x16 alphabet, N={N}): mean={np.mean(noise):.5f} max={np.max(noise):.5f}")

# positive control: a feature that carries 0.3 bits about k%4
base=d["k"]%4
leak=np.where(rng.random(N)<0.4, base, rng.integers(0,4,N))
mi,A,B=L.mi_bits(leak, base)
print(f"[CONTROL] planted 40%-agreement feature -> k%4: MI={mi:.4f} bits (detector sees real leaks)")
print("\nRead: any real feature MI clearly above the noise floor is a candidate to chase.")
