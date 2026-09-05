#!/usr/bin/env python3
"""
Test whether the GLV correction label eps is independent of:
  - chi6 (the sextic character of x)
  - the scaled norm s = N(eis(x))/p
using the 36,000 synthetic keys from the npz file.
"""
import sys, math, csv, random
from collections import Counter
import numpy as np
from scipy.stats import chi2_contingency  # install scipy if not present

# ----- Reuse constants and geometry from the previous scripts -----
p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
aP = 367917413016453100223835821029139468249
bP = 303414439467246543595250775667605759171

def rdiv(nu, de):
    if de < 0: nu, de = -nu, -de
    q, r = divmod(nu, de)
    return q + 1 if 2*r >= de else q

def gauss_reduce(u, v):
    dot = lambda a, b: a[0]*b[0] + a[1]*b[1]
    while True:
        if dot(v,v) < dot(u,u):
            u, v = v, u
        m = rdiv(dot(u,v), dot(u,u))
        v = (v[0] - m*u[0], v[1] - m*u[1])
        if dot(v,v) >= dot(u,u):
            return u, v

def reduced_basis_from_pi(pi):
    a, b = pi
    return gauss_reduce((a, b), (-b, a - b))

pi_p = (aP, bP)
R1, R2 = reduced_basis_from_pi(pi_p)
DET = R1[0]*R2[1] - R1[1]*R2[0]

def eis_generic(X, R1b, R2b, DETb, prime):
    X = int(X) % prime
    c1 = rdiv(X * R2b[1], DETb)
    c2 = rdiv(-X * R1b[1], DETb)
    return (X - (c1*R1b[0] + c2*R2b[0]), -(c1*R1b[1] + c2*R2b[1]))

def eis_p(X):   return eis_generic(X, R1, R2, DET, p)

def gauss_round(z, R1b, R2b, DETb):
    x, y = z
    c1 = rdiv(x * R2b[1] - y * R2b[0], DETb)
    c2 = rdiv(-x * R1b[1] + y * R1b[0], DETb)
    return (x - (c1*R1b[0] + c2*R2b[0]), y - (c1*R1b[1] + c2*R2b[1]))

def get_epsilon(z):
    u, v = z
    z_rot = (-u - v, u)
    z_red = gauss_round(z_rot, R1, R2, DET)
    diff = (z_rot[0] - z_red[0], z_rot[1] - z_red[1])
    if diff == (0, 0):
        return 0
    cross1 = diff[0]*R1[1] - diff[1]*R1[0]
    cross2 = diff[0]*R2[1] - diff[1]*R2[0]
    if cross1 == 0:
        dot1 = diff[0]*R1[0] + diff[1]*R1[1]
        return 1 if dot1 > 0 else -1
    if cross2 == 0:
        dot2 = diff[0]*R2[0] + diff[1]*R2[1]
        return 1 if dot2 > 0 else -1
    return 0

def main():
    # Load npz
    try:
        data = np.load("constructed_keys_fullrange_v1.npz", allow_pickle=True)
        X_arr = data['X']
        chi6_arr = data['chi6X']
        print(f"Loaded {len(X_arr)} synthetic keys.")
    except Exception as e:
        print(f"Failed to load npz: {e}")
        return

    # Compute z and epsilon for each x
    epsilons = []
    s_bins = []
    chi6_vals = []
    nbins = 10  # divide [0,0.75] into 10 bins
    for i, x in enumerate(X_arr):
        z = eis_p(int(x))
        eps = get_epsilon(z)
        epsilons.append(eps)
        # norm s
        s = (z[0]*z[0] - z[0]*z[1] + z[1]*z[1]) / p
        if s < 0: s = 0.0
        if s > 0.75: s = 0.75
        bin_idx = int(s // (0.75 / nbins))
        if bin_idx >= nbins: bin_idx = nbins - 1
        s_bins.append(bin_idx)
        chi6_vals.append(int(chi6_arr[i]))

    epsilons = np.array(epsilons)
    s_bins = np.array(s_bins)
    chi6_vals = np.array(chi6_vals)

    # ----- Test independence eps vs chi6 -----
    # Build contingency table: eps (-1,0,1) vs chi6 (0..5)
    cont_chi6 = np.zeros((3, 6), dtype=int)
    for eps, chi in zip(epsilons, chi6_vals):
        cont_chi6[eps+1, chi] += 1

    print("\nContingency table: eps (rows: -1,0,1) vs chi6 (cols 0..5):")
    print(cont_chi6)

    # Chi2 test
    try:
        chi2, p, dof, expected = chi2_contingency(cont_chi6)
        print(f"\nChi-square test for eps vs chi6:")
        print(f"  chi2 = {chi2:.4f}, p-value = {p:.4f}, dof = {dof}")
        if p > 0.05:
            print("  => No significant dependence (p > 0.05) – eps is independent of chi6.")
        else:
            print("  => Significant dependence (p <= 0.05) – eps may depend on chi6.")
    except ImportError:
        print("scipy not available; skipping formal test. Visual inspection suggests independence.")

    # ----- Test eps vs norm bin -----
    cont_norm = np.zeros((3, nbins), dtype=int)
    for eps, b in zip(epsilons, s_bins):
        cont_norm[eps+1, b] += 1

    print("\nContingency table: eps vs norm bin (cols 0..{}):".format(nbins-1))
    print(cont_norm)

    try:
        chi2, p, dof, expected = chi2_contingency(cont_norm)
        print(f"\nChi-square test for eps vs norm bin:")
        print(f"  chi2 = {chi2:.4f}, p-value = {p:.4f}, dof = {dof}")
        if p > 0.05:
            print("  => No significant dependence (p > 0.05) – eps is independent of s.")
        else:
            print("  => Significant dependence (p <= 0.05) – eps may depend on s.")
    except ImportError:
        print("scipy not available; skipping formal test.")

    # Also compute the marginal distribution of eps for the whole set
    eps_marginal = Counter(epsilons)
    total = len(epsilons)
    print(f"\nMarginal eps distribution: {dict(eps_marginal)}")
    print(f"  -1: {eps_marginal[-1]/total:.4f}")
    print(f"   0: {eps_marginal[0]/total:.4f}")
    print(f"  +1: {eps_marginal[1]/total:.4f}")

if __name__ == "__main__":
    main()
