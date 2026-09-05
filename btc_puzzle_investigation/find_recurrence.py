import sys
from _sigma_chi2_scan_v1 import build

p = 2**256 - 2**32 - 977
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G = (Gx, Gy)

def inv_mod(a, m): return pow(a, -1, m)

def ecc_add(P, Q):
    if P is None: return Q
    if Q is None: return P
    x1, y1 = P; x2, y2 = Q
    if x1 == x2 and (y1 + y2) % p == 0: return None
    if P == Q:
        m = (3 * x1 * x1) * inv_mod(2 * y1, p) % p
    else:
        m = (y2 - y1) * inv_mod(x2 - x1, p) % p
    x3 = (m * m - x1 - x2) % p
    y3 = (m * (x1 - x3) - y1) % p
    return (x3, y3)

print("Building structure...")
eis, eps, beta, R1, R2, DET = build(p)

print("Generating 50 curve points and extracting 2D lattice coordinates (a, b)...")
P = G
points = []
for k in range(1, 51):
    if k > 1:
        P = ecc_add(P, G)
    if P is None: break
    a, b = eis(P[0])
    points.append((a, b))

# Function to test for linear recurrence of order d
def has_recurrence(seq, d):
    # seq is a list of tuples (a, b)
    # We check if seq[i] = c1*seq[i-1] + ... + cd*seq[i-d]
    # We set up a linear system using the first 2d elements
    # and verify it on the rest.
    if len(seq) < 2 * d + 1:
        return False, None
    
    # We test 'a' and 'b' separately
    for coord_idx in range(2):
        s = [x[coord_idx] for x in seq]
        
        # Build matrix A and vector B for the first d equations
        # s[d] = c1*s[d-1] + ... + cd*s[0]
        # s[d+1] = c1*s[d] + ... + cd*s[1]
        # ...
        A = []
        B = []
        for i in range(d, 2*d):
            row = s[i-d:i]
            A.append(row)
            B.append(s[i])
            
        # Solve for coefficients c1..cd using exact fractions
        # (Using numpy would introduce floats, which are forbidden)
        from fractions import Fraction as Fr
        # Gaussian elimination
        mat = [[Fr(x) for x in A[i]] + [Fr(B[i])] for i in range(d)]
        for col in range(d):
            # find pivot
            pivot = -1
            for r in range(col, d):
                if mat[r][col] != 0:
                    pivot = r
                    break
            if pivot == -1: break
            mat[col], mat[pivot] = mat[pivot], mat[col]
            # normalize
            piv_val = mat[col][col]
            mat[col] = [x / piv_val for x in mat[col]]
            # eliminate
            for r in range(d):
                if r != col and mat[r][col] != 0:
                    factor = mat[r][col]
                    mat[r] = [mat[r][i] - factor * mat[col][i] for i in range(d+1)]
        
        coeffs = [mat[i][d] for i in range(d)]
        
        # Verify on the rest of the sequence
        for i in range(2*d, len(s)):
            pred = sum(coeffs[j] * s[i-1-j] for j in range(d))
            if pred != s[i]:
                return False, None
    return True, coeffs

print("\nTesting for low-order linear recurrences in the lattice coordinates...")
for d in range(1, 6):
    found, coeffs = has_recurrence(points, d)
    if found:
        print(f"FOUND RECURRENCE OF ORDER {d}!")
        print(f"  Coefficients: {coeffs}")
        break
else:
    print("No linear recurrence of order 1 to 5 found.")

print("\n--- Done ---")
