import csv

p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
a_curve = 0
b_curve = 7

def modinv(a, m):
    g, x, _ = extended_gcd(a % m, m)
    return x % m

def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

def point_add(P, Q):
    if P is None: return Q
    if Q is None: return P
    x1, y1 = P
    x2, y2 = Q
    if x1 == x2:
        if (y1 + y2) % p == 0:
            return None
        lam = (3 * x1 * x1 + a_curve) * modinv(2 * y1, p) % p
    else:
        lam = (y2 - y1) * modinv(x2 - x1, p) % p
    x3 = (lam * lam - x1 - x2) % p
    y3 = (lam * (x1 - x3) - y1) % p
    return (x3, y3)

def point_neg(P):
    if P is None: return None
    return (P[0], (-P[1]) % p)

def point_sub(P, Q):
    return point_add(P, point_neg(Q))

def legendre(a, pp):
    ls = pow(a % pp, (pp - 1) // 2, pp)
    if ls == pp - 1:
        return -1
    return ls  # 0 or 1

def cubic_char(x, pp):
    if x % pp == 0:
        return 0
    val = pow(x, (pp - 1) // 3, pp)
    return val

# Load the 82 solved keys
keys = []
with open("/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/solved_puzzles_xy.csv") as f:
    reader = csv.DictReader(f)
    for row in reader:
        puzzle = int(row['puzzle_num'])
        d = int(row['private_key'], 16)
        X = int(row['X'], 16)
        Y = int(row['Y'], 16)
        # verify on curve
        assert (Y * Y - X * X * X - 7) % p == 0, f"puzzle {puzzle} not on curve!"
        keys.append((puzzle, d, X, Y))

print(f"Loaded {len(keys)} keys, all verified on curve")

# Compute S_diff = sum_{j<k} chi_2(y_{j-k}) where j<k in puzzle order
s_diff_all = 0
cubic_counts = [0, 0, 0]  # class 0 (residue), class 1 (beta), class 2 (beta^2)
beta = pow(2, (p-1)//3, p)  # a primitive cube root of unity mod p

pair_count = 0
for i in range(len(keys)):
    for j in range(i+1, len(keys)):
        Pi = (keys[i][2], keys[i][3])
        Pj = (keys[j][2], keys[j][3])
        # P_j - P_i (j > i in puzzle order)
        D = point_sub(Pj, Pi)
        if D is None:
            print(f"  WARNING: difference is O for puzzles {keys[i][0]}, {keys[j][0]}")
            continue
        xd, yd = D

        # S_diff: Legendre of y-coordinate
        leg = legendre(yd, p)
        s_diff_all += leg

        # E3: cubic residue class of x-coordinate
        cc = cubic_char(xd, p)
        if cc == 1:
            cubic_counts[0] += 1
        elif cc == beta:
            cubic_counts[1] += 1
        elif cc == (beta * beta) % p:
            cubic_counts[2] += 1
        else:
            print(f"  WARNING: unexpected cubic char {cc} for puzzles {keys[i][0]}, {keys[j][0]}")

        pair_count += 1

print(f"\nTotal pairs: {pair_count} (expected {len(keys)*(len(keys)-1)//2})")
print(f"\nS_diff (all 82) = {s_diff_all}")
print(f"  Document claims: -63")

print(f"\nE3 cubic energy:")
print(f"  Class 0 (cubic residues): {cubic_counts[0]}  (deviation {cubic_counts[0] - pair_count/3:.2f})")
print(f"  Class 1 (beta):           {cubic_counts[1]}  (deviation {cubic_counts[1] - pair_count/3:.2f})")
print(f"  Class 2 (beta^2):         {cubic_counts[2]}  (deviation {cubic_counts[2] - pair_count/3:.2f})")
print(f"  Document claims: 1093 / 1110 / 1118")

# Now do subsets
for cutoff_puzzle in [50, 60, 65, 70]:
    subset = [(pz, d, x, y) for pz, d, x, y in keys if pz <= cutoff_puzzle]
    sd = 0
    cnt = 0
    for i in range(len(subset)):
        for j in range(i+1, len(subset)):
            Pi = (subset[i][2], subset[i][3])
            Pj = (subset[j][2], subset[j][3])
            D = point_sub(Pj, Pi)
            if D is None:
                continue
            xd, yd = D
            leg = legendre(yd, p)
            sd += leg
            cnt += 1
    print(f"\nS_diff (puzzles 1..{cutoff_puzzle}): {sd}  ({cnt} pairs)")

# Semaev S3 validation: pick 3 random collinear points
import random
random.seed(42)
Gx = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
Gy = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
G = (Gx, Gy)

def scalar_mult(k, P):
    R = None
    Q = P
    while k > 0:
        if k & 1:
            R = point_add(R, Q)
        Q = point_add(Q, Q)
        k >>= 1
    return R

def semaev_s3(x1, x2, x3):
    # S3(x1,x2,x3) = (x1-x2)^2 * x3^2 - 2*((x1+x2)*(x1*x2) + 14)*x3 + (x1^2*x2^2 - 28*(x1+x2))
    t1 = ((x1 - x2) * (x1 - x2)) % p
    t1 = (t1 * x3 * x3) % p
    t2 = (2 * ((x1 + x2) * (x1 * x2 % p) % p + 14)) % p
    t2 = (t2 * x3) % p
    t3 = (x1 * x1 % p * (x2 * x2 % p) % p - 28 * (x1 + x2)) % p
    return (t1 - t2 + t3) % p

print("\n\nSemaev S3 validation:")
for trial in range(3):
    d1 = random.randrange(1, n)
    d2 = random.randrange(1, n)
    d3 = (n - (d1 + d2) % n) % n
    P1 = scalar_mult(d1, G)
    P2 = scalar_mult(d2, G)
    P3 = scalar_mult(d3, G)
    # Check P1+P2+P3 = O
    S = point_add(point_add(P1, P2), P3)
    s3_val = semaev_s3(P1[0], P2[0], P3[0])
    print(f"  Trial {trial+1}: S3 = {s3_val}, P1+P2+P3 = {'O' if S is None else 'NOT O'}")
