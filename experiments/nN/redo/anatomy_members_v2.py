# The cascade as a chain of zones.  R = 8*d_min*t, rho_x = x/d_min.  Reading x blocks R in the zone
# Z(x,j) = ((8j-1)/rho_x, (8j+1)/rho_x), j >= 0 (open).  The cascade from R = 1 jumps to the right end of the zone(s)
# containing it; the landing is the first R >= 1 outside every zone.  Print the chain it actually uses and the overlaps.
import sys
sys.argv = [sys.argv[0]]
exec(open('anatomy_members_v1.py').read().split('if __name__')[0])
def chain(S, name):
    S = sorted(S); m = S[0]; rho = [F(x, m) for x in S]
    steps, t = run(S); Rend = 8 * m * t
    print("=" * 96); print(name, " rho:", [round(float(r), 3) for r in rho], " R* = %.4f" % float(Rend))
    zones = []
    for i, r in enumerate(rho):
        j = 0
        while (8 * j - 1) / r < Rend:
            lo, hi = (8 * j - 1) / r, (8 * j + 1) / r
            if hi > 1: zones.append((lo, hi, i + 1, j))
            j += 1
    zones.sort()
    # the zones the cascade used: follow R from 1
    R = F(1); used = []
    while True:
        cont = [z for z in zones if z[0] < R < z[1]]
        if not cont: break
        z = max(cont, key=lambda z: z[1]); used.append((R, z)); R = z[1]
    print(" zones containing R during the run, in order (rank, lap) [lo, hi]:   overlap with the previous end")
    prev = None
    for R0, (lo, hi, rk, j) in used:
        print("   rank %d lap %d  [%.4f, %.4f]   entered at R=%.4f   overlap %.4f" % (rk, j, float(lo), float(hi), float(R0), float(R0 - lo) if prev is None else float(prev - lo)))
        prev = hi
    nxt = [z for z in zones if z[0] >= R]
    print("   free at R* = %.4f ; the next zone starts at %s" % (float(R), "%.4f (rank %d lap %d)" % (float(nxt[0][0]), nxt[0][2], nxt[0][3]) if nxt else "none below"))
    # zones that start inside [1,R*] but were not on the path (covered by the chain)
if __name__ == "__main__":
    for i in (0, 1, 7, 3, 5): chain(B[i], "B1 #%d" % i)
    for i in (0, 1, 2): chain(C[i], "C1 #%d" % i)
