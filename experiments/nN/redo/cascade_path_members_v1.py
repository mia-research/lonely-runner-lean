# The same map on the REAL EightResidual members (B1: 47, C1: 547): cascade moves, setter rank, how each new blocker got in, shift sizes.
import sys
sys.argv = [sys.argv[0]]
exec(open('anatomy_members_v1.py').read().split('\nif __name__ == "__main__":')[0])
exec(open('redo/cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
from collections import Counter
for name, mem in (("B1", B), ("C1", C)):
    nm = Counter(); setr = Counter(); carry = Counter(); ret = 0; lens = Counter(); firstp0 = Counter(); lastlap = Counter()
    for S in mem:
        S = sorted(S); rhos = [F(x, S[0]) for x in S]
        steps, Rend = path(rhos); lens[len(steps)] += 1
        for n, mv in enumerate(steps):
            key = min(n + 1, 3); nm[key] += 1; setr[(key, mv["setter"] + 1)] += 1
            for i, how, p0, sh in mv["new"]:
                if how == "returned": ret += 1
                else: carry[(key, "shift<1" if sh < 1 else ("shift 1-3" if sh < 3 else "shift>=3"))] += 1
            if n == 0:
                for i, how, p0, sh in mv["new"]: firstp0[round(float(p0), 1)] += 1
        lastlap[steps[-1]["lap"] if steps else 0] += 1
    print("=" * 100); print(name, len(mem), "members; cascade moves per member:", sorted(lens.items()))
    print(" moves by index (1,2,3+):", sorted(nm.items()))
    print(" setter reading rank (1 = smallest, 7 = fastest) by move index:", sorted(setr.items()))
    print(" new blockers: carried, by shift size:", sorted(carry.items()), "; returned:", ret)
    print(" first move, position (eighths) of the carried blocker before the move (rounded):", sorted(firstp0.items())[:15])
    print(" lap of the last setter:", sorted(lastlap.items()))
