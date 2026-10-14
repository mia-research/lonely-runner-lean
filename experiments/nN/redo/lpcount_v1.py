# Count the LP queries per node in the tree (how many feasibility answers would need an exact certificate).
import sys, time
sys.argv = [sys.argv[0], "1", "2", "1"]
src = open('path_tree_par2.py').read().split('if __name__ == "__main__":')[0]
exec(src)
CALLS = {"feasible": 0, "false": 0, "range": 0}
_f = feasible; _r = rho_range
def feasible(cons):
    CALLS["feasible"] += 1; ok, v = _f(cons)
    if not ok: CALLS["false"] += 1
    return ok, v
def rho_range(cons, y):
    CALLS["range"] += 1; return _r(cons, y)
specs = frontier(root(), levels=2)
spec = [s for s in specs if s[3] == [(7, 1), (4, 1)]][0]
t = time.time(); r = work(spec)
print("subtree", r[0], "nodes", r[1], "terminal", r[2], "%.0fs" % (time.time() - t))
print("feasibility queries: %d (infeasible answers %d), range LPs %d  -> per node: %.1f queries, %.1f infeasible, %.1f range LPs" % (
    CALLS["feasible"], CALLS["false"], CALLS["range"], CALLS["feasible"] / r[1], CALLS["false"] / r[1], CALLS["range"] / r[1]))
