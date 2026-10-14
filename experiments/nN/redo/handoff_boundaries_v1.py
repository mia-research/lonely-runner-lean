"""Exact one-parameter cascade cells. Discovery experiment, not an LRC proof.

Speeds are v_i(z)=a_i+b_i*z. At an opening t=A/(8*v_s), every
grid/entrance/exit wall is A*v_i-q*v_s=0. Setter ties have the same
linear form. Signs of these forms certify the complete finite trace
throughout each returned OPEN cell. Boundary points are traced separately.
All decisions use Fraction. A step/cell cap is reported as incomplete.
"""
from fractions import Fraction as F
from collections import Counter
import argparse
import json
import unittest

H = F(1, 8)


def frac(x):
    return str(x) if isinstance(x, F) else x


def distance(x):
    r = x % 1
    return min(r, 1-r)


def trace(a, b, z, lo, hi, cap=2000):
    v = [x+y*z for x, y in zip(a, b)]
    assert all(x > 0 for x in v) and len(set(v)) == len(v)
    left, right = lo, hi
    walls = {}
    on_wall = False

    def sign(c, d, why):
        nonlocal left, right, on_wall
        # Record an exact sign constraint c+d*z. Identical equalities
        # (including a setter's own leaving edge) impose no wall.
        if not d:
            return
        root = -c/d
        if lo <= root <= hi:
            walls.setdefault(root, []).append(why)
            if root < z:
                left = max(left, root)
            elif z < root:
                right = min(right, root)
            else:
                on_wall = True

    for i in range(len(v)):
        sign(a[i], b[i], {"kind": "positive", "runner": i})
        for j in range(i):
            sign(a[i]-a[j], b[i]-b[j], {"kind": "speed_order", "pair": [i,j]})
    s = min(range(len(v)), key=v.__getitem__)
    A = 1
    rows = []
    for step in range(cap+1):
        t = F(A, 8)/v[s]
        readings = [8*x*t for x in v]
        active = []
        laps = {}
        for i, y in enumerate(readings):
            q = y.numerator // y.denominator
            # The integer grid floor records residue and deviation. These
            # extra walls refine, but never enlarge, the decision cell.
            for edge in (q, q+1):
                sign(A*a[i]-edge*a[s], A*b[i]-edge*b[s],
                     {"kind": "grid", "step": step, "setter": s,
                      "runner": i, "A": A, "edge": edge})
            if distance(v[i]*t) < H:
                active.append(i)
                laps[i] = (v[i]*t + F(1, 2)).__floor__()
        row = {"time": t, "source": s, "A": A,
               "grid": [{"floor": y.__floor__(), "residue": y.__floor__()%8,
                         "deviation": y-y.__floor__()} for y in readings],
               "blockers": active, "laps": laps}
        rows.append(row)
        if not active:
            clear_until = min(F(8*(v[i]*t).__floor__()+7,8)/v[i]
                              for i in range(len(v)))
            assert clear_until >= t
            return {"status": "clear", "steps": step, "rows": rows,
                    "left": left, "right": right, "on_wall": on_wall,
                    "walls": walls, "nearest_time": min(v)*t,
                    "clear_until": clear_until, "clear_width": clear_until-t}
        if step == cap:
            return {"status": "step_cap", "steps": step, "rows": rows,
                    "left": left, "right": right, "on_wall": on_wall,
                    "walls": walls}
        exits = {i: F(8*laps[i]+1, 8)/v[i] for i in active}
        winner = max(active, key=lambda i: (exits[i], -i))
        B = 8*laps[winner]+1
        for i in active:
            C = 8*laps[i]+1
            sign(B*a[i]-C*a[winner], B*b[i]-C*b[winner],
                 {"kind": "exit_tie", "step": step, "pair": [winner, i],
                  "numerators": [B, C]})
        row.update({"winner": winner, "exit_lap": laps[winner],
                    "capture_depth": B-readings[winner]})
        assert exits[winner] > t
        s, A = winner, B
    raise AssertionError("unreachable")


def signature(result):
    return [(r["source"], r["A"], tuple(r["blockers"]), r.get("winner"),
             tuple(g["floor"] for g in r["grid"])) for r in result["rows"]]


def partition(a, b, lo, hi, max_cells=600):
    todo = [(lo, hi)]
    cells, incomplete = [], []
    while todo and len(cells) < max_cells:
        l, r = todo.pop()
        result = None
        # Avoid nonidentical equalities at the sample. Exact boundary points
        # are examined later, never assigned the adjacent open-cell trace.
        for den in range(2, 102):
            z = l+(r-l)/den
            v = [x+y*z for x,y in zip(a,b)]
            if min(v) <= 0 or len(set(v)) != len(v):
                continue
            trial = trace(a,b,z,l,r)
            if not trial["on_wall"]:
                result = trial
                break
        if result is None or result["status"] != "clear":
            incomplete.append([str(l), str(r), "sample_or_step_cap"])
            continue
        L, R = result["left"], result["right"]
        # Independent interior replays check the extracted certificate.
        for p in (F(1,3), F(2,3)):
            check = trace(a,b,L+(R-L)*p,L,R)
            assert signature(check) == signature(result)
        cells.append({"left": L, "right": R, "sample": z, "trace": result})
        if l < L:
            todo.append((l,L))
        if R < r:
            todo.append((R,r))
    incomplete.extend([[str(l),str(r),"cell_cap"] for l,r in todo])
    cells.sort(key=lambda c:c["left"])
    if not incomplete:
        assert cells[0]["left"] == lo and cells[-1]["right"] == hi
        assert all(x["right"]==y["left"] for x,y in zip(cells,cells[1:]))
    boundaries = []
    for z in sorted({lo,hi} | {c[k] for c in cells for k in ("left","right")}):
        v = [x+y*z for x,y in zip(a,b)]
        if min(v) <= 0 or len(set(v)) != len(v):
            boundaries.append({"parameter": z, "status": "invalid_speeds"})
            continue
        tr = trace(a,b,z,lo,hi)
        adjacent = [c for c in cells if c["left"] == z or c["right"] == z]
        causes = []
        for c in adjacent:
            causes.extend(c["trace"]["walls"].get(z, []))
        boundaries.append({"parameter": z, "status": tr["status"],
                           "steps": tr["steps"], "trace": tr, "causes": causes,
                           "adjacent_steps": [c["trace"]["steps"] for c in adjacent]})
    return cells, boundaries, incomplete


def recurrence_records(v, tr):
    seen = {}
    out = []
    for step,r in enumerate(tr["rows"]):
        if "winner" not in r:
            continue
        s,w = r["source"],r["winner"]
        K,L = (r["A"]-1)//8,r["exit_lap"]
        key = s,w
        if key in seen:
            p,old = seen[key]
            dK = K-(old["A"]-1)//8
            dL = L-old["exit_lap"]
            drift = r["capture_depth"]-old["capture_depth"]
            assert drift == 8*(dL-v[w]/v[s]*dK)
            assert dK > 0 and dL > 0
            out.append({"pair": [s,w], "steps": [p,step], "lap_advance": [dK,dL],
                        "depth_before": old["capture_depth"],
                        "depth_after": r["capture_depth"], "depth_drift": drift})
        seen[key] = step,r
    return out


def compact_trace(tr):
    return {k:v for k,v in tr.items() if k != "walls"}


def run(path, custom=None, radius=F(1,50)):
    seeds = {
        "late_a": list(map(F,["1","2.3509","3.2412","4.1886","5.2223","5.7871","7.4378"])),
        "late_b": list(map(F,["1","2.5302","3.2218","4.1563","4.531","5.6544","7.0302"])),
        "manuscript_28": [F(x,49) for x in [49,205,234,256,286,323,366]],
        "doubled_ap": list(map(F,[1,2,3,4,5,6,8])),
        "wide_100": list(map(F,[1,8,16,25,33,41,100])),
    }
    output = {"method": __doc__, "paths": []}
    counts = Counter()
    examples = {}
    jobs=[]
    for name,a in seeds.items():
        for coordinate in range(1,7):
            jobs.append((name,a,[F(int(i==coordinate)) for i in range(7)],coordinate))
        jobs.append((name,a,list(map(F,[0,1,-1,1,-1,1,-1])),"coupled"))
    if custom:
        jobs=[("custom",custom[0],custom[1],"custom")]
    for name,a,b,coordinate in jobs:
            cells, boundaries, incomplete = partition(a,b,-radius,radius)
            entry = {"seed": name, "a": a, "b": b, "range": [-radius,radius],
                     "incomplete": incomplete, "cells": [], "boundaries": []}
            for cell in cells:
                tr=cell["trace"]
                v=[x+y*cell["sample"] for x,y in zip(a,b)]
                rec=recurrence_records(v,tr)
                counts["open_cells"] += 1
                counts["returning_pair_events"] += len(rec)
                counts["max_moves"] = max(counts["max_moves"],tr["steps"])
                for r in tr["rows"]:
                    counts["max_simultaneous_blockers"] = max(counts["max_simultaneous_blockers"],len(r["blockers"]))
                for r in rec:
                    direction = "increases" if r["depth_drift"]>0 else "decreases" if r["depth_drift"]<0 else "unchanged"
                    counts["return_depth_"+direction] += 1
                    examples.setdefault(direction,{"seed":name,"coordinate":coordinate,
                        "parameter":cell["sample"],"speeds":v,"return":r})
                entry["cells"].append({**{k:v for k,v in cell.items() if k!="trace"},
                    "trace":compact_trace(tr),"returns":rec})
            for bd in boundaries:
                counts["boundary_points"] += 1
                if bd["status"] == "clear":
                    counts["clear_boundary_points"] += 1
                    if len(bd["adjacent_steps"])==2 and bd["steps"] < min(bd["adjacent_steps"]):
                        counts["boundary_shorter_than_both_sides"] += 1
                    if bd["trace"]["clear_width"] == 0:
                        counts["zero_width_boundary_isolation"] += 1
                entry["boundaries"].append({**{k:v for k,v in bd.items() if k!="trace"},
                    **({"trace":compact_trace(bd["trace"])} if "trace" in bd else {})})
            output["paths"].append(entry)
            counts["incomplete_intervals"] += len(incomplete)
            print(name,coordinate,"cells",len(cells),"boundaries",len(boundaries),
                  "moves",min(c["trace"]["steps"] for c in cells),
                  max(c["trace"]["steps"] for c in cells),"incomplete",len(incomplete),flush=True)
    output["summary"] = dict(counts)
    output["recurrence_examples"] = examples
    changes=[]
    for p in output["paths"]:
        for bd in p["boundaries"]:
            adj=bd.get("adjacent_steps",[])
            if len(adj)==2 and len(set(adj+[bd["steps"]]))>1:
                changes.append({"seed":p["seed"],"b":p["b"],
                    "parameter":bd["parameter"],"boundary_steps":bd["steps"],
                    "adjacent_steps":adj,"clear_width":bd["trace"]["clear_width"],
                    "causes":bd["causes"]})
    changes.sort(key=lambda x:max(x["adjacent_steps"])-min(x["adjacent_steps"]+[x["boundary_steps"]]),reverse=True)
    output["largest_boundary_changes"] = changes[:8]
    with open(path,"w") as f:
        json.dump(output,f,default=frac,indent=2)
    print(json.dumps({"summary":dict(counts),"examples":examples,
                      "largest_boundary_changes":changes[:3]},default=frac,indent=2))


class Tests(unittest.TestCase):
    def test_clear_ap(self):
        tr=trace(list(map(F,range(1,8))),[F(0)]*7,F(0),F(-1),F(1))
        self.assertEqual(tr["steps"],0)

    def test_threshold_is_clear(self):
        self.assertEqual(distance(F(1,8)),H)
        self.assertEqual(distance(F(7,8)),H)

    def test_manuscript(self):
        a=[F(x,49) for x in [49,205,234,256,286,323,366]]
        tr=trace(a,[F(0)]*7,F(0),F(-1),F(1))
        self.assertEqual(tr["steps"],28)
        recurrence_records(a,tr)

    def test_simple_boundary(self):
        a=[F(1),F(8)]
        cells,bounds,inc=partition(a,[F(0),F(1)],F(-2),F(2))
        self.assertFalse(inc)
        self.assertTrue(all(c["trace"]["status"]=="clear" for c in cells))
        self.assertTrue(all(b["status"]=="clear" for b in bounds))

    def test_scale_invariance(self):
        a=[F(x,49) for x in [49,205,234,256,286,323,366]]
        cells,_,inc=partition(a,a,F(-1,10),F(1,10))
        self.assertFalse(inc)
        self.assertEqual(len(cells),1)
        self.assertEqual(cells[0]["trace"]["steps"],28)

    def test_exact_disappearing_handoff(self):
        a=list(map(F,["1","2.3509","3.2412","4.1886","5.2223","5.7871","7.4378"]))
        b=[F(0)]*6+[F(1)]
        wall=F(193,70000)
        tr=trace(a,b,wall,F(-1,50),F(1,50))
        self.assertEqual(tr["steps"],1)
        self.assertEqual(tr["clear_width"],0)
        self.assertEqual(trace(a,b,wall-F(1,10**7),F(-1,50),F(1,50))["steps"],27)
        self.assertEqual(trace(a,b,wall+F(1,10**7),F(-1,50),F(1,50))["steps"],1)

    def test_independent_opening_search(self):
        # Check first isolation independently by enumerating every runner's
        # opening up to the claimed endpoint, rather than using cascade moves.
        import random
        rng=random.Random(829)
        sets=[[F(1)]+list(map(F,sorted(rng.sample(range(2,41),6)))) for _ in range(30)]
        sets.append([F(x,49) for x in [49,205,234,256,286,323,366]])
        for a in sets:
            tr=trace(a,[F(0)]*7,F(0),F(-1),F(1))
            end=tr["rows"][-1]["time"]
            start=H/min(a)
            candidates={start}
            for d in a:
                for k in range((d*end).__floor__()+1):
                    t=(F(k)+H)/d
                    if start <= t <= end:
                        candidates.add(t)
            first=min(t for t in candidates if all(distance(d*t)>=H for d in a))
            self.assertEqual(first,end)


if __name__ == "__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--test",action="store_true")
    p.add_argument("--output",default="handoff_boundaries_v1.json")
    p.add_argument("--speeds",help="Seven positive distinct rationals, comma separated")
    p.add_argument("--direction",help="Seven rational perturbation coefficients, comma separated")
    p.add_argument("--radius",default="1/50")
    args=p.parse_args()
    if F(args.radius)<=0:
        p.error("--radius must be positive")
    if args.test:
        unittest.main(argv=[__file__])
    else:
        custom=None
        if args.speeds or args.direction:
            if not (args.speeds and args.direction):
                p.error("--speeds and --direction must be supplied together")
            custom=(list(map(F,args.speeds.split(','))),list(map(F,args.direction.split(','))))
            if len(custom[0])!=7 or len(custom[1])!=7:
                p.error("exactly seven speeds and seven direction coefficients required")
        run(args.output,custom,F(args.radius))
