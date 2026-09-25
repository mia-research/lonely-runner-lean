"""Localise the v1/v2 difference: run v1's search (cold LPs) from each of v2's 126 task states (the states after
the first move, box [1,9]) and compare per-task counts with v2's checkpoint file.  Exact; parallel."""
import json
from multiprocessing import Pool
import climb_cells_v1 as v1
import climb_cells_v2 as v2

def run_v1(args):
    tid, rows, N, p, lab, word = args
    S = v1.Search(9, 1)
    S.step(rows, N, p, lab, word)
    return tid, S.cells, S.early, len(S.terms)

if __name__ == '__main__':
    M = v2.Search(9, 1)
    tasks = [c for r in M.roots() for c in M.children(r)]
    print(f"main: roots expanded, cells {M.cells}, early {M.early}, terms {len(M.terms)}; tasks {len(tasks)}", flush=True)
    ck = {}
    for line in open('climb_cells_v2_B9_S1.jsonl'):
        d = json.loads(line); ck[d['id']] = d
    args = [(v2.task_id(st), st[0], st[2], st[3], st[4], st[5]) for st in tasks]
    diff = 0; tot1 = [0, 0, 0]; tot2 = [0, 0, 0]
    with Pool() as pool:
        for tid, c1, e1, t1 in pool.imap_unordered(run_v1, args):
            d = ck[tid]; t2 = len(d['terms'])
            tot1 = [tot1[0] + c1, tot1[1] + e1, tot1[2] + t1]; tot2 = [tot2[0] + d['cells'], tot2[1] + d['early'], tot2[2] + t2]
            if (c1, e1, t1) != (d['cells'], d['early'], t2):
                diff += 1
                print(f"DIFF task {tid}: v1 cells {c1} early {e1} terms {t1} | v2 cells {d['cells']} early {d['early']} terms {t2}", flush=True)
    print(f"tasks differing: {diff}; totals over tasks v1 {tot1} v2 {tot2}")
