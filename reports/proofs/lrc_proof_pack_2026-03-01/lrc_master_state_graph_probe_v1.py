#!/usr/bin/env python3
"""
Master state-graph probe scaffold for unified M1-M3 work.

Given (n, E_fix, M), this script constructs the discrete state graph over B_div:
- nodes: realized tau states
- edges: transitions between consecutive fibers b -> b+1
- labels: changed coordinates, U_fix/R_fix statistics
- residue diagnostics: miss components per r

This is a scaffold for theorem work (not a proof).
"""

from __future__ import annotations

import argparse
import csv
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from functools import reduce
from itertools import combinations
from math import gcd, lcm
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple


def ext_gcd(a: int, b: int) -> Tuple[int, int, int]:
    if a == 0:
        return b, 0, 1
    g, x, y = ext_gcd(b % a, a)
    return g, y - (b // a) * x, x


def modinv(a: int, n: int) -> int | None:
    g, x, _ = ext_gcd(a % n, n)
    if g != 1:
        return None
    return x % n


def bad_set(e: int, t: int, n: int) -> set[int]:
    g = gcd(e, n)
    n1 = n // g
    e1 = e // g
    inv = modinv(e1, n1)
    if inv is None:
        return set()

    out: set[int] = set()
    for rr in ((-t) % n, (-(t + 1)) % n):
        if rr % g != 0:
            continue
        a0 = ((rr // g) * inv) % n1
        for k in range(g):
            out.add((a0 + k * n1) % n)
    return out


def lcm_list(vals: Iterable[int]) -> int:
    return reduce(lcm, vals, 1)


def parse_list(s: str) -> List[int]:
    s = s.strip()
    if not s:
        return []
    return [int(x.strip()) for x in s.split(",") if x.strip()]


@dataclass
class Node:
    tau: Tuple[int, ...]
    first_b: int
    last_b: int
    count_b: int
    u_size: int
    r_size: int
    r_mask: str


def near_complete_from_dropped(n: int, dropped: Tuple[int, int]) -> List[int]:
    return [e for e in range(1, n) if e not in dropped]


def contiguous_components(points: Sequence[int]) -> List[Tuple[int, int]]:
    if not points:
        return []
    pts = sorted(points)
    out: List[Tuple[int, int]] = []
    a = b = pts[0]
    for x in pts[1:]:
        if x == b + 1:
            b = x
        else:
            out.append((a, b))
            a = b = x
    out.append((a, b))
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--M", type=int, default=1)
    ap.add_argument("--e-fix", type=str, default="", help="Comma list; optional if --dropped used")
    ap.add_argument("--dropped", type=str, default="", help="Two dropped values a,b for near-complete template")
    ap.add_argument("--out-dir", type=Path, default=Path("/tmp"))
    ap.add_argument("--tag", type=str, default="")
    args = ap.parse_args()

    n = args.n
    M = args.M

    E_fix: List[int]
    if args.e_fix:
        E_fix = parse_list(args.e_fix)
    elif args.dropped:
        d = parse_list(args.dropped)
        if len(d) != 2:
            raise ValueError("--dropped must contain exactly two integers")
        E_fix = near_complete_from_dropped(n, (d[0], d[1]))
    else:
        raise ValueError("Provide either --e-fix or --dropped")

    E_fix = sorted(E_fix)
    e_index = {e: i for i, e in enumerate(E_fix)}

    L0 = lcm_list(E_fix + [n])
    L = L0 * M

    b_lo = (L + n - 1) // n
    b_hi = ((n - 1) * L) // n

    if b_lo > b_hi:
        raise RuntimeError("Empty B_div; invalid configuration")

    tau_by_b: Dict[int, Tuple[int, ...]] = {}
    U_by_b: Dict[int, set[int]] = {}
    R_by_b: Dict[int, set[int]] = {}

    nodes_data: Dict[Tuple[int, ...], List[int]] = defaultdict(list)
    node_u: Dict[Tuple[int, ...], set[int]] = {}

    ZN = set(range(n))

    for b in range(b_lo, b_hi + 1):
        tau = tuple((e * b) // L for e in E_fix)
        tau_by_b[b] = tau

        U: set[int] = set()
        for e, t in zip(E_fix, tau):
            U |= bad_set(e, t, n)
        R = ZN - U

        U_by_b[b] = U
        R_by_b[b] = R

        nodes_data[tau].append(b)
        if tau not in node_u:
            node_u[tau] = set(U)

    nodes: List[Node] = []
    for tau, bs in nodes_data.items():
        first_b = min(bs)
        last_b = max(bs)
        U = node_u[tau]
        R = ZN - U
        r_mask = "".join("1" if r in R else "0" for r in range(n))
        nodes.append(
            Node(
                tau=tau,
                first_b=first_b,
                last_b=last_b,
                count_b=len(bs),
                u_size=len(U),
                r_size=len(R),
                r_mask=r_mask,
            )
        )

    edges = []
    multi_coord_count = 0
    one_coord_count = 0

    for b in range(b_lo, b_hi):
        t0 = tau_by_b[b]
        t1 = tau_by_b[b + 1]
        if t0 == t1:
            continue
        changed = [i for i, (a, c) in enumerate(zip(t0, t1)) if a != c]
        if len(changed) == 1:
            one_coord_count += 1
        else:
            multi_coord_count += 1

        changed_e = [E_fix[i] for i in changed]

        edges.append(
            {
                "b": b,
                "from_tau": "(" + ",".join(map(str, t0)) + ")",
                "to_tau": "(" + ",".join(map(str, t1)) + ")",
                "changed_coords": len(changed),
                "changed_e": ",".join(map(str, changed_e)),
                "u_size_from": len(U_by_b[b]),
                "u_size_to": len(U_by_b[b + 1]),
                "r_size_from": len(R_by_b[b]),
                "r_size_to": len(R_by_b[b + 1]),
            }
        )

    # residue-level miss diagnostics over B_div fibers
    residue_rows = []
    for r in range(n):
        miss_points = [b for b in range(b_lo, b_hi + 1) if r not in U_by_b[b]]
        comps = contiguous_components(miss_points)
        largest_len = max((b - a + 1) for a, b in comps) if comps else 0
        miss_count = len(miss_points)
        residue_rows.append(
            {
                "r": r,
                "miss_fiber_count": miss_count,
                "miss_component_count": len(comps),
                "largest_miss_component_fibers": largest_len,
                "has_miss": int(miss_count > 0),
            }
        )

    has_any_miss = any(row["has_miss"] == 1 for row in residue_rows)

    tag = args.tag.strip() if args.tag else f"n{n}_M{M}"
    out_dir = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    nodes_csv = out_dir / f"lrc_master_state_nodes_{tag}_v1.csv"
    edges_csv = out_dir / f"lrc_master_state_edges_{tag}_v1.csv"
    residue_csv = out_dir / f"lrc_master_state_residue_{tag}_v1.csv"
    summary_md = out_dir / f"lrc_master_state_summary_{tag}_v1.md"

    with nodes_csv.open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["tau", "first_b", "last_b", "count_b", "u_size", "r_size", "r_mask"])
        for nd in sorted(nodes, key=lambda x: x.first_b):
            w.writerow([
                "(" + ",".join(map(str, nd.tau)) + ")",
                nd.first_b,
                nd.last_b,
                nd.count_b,
                nd.u_size,
                nd.r_size,
                nd.r_mask,
            ])

    with edges_csv.open("w", newline="") as f:
        if edges:
            keys = list(edges[0].keys())
        else:
            keys = [
                "b",
                "from_tau",
                "to_tau",
                "changed_coords",
                "changed_e",
                "u_size_from",
                "u_size_to",
                "r_size_from",
                "r_size_to",
            ]
        w = csv.DictWriter(f, fieldnames=keys)
        w.writeheader()
        for row in edges:
            w.writerow(row)

    with residue_csv.open("w", newline="") as f:
        keys = list(residue_rows[0].keys()) if residue_rows else [
            "r", "miss_fiber_count", "miss_component_count", "largest_miss_component_fibers", "has_miss"
        ]
        w = csv.DictWriter(f, fieldnames=keys)
        w.writeheader()
        for row in residue_rows:
            w.writerow(row)

    bdiv_len = b_hi - b_lo + 1
    lines: List[str] = []
    lines.append(f"# Master State Graph Summary ({tag})")
    lines.append("")
    lines.append(f"- n: {n}")
    lines.append(f"- M: {M}")
    lines.append(f"- E_fix: {E_fix}")
    lines.append(f"- L0: {L0}")
    lines.append(f"- L: {L}")
    lines.append(f"- B_div: [{b_lo}, {b_hi}] (size {bdiv_len})")
    lines.append("")
    lines.append("## Graph stats")
    lines.append("")
    lines.append(f"- Nodes (realized tau): {len(nodes)}")
    lines.append(f"- Transition edges: {len(edges)}")
    lines.append(f"- One-coordinate edges: {one_coord_count}")
    lines.append(f"- Multi-coordinate edges: {multi_coord_count}")
    lines.append("")
    lines.append("## Miss diagnostics")
    lines.append("")
    lines.append(f"- Exists residue with miss fibers: {has_any_miss}")
    best = max(residue_rows, key=lambda x: x["miss_fiber_count"]) if residue_rows else None
    if best:
        lines.append(
            f"- Best residue r*: {best['r']} (miss_fiber_count={best['miss_fiber_count']}, "
            f"components={best['miss_component_count']}, largest_component={best['largest_miss_component_fibers']})"
        )
    lines.append("")
    lines.append("## Artifacts")
    lines.append("")
    lines.append(f"- Nodes CSV: {nodes_csv}")
    lines.append(f"- Edges CSV: {edges_csv}")
    lines.append(f"- Residue CSV: {residue_csv}")

    summary_md.write_text("\n".join(lines) + "\n")

    print(f"wrote: {nodes_csv}")
    print(f"wrote: {edges_csv}")
    print(f"wrote: {residue_csv}")
    print(f"wrote: {summary_md}")


if __name__ == "__main__":
    main()
