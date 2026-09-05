#!/usr/bin/env python3
from __future__ import annotations

from fractions import Fraction
import csv
import math
import random
from itertools import combinations

OUT_SUMMARY = "/tmp/lrc_defect_move_audit_summary_v1.md"
OUT_ROWS = "/tmp/lrc_defect_move_audit_rows_v1.csv"

RANDOM_SEED = 0
SAMPLES_PER_N = 120
MAXV_BY_N = {5: 10, 6: 10, 7: 10, 8: 10}


def move_hole_insert_suffix(E: tuple[int, ...], p: int) -> tuple[int, ...]:
    arr = list(E)
    for i in range(p - 1, len(arr)):
        arr[i] += 1
    return tuple(arr)


def forbidden_density(E: tuple[int, ...], n: int):
    L = math.lcm(*E)
    N = n * L
    bad = 0
    for k in range(N):
        s = Fraction(k, N)
        is_bad = False
        for e in E:
            v = (e * s) % 1
            if not (Fraction(1, n) <= v <= Fraction(n - 1, n)):
                is_bad = True
                break
        if is_bad:
            bad += 1
    return bad / N, bad, N, L


def defects(E: tuple[int, ...]) -> tuple[int, ...]:
    # d_j = e_j - j for sorted strict tuple
    return tuple(E[i] - (i + 1) for i in range(len(E)))


def decomposition_exponents(E: tuple[int, ...]) -> tuple[int, ...]:
    # eta_p = d_p - d_{p-1}, d_0=0
    d = defects(E)
    out = []
    prev = 0
    for x in d:
        out.append(x - prev)
        prev = x
    return tuple(out)


def main():
    random.seed(RANDOM_SEED)

    rows = []
    summary = []

    for n, maxv in MAXV_BY_N.items():
        m = n - 1
        all_tuples = list(combinations(range(1, maxv + 1), m))
        sample = random.sample(all_tuples, min(SAMPLES_PER_N, len(all_tuples)))

        move_tests = 0
        dens_nonincrease_ok = 0
        dens_nonincrease_fail = 0

        for E in sample:
            fE, badE, NE, LE = forbidden_density(E, n)
            dE = defects(E)
            etaE = decomposition_exponents(E)

            for p in range(1, m + 1):
                E2 = move_hole_insert_suffix(E, p)
                fE2, badE2, NE2, LE2 = forbidden_density(E2, n)

                move_tests += 1
                ok = fE2 <= fE + 1e-12
                if ok:
                    dens_nonincrease_ok += 1
                else:
                    dens_nonincrease_fail += 1

                rows.append(
                    {
                        "n": n,
                        "E": " ".join(map(str, E)),
                        "defects_d": " ".join(map(str, dE)),
                        "decomp_eta": " ".join(map(str, etaE)),
                        "move_p": p,
                        "E_prime": " ".join(map(str, E2)),
                        "f_E": f"{fE:.12f}",
                        "f_E_prime": f"{fE2:.12f}",
                        "N_E": NE,
                        "N_E_prime": NE2,
                        "bad_E": badE,
                        "bad_E_prime": badE2,
                        "ineq_f_nonincrease": int(ok),
                    }
                )

        summary.append(
            {
                "n": n,
                "sample_tuples": len(sample),
                "move_tests": move_tests,
                "dens_nonincrease_ok": dens_nonincrease_ok,
                "dens_nonincrease_fail": dens_nonincrease_fail,
                "ok_rate": dens_nonincrease_ok / move_tests if move_tests else 0.0,
            }
        )

    with open(OUT_ROWS, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    lines = []
    lines.append("# Defect-Move Inequality Audit (v1)")
    lines.append("")
    lines.append("Primitive move tested:")
    lines.append("- `H_p`: suffix hole insertion (`e_p..e_m += 1`) on strict sorted tuple `E`.")
    lines.append("")
    lines.append("Inequality tested:")
    lines.append("- `f(H_p(E)) <= f(E)` where `f(E)=|U D_e|/N` is forbidden density.")
    lines.append("")
    lines.append("| n | sampled tuples | move tests | nonincrease OK | nonincrease FAIL | OK rate |")
    lines.append("|---:|---:|---:|---:|---:|---:|")
    for r in summary:
        lines.append(
            f"| {r['n']} | {r['sample_tuples']} | {r['move_tests']} | {r['dens_nonincrease_ok']} | {r['dens_nonincrease_fail']} | {r['ok_rate']:.4f} |"
        )

    lines.append("")
    lines.append("Conclusion:")
    lines.append("- This naive monotonic inequality is not universally true on sampled exact checks.")
    lines.append("- Defect-monotonic proof must use a stronger/structured potential than raw `f` per single move.")
    lines.append("")
    lines.append("Artifacts:")
    lines.append(f"- rows: `{OUT_ROWS}`")
    lines.append(f"- summary: `{OUT_SUMMARY}`")

    with open(OUT_SUMMARY, "w") as f:
        f.write("\n".join(lines) + "\n")

    print("FINAL")
    print("rows", OUT_ROWS)
    print("summary", OUT_SUMMARY)


if __name__ == "__main__":
    main()
