#!/usr/bin/env python3
from __future__ import annotations

import csv
import math
from collections import Counter, defaultdict
from fractions import Fraction

N = 11

OUT_ROWS = "/tmp/lrc_case2_n11_family_set_rows_v3.csv"
OUT_CMODELS = "/tmp/lrc_case2_n11_family_set_cmodels_v3.csv"
OUT_SIGMODELS = "/tmp/lrc_case2_n11_family_set_signature_models_v3.csv"
OUT_SUMMARY = "/tmp/lrc_case2_n11_family_set_summary_v3.md"


def rat(x: float, max_den: int = 1000000) -> str:
    return str(Fraction(x).limit_denominator(max_den))


def fit_periodic_linear(points, period):
    by_r = defaultdict(list)
    for M, y in points:
        by_r[M % period].append((M, y))

    model = {}
    for r, arr in by_r.items():
        arr.sort()
        if len(arr) < 2:
            continue
        M1, y1 = arr[0]
        M2, y2 = arr[1]
        a = (y2 - y1) / (M2 - M1)
        b = y1 - a * M1
        for M, y in arr:
            if abs((a * M + b) - y) > 1e-9:
                return False, {}, 0
        model[r] = (a, b, len(arr))

    return True, model, len(model)


def eval_family(E, slot_speeds):
    n = N
    L = math.lcm(*E)
    NL = n * L
    lo = L
    hi = (n - 1) * L

    E_div = [e for e in E if e % n == 0]
    E_non = [e for e in E if e % n != 0]

    # fast path when only divisible speed is 11
    if len(E_div) == 1 and E_div[0] == 11:
        b_lo = L // n
        b_hi = ((n - 1) * L) // n
        B_div_vals = range(b_lo, b_hi + 1)
        B_div = b_hi - b_lo + 1
    else:
        b_vals = []
        for b in range(L):
            ok = True
            for e in E_div:
                x = (e * b) % NL
                if x < lo or x > hi:
                    ok = False
                    break
            if ok:
                b_vals.append(b)
        B_div_vals = b_vals
        B_div = len(b_vals)

    C_bad = 0
    sig_count = Counter()

    for b in B_div_vals:
        # compressed signature for periodic-linear occupancy modeling
        s = []
        for e in slot_speeds:
            x = (e * b) % NL
            s.append((int(x // L), 1 if x % L else 0))
        sig_count[tuple(s)] += 1

        bad = True
        for a in range(n):
            k = a * L + b
            ok = True
            for e in E_non:
                x = (e * k) % NL
                if x < lo or x > hi:
                    ok = False
                    break
            if ok:
                bad = False
                break
        if bad:
            C_bad += 1

    return {
        "L": L,
        "B_div": B_div,
        "C_bad": C_bad,
        "B_safe": B_div - C_bad,
        "sig_count": sig_count,
    }


FAMILIES = {
    "F1": {
        "desc": "E(M)=(1^8,M,11), 11∤M",
        "M_values": [m for m in range(1, 485) if m % 11 != 0],
        "build": lambda M: (1, 1, 1, 1, 1, 1, 1, 1, M, 11),
        "slot_speeds": lambda M: [1, M],
        "period": 121,
        "C_F": 9,
        "B_formula": lambda M: 9 * M + 1,
        "B_formula_text": "9M+1",
    },
    "F12": {
        "desc": "E(M)=(1^7,M,11,22), gcd(M,22)=1",
        "M_values": [m for m in range(1, 485) if math.gcd(m, 22) == 1],
        "build": lambda M: (1, 1, 1, 1, 1, 1, 1, M, 11, 22),
        "slot_speeds": lambda M: [1, M],
        "period": 121,
        "C_F": 16,
        "B_formula": lambda M: 16 * M + 2,
        "B_formula_text": "16M+2",
    },
    "F1246689": {
        "desc": "E(M)=(1,2,3,4,6,6,8,9,M,11), gcd(M,792)=1",
        "M_values": [m for m in range(1, 501) if math.gcd(m, 792) == 1],
        "build": lambda M: (1, 2, 3, 4, 6, 6, 8, 9, M, 11),
        "slot_speeds": lambda M: [1, M],
        "period": 121,
        "C_F": 648,
        "B_formula": lambda M: 648 * M + 1,
        "B_formula_text": "648M+1",
    },
}


def main():
    rows = []
    cmodel_rows = []
    sig_rows = []
    summary = []

    summary.append("# n=11 Family Set (v3)")
    summary.append("")
    summary.append("Goal outputs: explicit `B_div(F,M)` formulas, exact periodic-linear `N_s(F,M)` forms, and `alpha_F` vs `C_F`.")
    summary.append("")
    summary.append("## Family Definitions")
    summary.append("")
    for fam, cfg in FAMILIES.items():
        summary.append(f"- **{fam}**: `{cfg['desc']}`")
    summary.append("")

    summary.append("## Alpha vs C Table")
    summary.append("")
    summary.append("| family | tested M | B_div formula exact | C_F | C_bad fit (period) | alpha_F range | max C_bad | min(B_safe-(n-1)) |")
    summary.append("|---|---:|---:|---:|---:|---|---:|---:|")

    for fam, cfg in FAMILIES.items():
        M_values = cfg["M_values"]
        period = cfg["period"]

        bdiv_ok = True
        sig_series = defaultdict(list)
        cbad_points = []
        bsafe_points = []

        max_cbad = 0
        min_margin = None

        for M in M_values:
            t = eval_family(cfg["build"](M), cfg["slot_speeds"](M))

            if t["B_div"] != cfg["B_formula"](M):
                bdiv_ok = False

            margin = t["B_safe"] - (N - 1)
            if min_margin is None or margin < min_margin:
                min_margin = margin
            max_cbad = max(max_cbad, t["C_bad"])

            cbad_points.append((M, t["C_bad"]))
            bsafe_points.append((M, t["B_safe"]))

            for s, c in t["sig_count"].items():
                sig_series[s].append((M, c))

            rows.append(
                {
                    "family": fam,
                    "M": M,
                    "L": t["L"],
                    "B_div": t["B_div"],
                    "C_bad": t["C_bad"],
                    "B_safe": t["B_safe"],
                    "B_margin": margin,
                    "period_used": period,
                }
            )

        ok_cbad, model_cbad, classes_cbad = fit_periodic_linear(cbad_points, period)
        ok_bsafe, model_bsafe, classes_bsafe = fit_periodic_linear(bsafe_points, period)

        if max_cbad == 0:
            alpha_range = "[0,0]"
        elif ok_cbad and classes_cbad > 0:
            slopes = [v[0] for v in model_cbad.values()]
            alpha_range = f"[{rat(min(slopes))}, {rat(max(slopes))}]"
        else:
            alpha_range = "fit-failed"

        summary.append(
            f"| {fam} | {len(M_values)} | {1 if bdiv_ok else 0} | {cfg['C_F']} | "
            f"{1 if ok_cbad else 0} ({period}) | {alpha_range} | {max_cbad} | {min_margin} |"
        )

        # store C_bad/B_safe class models
        if ok_cbad:
            for r, (a, b, cnt) in sorted(model_cbad.items()):
                cmodel_rows.append(
                    {
                        "family": fam,
                        "target": "C_bad",
                        "period": period,
                        "residue": r,
                        "slope_a": rat(a),
                        "intercept_b": rat(b),
                        "points_in_class": cnt,
                    }
                )
        if ok_bsafe:
            for r, (a, b, cnt) in sorted(model_bsafe.items()):
                cmodel_rows.append(
                    {
                        "family": fam,
                        "target": "B_safe",
                        "period": period,
                        "residue": r,
                        "slope_a": rat(a),
                        "intercept_b": rat(b),
                        "points_in_class": cnt,
                    }
                )

        # top signature models
        ranked = []
        for s, pts in sig_series.items():
            avg = sum(y for _, y in pts) / len(pts)
            ranked.append((avg, s, pts))
        ranked.sort(reverse=True, key=lambda x: x[0])

        top = ranked[:8]
        fit_ok = 0
        for avg, s, pts in top:
            ok_s, model_s, classes_s = fit_periodic_linear(pts, period)
            fit_ok += 1 if ok_s else 0
            if ok_s:
                for r, (a, b, cnt) in sorted(model_s.items()):
                    sig_rows.append(
                        {
                            "family": fam,
                            "signature": str(s),
                            "period": period,
                            "residue": r,
                            "slope_a": rat(a),
                            "intercept_b": rat(b),
                            "points_in_class": cnt,
                            "avg_Ns": f"{avg:.6f}",
                        }
                    )

        summary.append("")
        summary.append(f"### {fam}")
        summary.append(f"- `B_div(M)={cfg['B_formula_text']}` exact on tested M: `{1 if bdiv_ok else 0}`")
        summary.append(f"- `C_bad(M)` periodic-linear fit success: `{1 if ok_cbad else 0}` with period `{period}` and `{classes_cbad}` residue classes")
        if ok_cbad and classes_cbad > 0:
            slopes = sorted(v[0] for v in model_cbad.values())
            summary.append(f"- `C_bad` slope range: `[{rat(slopes[0])}, {rat(slopes[-1])}]`")
        summary.append(f"- Top signature fits (slots [1,M]): `{fit_ok}/{len(top)}`")

        # sample formula lines (compact)
        if ok_cbad and classes_cbad > 0:
            sample_rs = sorted(model_cbad)[:3]
            summary.append("- Sample `C_bad` class formulas:")
            for r in sample_rs:
                a, b, cnt = model_cbad[r]
                summary.append(f"  - r={r}: `C_bad={rat(a)}*M + {rat(b)}` (points={cnt})")

        summary.append("")

    with open(OUT_ROWS, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    with open(OUT_CMODELS, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(cmodel_rows[0].keys()))
        w.writeheader()
        w.writerows(cmodel_rows)

    with open(OUT_SIGMODELS, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(sig_rows[0].keys()))
        w.writeheader()
        w.writerows(sig_rows)

    with open(OUT_SUMMARY, "w") as f:
        f.write("\n".join(summary) + "\n")

    print("wrote:", OUT_ROWS)
    print("wrote:", OUT_CMODELS)
    print("wrote:", OUT_SIGMODELS)
    print("wrote:", OUT_SUMMARY)


if __name__ == "__main__":
    main()
