#!/usr/bin/env python3
"""Evaluate cycle budget and governance health from monitor log."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any, Dict, Optional


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Check cycle budget status")
    p.add_argument("--monitor-log", required=True)
    p.add_argument("--output", required=True)
    p.add_argument("--cycle-id", default="", help="Specific cycle; default latest")
    p.add_argument("--manager-cap", type=float, default=0.15)
    p.add_argument("--premium-cap", type=float, default=0.35)
    p.add_argument("--quota-warning", type=float, default=0.80)
    return p.parse_args()


def parse_float(v: str, default: float = 0.0) -> float:
    try:
        return float(v)
    except Exception:
        return default


def load_row(path: Path, cycle_id: str) -> Dict[str, str]:
    with path.open(newline="", encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    if not rows:
        raise SystemExit("monitor-log-empty")
    if cycle_id:
        for r in rows:
            if r.get("cycle_id") == cycle_id:
                return r
        raise SystemExit(f"cycle-not-found:{cycle_id}")
    return rows[-1]


def quota_value(provider_state: str) -> Optional[float]:
    # Supports simple forms: "0.72", "not_started", or JSON-like "{...}"
    provider_state = (provider_state or "").strip()
    if not provider_state or provider_state == "not_started":
        return None
    try:
        return float(provider_state)
    except Exception:
        try:
            obj = json.loads(provider_state)
            if isinstance(obj, dict):
                vals = []
                for v in obj.values():
                    try:
                        vals.append(float(v))
                    except Exception:
                        pass
                if vals:
                    return max(vals)
        except Exception:
            return None
    return None


def main() -> int:
    args = parse_args()
    row = load_row(Path(args.monitor_log), args.cycle_id)

    manager = parse_float(row.get("manager_token_share", "0"), 0.0)
    premium = parse_float(row.get("premium_token_share", "0"), 0.0)
    breaches = int(parse_float(row.get("governance_breach_count", "0"), 0.0))
    qv = quota_value(row.get("provider_quota_state", ""))

    findings = []
    actions = []

    if manager > args.manager_cap:
        findings.append("manager-cap-exceeded")
        actions.append("delegate-remaining-tasks")
    if premium > args.premium_cap:
        findings.append("premium-cap-exceeded")
        actions.append("block-noncritical-premium-calls")
    if qv is not None and qv >= args.quota_warning:
        findings.append("provider-quota-warning")
        actions.append("reroute-noncritical")
    if breaches > 0:
        findings.append("governance-breach")
        actions.append("mark-cycle-invalid-for-promotion")

    if "governance-breach" in findings or "manager-cap-exceeded" in findings:
        health = "red"
    elif findings:
        health = "amber"
    else:
        health = "green"

    report: Dict[str, Any] = {
        "cycle_id": row.get("cycle_id"),
        "manager_token_share": manager,
        "premium_token_share": premium,
        "provider_quota_max": qv,
        "governance_breach_count": breaches,
        "health": health,
        "findings": findings,
        "actions": actions,
    }

    out = Path(args.output)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"wrote={out} health={health} findings={len(findings)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
