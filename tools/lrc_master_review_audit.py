#!/usr/bin/env python3
from __future__ import annotations

import csv
import hashlib
import os
import re
from collections import Counter, defaultdict
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Dict, Iterable, List, Tuple


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex").resolve()
CLAUDE_LIBRARY = Path("/Users/trentpalelei/Documents/Claude Library").resolve()
OUTPUT_DIR = ROOT / "reports" / "reviews" / "lrc_master_review_2026-03-30"

SOURCE_LEDGER = OUTPUT_DIR / "lrc_master_source_ledger_2026-03-30.csv"
DISCOVERY_LEDGER = OUTPUT_DIR / "lrc_master_discovery_ledger_2026-03-30.csv"
CONFLICT_LEDGER = OUTPUT_DIR / "lrc_master_conflict_ledger_2026-03-30.csv"
DOSSIER = OUTPUT_DIR / "lrc_master_review_dossier_2026-03-30.md"

EXCLUDED_SUFFIXES = {
    ".aux",
    ".log",
    ".out",
    ".toc",
    ".pyc",
}
TEXT_SUFFIXES = {
    ".md",
    ".txt",
    ".tex",
    ".csv",
    ".json",
    ".py",
    ".rtf",
    ".toml",
    ".yaml",
    ".yml",
    ".html",
}


@dataclass
class ArtifactRecord:
    artifact: str
    bucket: str
    date: str
    scope: str
    status_type: str
    evidence_type: str
    duplicate_group: str
    authority_rank: int
    notes: str
    sha256: str


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read_head(path: Path, limit: int = 12000) -> str:
    if path.suffix.lower() not in TEXT_SUFFIXES:
        return ""
    try:
        with path.open("r", encoding="utf-8", errors="ignore") as handle:
            return handle.read(limit)
    except OSError:
        return ""


DATE_PATTERNS = [
    re.compile(r"(?im)^\*\*Date:\*\*\s*([0-9]{4}-[0-9]{2}-[0-9]{2})"),
    re.compile(r"(?im)^Date:\s*([0-9]{4}-[0-9]{2}-[0-9]{2})"),
    re.compile(r"(?im)^Generated:\s*([0-9]{4}-[0-9]{2}-[0-9]{2})"),
    re.compile(r"(?im)^Summary prepared:\s*([0-9]{4}-[0-9]{2}-[0-9]{2})"),
    re.compile(r"(?im)^Last reviewed:\s*([0-9]{4}-[0-9]{2}-[0-9]{2})"),
]
FILENAME_DATE_PATTERNS = [
    re.compile(r"(20[0-9]{2}-[0-9]{2}-[0-9]{2})"),
    re.compile(r"(20[0-9]{2}[01][0-9][0-3][0-9])"),
]


def extract_date(path: Path) -> str:
    head = read_head(path)
    for pattern in DATE_PATTERNS:
        match = pattern.search(head)
        if match:
            return match.group(1)
    for pattern in FILENAME_DATE_PATTERNS:
        match = pattern.search(path.name)
        if match:
            token = match.group(1)
            if len(token) == 8:
                return f"{token[0:4]}-{token[4:6]}-{token[6:8]}"
            return token
    return datetime.fromtimestamp(path.stat().st_mtime).strftime("%Y-%m-%d")


def root_label(path: Path) -> str:
    return "Math Ex" if str(path).startswith(str(ROOT)) else "Claude Library"


def rel_string(path: Path, root: Path) -> str:
    try:
        return path.relative_to(root).as_posix().lower()
    except ValueError:
        return path.name.lower()


def is_included(path: Path, source_root: Path) -> bool:
    if not path.is_file():
        return False
    if path.name.startswith("."):
        return False
    if path.suffix.lower() in EXCLUDED_SUFFIXES:
        return False

    rel = rel_string(path, source_root)
    name = path.name.lower()

    if source_root == ROOT and (rel.startswith("reports/") or rel.startswith("registry/")):
        return True

    if "claim-lrc" in rel or "claim-lrc" in name:
        return True

    if "lrc" in rel or "lrc" in name:
        return True

    if rel.startswith("swarm_planning/") and "lrc" in rel:
        return True

    if rel.startswith("swarm_skills/") and "lrc" in rel:
        return True

    return False


def classify_bucket(path: Path, source_root: Path) -> str:
    rel = rel_string(path, source_root)
    name = path.name.lower()

    if rel.startswith("reports/proofs/lrc_proof_pack_2026-03-01/"):
        return "proof-pack/certifier export"
    if rel.startswith("reports/"):
        return "claim-validation report"
    if rel.startswith("registry/"):
        return "claim-validation registry"
    if rel.startswith("swarm_planning/") or rel.startswith("swarm_skills/"):
        return "coordination/planning"
    if rel.startswith("tools/"):
        return "tooling"

    if source_root == CLAUDE_LIBRARY and name.startswith("lrc_multidiv_"):
        return "spillover/multidiv"
    if source_root == CLAUDE_LIBRARY and name.startswith("lrc_sv56_"):
        return "spillover/sv56"
    if source_root == CLAUDE_LIBRARY and name.startswith("lrc_n11_"):
        if any(token in name for token in ("outer_", "exact_pair", "fsccc", "pscc", "sct", "cpot", "drwt")):
            return "spillover/n11 route memo"
        return "spillover/n11 memo"

    if name.startswith("lrc_n11_"):
        return "n=11 canon/draft"
    if name.startswith("lrc_proof_v") or name in {
        "lrc_proof_status.md",
        "lrc_transport_completeness_v1.md",
        "lrc_transport_completeness_v2.md",
        "lrc_transport_kge3_failure_note_v1.md",
        "lrc_prime_power_tier2_v1.md",
        "lrc_prime_power_persistence_v1.md",
        "lrc_small_cases_analytic_closure_2026-03-13.md",
        "lrc_8_2c_nonunit_closure_2026-03-12.md",
    }:
        return "all-n proof/preprint"
    if name.startswith(("lrc_prime_power_", "lrc_transport_", "lrc_c4_", "lrc_gap", "lrc_case2_", "lrc_ap_")):
        return "all-n supporting theorem/memo"
    if name.startswith("lrc_"):
        return "all-n supporting theorem/memo"

    return "supporting material"


def classify_scope(path: Path, source_root: Path) -> str:
    rel = rel_string(path, source_root)
    name = path.name.lower()

    if rel.startswith("reports/") or rel.startswith("registry/"):
        return "empirical pipeline"
    if "n11" in name or "n11" in rel:
        return "n=11"
    if "multidiv" in name or "gap2" in name:
        return "branch-scoped multidiv"
    if name.startswith("lrc_sv56_") or "prime_power" in name:
        return "branch-scoped prime-power"
    if any(token in name for token in ("gap4", "g4", "caseb", "lambda")):
        return "branch-scoped composite/gap4"
    if rel.startswith("swarm_") or rel.startswith("tools/"):
        return "coordination/tooling"
    return "all-n"


def classify_status_type(path: Path, source_root: Path) -> str:
    name = path.name.lower()
    rel = rel_string(path, source_root)

    if "canonical_status_ledger" in name:
        return "canonical status ledger"
    if name in {"lrc_proof_status.md", "lrc_gap_status_n_all_v1.md"}:
        return "status ledger"
    if any(token in name for token in ("audit", "assessment", "review", "decision_memo", "status_memo", "readiness")):
        return "audit/status memo"
    if any(token in name for token in ("paper", "preprint", "theorem", "lemma", "proof", "corollary")):
        return "theorem/proof file"
    if any(token in name for token in ("summary", "note", "memo", "program", "plan", "roadmap", "handoff", "catalogue", "synthesis")):
        return "memo/program file"
    if path.suffix.lower() in {".py", ".csv", ".json"}:
        return "computational artifact"
    if rel.startswith("swarm_") or rel.startswith("tools/"):
        return "tooling/planning artifact"
    return "supporting artifact"


def classify_evidence_type(path: Path) -> str:
    suffix = path.suffix.lower()
    if suffix in {".md", ".tex", ".pdf"}:
        return "writeup"
    if suffix == ".py":
        return "script"
    if suffix == ".csv":
        return "tabular data"
    if suffix == ".json":
        return "structured output"
    if suffix in {".txt", ".rtf", ".html", ".toml", ".yaml", ".yml"}:
        return "support text"
    return "artifact"


def default_authority_rank(status_type: str) -> int:
    if status_type in {"canonical status ledger", "theorem/proof file"}:
        return 1
    if status_type in {"audit/status memo", "status ledger"}:
        return 2
    if status_type in {"memo/program file", "tooling/planning artifact"}:
        return 3
    if status_type == "supporting artifact":
        return 4
    return 5


def apply_overrides(base: Dict[str, str | int], overrides: Dict[str, Dict[str, str | int]]) -> Dict[str, str | int]:
    out = dict(base)
    if base["artifact"] in overrides:
        out.update(overrides[base["artifact"]])
    return out


def build_manual_overrides() -> Dict[str, Dict[str, str | int]]:
    paths = {
        "n11_ledger_v2": ROOT / "lrc_n11_canonical_status_ledger_v2.md",
        "n11_paper_v22": ROOT / "lrc_n11_ap_paper_v22.md",
        "n11_static_core": ROOT / "lrc_n11_static_core_theorem_v1.md",
        "n11_u_v3": ROOT / "lrc_n11_universalincompat_v3.md",
        "n11_s1": ROOT / "lrc_n11_lemma_s1_runner2_elimination_v1.md",
        "n11_s2": ROOT / "lrc_n11_lemma_s2_proof_v2.md",
        "n11_periodicity": ROOT / "lrc_n11_periodicity_lemma_v1.md",
        "alln_v78": ROOT / "lrc_proof_v7_8_preprint.md",
        "proof_status": ROOT / "lrc_proof_status.md",
        "pub_bar": ROOT / "reports" / "publication_bar_assessment_cycle_003.md",
        "math_pr": ROOT / "reports" / "matsengrp" / "math-pr-summary-v7_6.md",
        "scholareval": ROOT / "reports" / "scholareval" / "scholareval-v7_6.md",
        "journal_check": ROOT / "reports" / "matsengrp" / "journal-submission-check-v7_6.md",
        "d3_summary": ROOT / "reports" / "proofs" / "lrc_proof_pack_2026-03-01" / "lrc_case2_d3_batch_summary_n7n11_v2.md",
        "multidiv_summary": ROOT / "reports" / "proofs" / "lrc_proof_pack_2026-03-01" / "lrc_case2_multidiv_batch_summary_n13_d23_f1234_m100_v1.md",
        "gap4_track": ROOT / "reports" / "proofs" / "lrc_proof_pack_2026-03-01" / "lrc_gap4_complementarity_theorem_track_v1.md",
        "gap_status": ROOT / "reports" / "proofs" / "lrc_proof_pack_2026-03-01" / "lrc_gap_status_n_all_v1.md",
        "release_note": ROOT / "reports" / "proofs" / "lrc_proof_pack_2026-03-01" / "lrc_release_readiness_note_2026-03-09.md",
        "project_review": CLAUDE_LIBRARY / "lrc_project_review_2026-03-06.md",
        "n11_ledger_v1": CLAUDE_LIBRARY / "lrc_n11_canonical_status_ledger_v1.md",
        "n11_mech_audit": CLAUDE_LIBRARY / "lrc_n11_mechanism_audit_report_v1.md",
        "primepower_t2": CLAUDE_LIBRARY / "lrc_prime_power_tier2_closure_v1.md",
        "n11_actual_state": CLAUDE_LIBRARY / "lrc_n11_actual_state_theorem_summary_v1.md",
        "n11_outer_confinement": CLAUDE_LIBRARY / "lrc_n11_outer_confinement_results_v1.md",
        "n11_exact_pair": CLAUDE_LIBRARY / "lrc_n11_exact_pair_decision_memo_v1.md",
        "n11_two_theorem": CLAUDE_LIBRARY / "lrc_n11_two_theorem_discovery_plan_v1.md",
    }

    def p(key: str) -> str:
        return str(paths[key].resolve())

    return {
        p("n11_ledger_v2"): {
            "bucket": "n=11 canon/draft",
            "scope": "n=11",
            "status_type": "canonical status ledger",
            "evidence_type": "writeup",
            "authority_rank": 1,
            "notes": "Canonical local n=11 ledger after static-core extraction; explicitly demotes SET/WIT routes.",
        },
        p("n11_paper_v22"): {
            "bucket": "n=11 canon/draft",
            "scope": "n=11",
            "status_type": "theorem/proof file",
            "evidence_type": "writeup",
            "authority_rank": 1,
            "notes": "Canonical clean n=11 AP paper per v2 ledger; historical routes moved to appendix.",
        },
        p("n11_static_core"): {
            "status_type": "theorem/proof file",
            "authority_rank": 1,
            "notes": "Authoritative static-front theorem note for n=11.",
        },
        p("n11_u_v3"): {
            "status_type": "theorem/proof file",
            "authority_rank": 1,
            "notes": "Canonical sigma_2=+1 closure note for n=11.",
        },
        p("n11_s1"): {
            "status_type": "theorem/proof file",
            "authority_rank": 1,
            "notes": "Canonical runner-2 elimination lemma for n=11.",
        },
        p("n11_s2"): {
            "status_type": "theorem/proof file",
            "authority_rank": 1,
            "notes": "Canonical sigma_2=-1 closure note for n=11.",
        },
        p("n11_periodicity"): {
            "status_type": "theorem/proof file",
            "authority_rank": 1,
            "notes": "Canonical phase-independence / W_ref closure note for residual Case R>.",
        },
        p("alln_v78"): {
            "bucket": "all-n proof/preprint",
            "scope": "all-n",
            "status_type": "theorem/proof file",
            "evidence_type": "writeup",
            "authority_rank": 1,
            "notes": "Current all-n preprint claiming Theorem A; local theorem authority outranks older status memos but remains cross-packet conflicted.",
        },
        p("proof_status"): {
            "bucket": "all-n proof/preprint",
            "scope": "all-n",
            "status_type": "status ledger",
            "evidence_type": "writeup",
            "authority_rank": 2,
            "notes": "Stale v6.3-era status ledger; superseded on prime-power Tier 2 by later closure text and v7.8 preprint.",
        },
        p("pub_bar"): {
            "bucket": "claim-validation report",
            "scope": "empirical pipeline",
            "status_type": "audit/status memo",
            "evidence_type": "writeup",
            "authority_rank": 2,
            "notes": "Governance assessment of the claim pipeline; not a theorem-truth authority for the all-n preprint.",
        },
        p("math_pr"): {
            "bucket": "claim-validation report",
            "scope": "all-n",
            "status_type": "audit/status memo",
            "evidence_type": "writeup",
            "authority_rank": 2,
            "notes": "Summarizes v7.6 as if prime-power Tier 2 is closed; useful for theorem extraction but not the final canonical ledger.",
        },
        p("scholareval"): {
            "bucket": "claim-validation report",
            "scope": "all-n",
            "status_type": "audit/status memo",
            "evidence_type": "writeup",
            "authority_rank": 2,
            "notes": "External-style review of v7.6; flags presentation gaps but not a direct refutation.",
        },
        p("journal_check"): {
            "bucket": "claim-validation report",
            "scope": "all-n",
            "status_type": "audit/status memo",
            "evidence_type": "writeup",
            "authority_rank": 2,
            "notes": "Submission checklist for v7.6; scope is publication readiness, not mathematical invalidation.",
        },
        p("d3_summary"): {
            "bucket": "proof-pack/certifier export",
            "scope": "empirical pipeline",
            "status_type": "computational artifact",
            "evidence_type": "writeup",
            "authority_rank": 5,
            "notes": "Exact finite-window certification only; theorem support but not asymptotic closure.",
        },
        p("multidiv_summary"): {
            "bucket": "proof-pack/certifier export",
            "scope": "branch-scoped multidiv",
            "status_type": "computational artifact",
            "evidence_type": "writeup",
            "authority_rank": 5,
            "notes": "Finite-window certification only; explicitly not a full asymptotic closure theorem.",
        },
        p("gap4_track"): {
            "bucket": "proof-pack/certifier export",
            "scope": "branch-scoped composite/gap4",
            "status_type": "theorem/proof file",
            "evidence_type": "writeup",
            "authority_rank": 2,
            "notes": "Theorem-track block with G4.A proved, G4.B open target, G4.C conditional.",
        },
        p("gap_status"): {
            "bucket": "proof-pack/certifier export",
            "scope": "all-n",
            "status_type": "status ledger",
            "evidence_type": "writeup",
            "authority_rank": 2,
            "notes": "Historical n=all phi-target gap map; not the same theorem scope as v7.8 Theorem A.",
        },
        p("release_note"): {
            "bucket": "proof-pack/certifier export",
            "scope": "empirical pipeline",
            "status_type": "audit/status memo",
            "evidence_type": "writeup",
            "authority_rank": 2,
            "notes": "Proof-pack export readiness and hash inventory for certification artifacts.",
        },
        p("project_review"): {
            "bucket": "spillover/n11 memo",
            "scope": "all-n",
            "status_type": "audit/status memo",
            "evidence_type": "writeup",
            "authority_rank": 2,
            "notes": "March 6 review explicitly says no all-n proof in the interim packet; conflicts with later v7.8 theorem claim.",
        },
        p("n11_ledger_v1"): {
            "bucket": "spillover/n11 memo",
            "scope": "n=11",
            "status_type": "canonical status ledger",
            "evidence_type": "writeup",
            "authority_rank": 2,
            "notes": "Pre-extraction n=11 ledger from March 26; superseded by v2 local canonical ledger on March 27.",
        },
        p("n11_mech_audit"): {
            "bucket": "spillover/n11 memo",
            "scope": "n=11",
            "status_type": "audit/status memo",
            "evidence_type": "writeup",
            "authority_rank": 2,
            "notes": "Mechanism-first audit snapshot before the final periodicity/W_ref extraction.",
        },
        p("primepower_t2"): {
            "bucket": "spillover/sv56",
            "scope": "branch-scoped prime-power",
            "status_type": "theorem/proof file",
            "evidence_type": "writeup",
            "authority_rank": 1,
            "notes": "Branch-specific closure memo claiming odd prime-power Tier 2 closure via one-cell bridge.",
        },
        p("n11_actual_state"): {
            "bucket": "spillover/n11 memo",
            "scope": "n=11",
            "status_type": "memo/program file",
            "evidence_type": "writeup",
            "authority_rank": 3,
            "notes": "Exact state-space theorem summary backed by explicit witness CSV, but not promoted to canonical paper text.",
        },
        p("n11_outer_confinement"): {
            "bucket": "spillover/n11 route memo",
            "scope": "n=11",
            "status_type": "memo/program file",
            "evidence_type": "writeup",
            "authority_rank": 3,
            "notes": "Search summary for outer-confinement route; mechanism evidence, not theorem closure.",
        },
        p("n11_exact_pair"): {
            "bucket": "spillover/n11 route memo",
            "scope": "n=11",
            "status_type": "audit/status memo",
            "evidence_type": "writeup",
            "authority_rank": 3,
            "notes": "Decision memo explicitly says exact-pair branch is not computationally closed.",
        },
        p("n11_two_theorem"): {
            "bucket": "spillover/n11 route memo",
            "scope": "n=11",
            "status_type": "memo/program file",
            "evidence_type": "writeup",
            "authority_rank": 3,
            "notes": "Critical-path research plan for missing DRWT/CPOT theorems; superseded if v2 ledger is accepted.",
        },
    }


def gather_artifacts() -> List[Path]:
    artifacts: List[Path] = []
    for source_root in (ROOT, CLAUDE_LIBRARY):
        for path in source_root.rglob("*"):
            if is_included(path, source_root):
                artifacts.append(path.resolve())
    return sorted(set(artifacts))


def build_source_ledger() -> List[ArtifactRecord]:
    artifacts = gather_artifacts()
    overrides = build_manual_overrides()

    sha_map: Dict[str, str] = {}
    basename_map: Dict[str, List[Path]] = defaultdict(list)
    for path in artifacts:
        digest = sha256_file(path)
        sha_map[str(path)] = digest
        basename_map[path.name].append(path)

    duplicate_group_map: Dict[str, str] = {}
    duplicate_class_map: Dict[str, str] = {}
    duplicate_preferred_map: Dict[str, str] = {}

    groups = sorted((name, members) for name, members in basename_map.items() if len(members) > 1)
    for index, (name, members) in enumerate(groups, start=1):
        group_id = f"DG-{index:03d}"
        digests = {sha_map[str(member)] for member in members}
        duplicate_class = "identical_copy" if len(digests) == 1 else "divergent_fork"
        preferred = sorted(
            (str(member), 0 if str(member).startswith(str(ROOT)) else 1)
            for member in members
        )[0][0]
        for member in members:
            duplicate_group_map[str(member)] = group_id
            duplicate_class_map[str(member)] = duplicate_class
            duplicate_preferred_map[str(member)] = preferred

    records: List[ArtifactRecord] = []
    for path in artifacts:
        artifact = str(path)
        source_root = ROOT if artifact.startswith(str(ROOT)) else CLAUDE_LIBRARY
        base = {
            "artifact": artifact,
            "bucket": classify_bucket(path, source_root),
            "date": extract_date(path),
            "scope": classify_scope(path, source_root),
            "status_type": classify_status_type(path, source_root),
            "evidence_type": classify_evidence_type(path),
            "duplicate_group": duplicate_group_map.get(artifact, "unique"),
            "authority_rank": default_authority_rank(classify_status_type(path, source_root)),
            "notes": f"root={root_label(path)}",
        }
        row = apply_overrides(base, overrides)

        notes = [str(row["notes"])]
        if artifact in duplicate_group_map:
            notes.append(f"duplicate_class={duplicate_class_map[artifact]}")
            notes.append(f"preferred_copy={duplicate_preferred_map[artifact]}")
        row["notes"] = "; ".join(notes)

        records.append(
            ArtifactRecord(
                artifact=artifact,
                bucket=str(row["bucket"]),
                date=str(row["date"]),
                scope=str(row["scope"]),
                status_type=str(row["status_type"]),
                evidence_type=str(row["evidence_type"]),
                duplicate_group=str(row["duplicate_group"]),
                authority_rank=int(row["authority_rank"]),
                notes=str(row["notes"]),
                sha256=sha_map[artifact],
            )
        )

    return sorted(records, key=lambda item: (item.bucket, item.scope, item.date, item.artifact))


def write_source_ledger(records: List[ArtifactRecord]) -> None:
    with SOURCE_LEDGER.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(
            [
                "artifact",
                "bucket",
                "date",
                "scope",
                "status_type",
                "evidence_type",
                "duplicate_group",
                "authority_rank",
                "notes",
            ]
        )
        for record in records:
            writer.writerow(
                [
                    record.artifact,
                    record.bucket,
                    record.date,
                    record.scope,
                    record.status_type,
                    record.evidence_type,
                    record.duplicate_group,
                    record.authority_rank,
                    record.notes,
                ]
            )


def build_discovery_rows() -> List[Dict[str, str]]:
    p = lambda path: str(path.resolve())
    literature = {
        "survey": "[Perarnau-Serra 2025 survey](https://arxiv.org/abs/2409.20160)",
        "ros8": "[Rosenfeld 2025 eight runners](https://arxiv.org/abs/2509.14111)",
        "ros9": "[Rosenfeld 2025/2026 nine runners](https://arxiv.org/abs/2512.01912)",
        "tra910": "[Trakulthongchai 2025 nine and ten runners](https://arxiv.org/abs/2511.22427)",
    }

    return [
        {
            "claim_label": "DISC-N11-AP-COMPLETE",
            "statement": "The n=11 AP program is locally complete via the static front plus periodicity/W_ref chain; SET and WIT are no longer load-bearing.",
            "scope": "n=11 AP branch",
            "support_level": "proved/dependency-clean",
            "source_of_truth": p(ROOT / "lrc_n11_canonical_status_ledger_v2.md"),
            "corroborating_artifacts": " | ".join(
                [
                    p(ROOT / "lrc_n11_ap_paper_v22.md"),
                    p(ROOT / "lrc_n11_static_core_theorem_v1.md"),
                    p(ROOT / "lrc_n11_periodicity_lemma_v1.md"),
                ]
            ),
            "conflicts": "CONFLICT-N11-001; CONFLICT-N11-002",
            "literature_comparator": f"Comparison corpus reaches n=10 runner-count papers ({literature['ros8']}; {literature['ros9']}; {literature['tra910']}) but no verified n=11 analogue was found.",
            "novelty_verdict": "candidate new theorem-grade result",
            "next_action": "Keep as the local n=11 source of truth and package for external mathematical audit.",
        },
        {
            "claim_label": "DISC-N11-THEOREM-U",
            "statement": "Theorem U closes the sigma_2 = +1 sign classes in the n=11 AP branch.",
            "scope": "n=11 static front",
            "support_level": "proved/dependency-clean",
            "source_of_truth": p(ROOT / "lrc_n11_universalincompat_v3.md"),
            "corroborating_artifacts": " | ".join(
                [
                    p(ROOT / "lrc_n11_static_core_theorem_v1.md"),
                    p(ROOT / "lrc_n11_ap_paper_v22.md"),
                ]
            ),
            "conflicts": "CONFLICT-N11-001",
            "literature_comparator": f"No comparator in the March 30, 2026 published/arXiv corpus appears to state this n=11 AP sign-class theorem explicitly; background only in {literature['survey']}.",
            "novelty_verdict": "candidate new theorem-grade result",
            "next_action": "Retain as a named theorem dependency inside the n=11 package.",
        },
        {
            "claim_label": "DISC-N11-S2-PERIODICITY",
            "statement": "Lemma S2 plus the periodicity/W_ref package closes the sigma_2 = -1 and residual Case R> regimes for n=11.",
            "scope": "n=11 static plus residual branch",
            "support_level": "proved/dependency-clean",
            "source_of_truth": p(ROOT / "lrc_n11_periodicity_lemma_v1.md"),
            "corroborating_artifacts": " | ".join(
                [
                    p(ROOT / "lrc_n11_lemma_s2_proof_v2.md"),
                    p(ROOT / "lrc_n11_w1_argument_v1.md"),
                    p(ROOT / "lrc_n11_canonical_status_ledger_v2.md"),
                ]
            ),
            "conflicts": "CONFLICT-N11-001; CONFLICT-N11-002",
            "literature_comparator": f"The current comparison corpus includes only runner-count results through n=10 and survey-level summaries ({literature['survey']}); no matching n=11 residual-closure theorem was found.",
            "novelty_verdict": "candidate new theorem-grade result",
            "next_action": "Keep grouped with the canonical n=11 dependency chain rather than as a standalone novelty claim.",
        },
        {
            "claim_label": "DISC-ALLN-THEOREM-A",
            "statement": "The v7.8 preprint claims a full proof of the Lonely Runner Conjecture for all n >= 3 at the x_0(E) >= 1 level.",
            "scope": "all-n theorem chain",
            "support_level": "proved but packaging-conflicted",
            "source_of_truth": p(ROOT / "lrc_proof_v7_8_preprint.md"),
            "corroborating_artifacts": " | ".join(
                [
                    p(ROOT / "reports/matsengrp/math-pr-summary-v7_6.md"),
                    p(ROOT / "reports/scholareval/scholareval-v7_6.md"),
                ]
            ),
            "conflicts": "CONFLICT-ALLN-001; CONFLICT-ALLN-002; CONFLICT-ALLN-003",
            "literature_comparator": f"The external baseline still treats the general conjecture as open in {literature['survey']}; the local claim outruns the public corpus as of March 30, 2026.",
            "novelty_verdict": "candidate new theorem-grade result",
            "next_action": "Require packet-wide reconciliation and external proof checking before presenting as settled beyond the local corpus.",
        },
        {
            "claim_label": "DISC-ALLN-DROPPED-RUNNER-TARGETING",
            "statement": "The Dropped-Runner Targeting theorem isolates a floor-reset event where both coverage gates fail, yielding a safe residue in the composite Unit-Complete branch.",
            "scope": "all-n composite Unit-Complete branch",
            "support_level": "proved but packaging-conflicted",
            "source_of_truth": p(ROOT / "lrc_proof_v7_8_preprint.md"),
            "corroborating_artifacts": p(ROOT / "reports/matsengrp/math-pr-summary-v7_6.md"),
            "conflicts": "CONFLICT-ALLN-001",
            "literature_comparator": f"No analogue of this locally named theorem was found in the classical baseline or in {literature['survey']}.",
            "novelty_verdict": "candidate new theorem-grade result",
            "next_action": "Treat as one of the core candidate novel lemmas in any external all-n review.",
        },
        {
            "claim_label": "DISC-ALLN-ODD-PRIME-POWER-TIER2",
            "statement": "Odd prime-power Tier 2 closure is asserted locally: B_safe >= phi(n)(n-2)/2 for every odd prime power n = p^k with dropped non-unit pair.",
            "scope": "branch-scoped prime-power",
            "support_level": "proved but packaging-conflicted",
            "source_of_truth": p(CLAUDE_LIBRARY / "lrc_prime_power_tier2_closure_v1.md"),
            "corroborating_artifacts": " | ".join(
                [
                    p(ROOT / "lrc_proof_v7_8_preprint.md"),
                    p(ROOT / "reports/matsengrp/math-pr-summary-v7_6.md"),
                ]
            ),
            "conflicts": "CONFLICT-ALLN-002",
            "literature_comparator": f"No direct comparator appears in {literature['survey']} or the older cited corpus; this remains a local branch theorem pending reconciliation.",
            "novelty_verdict": "candidate new theorem-grade result",
            "next_action": "Update or retire the stale v6.3 status file before promoting this beyond the local corpus.",
        },
        {
            "claim_label": "DISC-GAP4-LIPSCHITZ",
            "statement": "Gap-4 theorem-track note proves an event-transition Lipschitz bound on obstruction deficit changes: |D(b+1)-D(b)| <= 4 sum g_e.",
            "scope": "branch-scoped composite/gap4",
            "support_level": "proved but packaging-conflicted",
            "source_of_truth": p(ROOT / "reports/proofs/lrc_proof_pack_2026-03-01/lrc_gap4_complementarity_theorem_track_v1.md"),
            "corroborating_artifacts": p(ROOT / "reports/proofs/lrc_proof_pack_2026-03-01/lrc_gap_status_n_all_v1.md"),
            "conflicts": "",
            "literature_comparator": f"The comparison corpus contains no published Gap-4 theorem-track statement of this form; nearest baseline remains {literature['survey']}.",
            "novelty_verdict": "candidate new theorem-grade result",
            "next_action": "Separate the proved Lipschitz lemma from the still-open complementarity cap in any external catalogue.",
        },
        {
            "claim_label": "DISC-D3-CERT-N7N11",
            "statement": "The D3 certification pack records exact finite-window zero-violation checks for 15 templates at n=7 and 45 templates at n=11.",
            "scope": "empirical pipeline / one-divisible finite window",
            "support_level": "exact certified empirical",
            "source_of_truth": p(ROOT / "reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_d3_batch_summary_n7n11_v2.md"),
            "corroborating_artifacts": " | ".join(
                [
                    p(ROOT / "reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_d3_batch_checks_n7n11_v2.csv"),
                    p(ROOT / "reports/proofs/lrc_proof_pack_2026-03-01/lrc_release_readiness_note_2026-03-09.md"),
                ]
            ),
            "conflicts": "",
            "literature_comparator": f"These are local certification artifacts, not direct literature claims; the baseline only gives runner-count results such as {literature['ros8']} and {literature['tra910']}.",
            "novelty_verdict": "not yet novelty-eligible",
            "next_action": "Use as corroborating evidence, not as a standalone theorem claim.",
        },
        {
            "claim_label": "DISC-MULTIDIV-FW-N13",
            "statement": "Finite-window multidiv certification at n=13 reports 1,320 two-divisible templates and 1,980 three-divisible templates with zero phi violations for M <= 100.",
            "scope": "branch-scoped multidiv",
            "support_level": "exact certified empirical",
            "source_of_truth": p(ROOT / "reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_multidiv_batch_summary_n13_d23_f1234_m100_v1.md"),
            "corroborating_artifacts": p(ROOT / "reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_multidiv_batch_checks_n13_d23_f1234_m100_v1.csv"),
            "conflicts": "",
            "literature_comparator": f"These exact certifications have no direct published counterpart in the comparison corpus, but they remain finite-window evidence only.",
            "novelty_verdict": "not yet novelty-eligible",
            "next_action": "Keep out of the new-knowledge section unless promoted to an analytic theorem.",
        },
        {
            "claim_label": "DISC-N11-ACTUAL-STATE-THEOREM",
            "statement": "The exact-state summary for the one-divisible n=11 branch claims that a local bad profile is actual iff q_1 >= 18 - sum_i q_i, leaving 38 actual profiles out of 45.",
            "scope": "n=11 one-divisible state space",
            "support_level": "exact certified empirical",
            "source_of_truth": p(CLAUDE_LIBRARY / "lrc_n11_actual_state_theorem_summary_v1.md"),
            "corroborating_artifacts": p(CLAUDE_LIBRARY / "lrc_n11_actual_bad_state_witnesses_v2.csv"),
            "conflicts": "",
            "literature_comparator": f"No direct published comparator was found; however the local support is still summary-plus-witness-table rather than canonical theorem packaging.",
            "novelty_verdict": "candidate new structural insight",
            "next_action": "Promote only after a dependency-clean proof note exists inside the active n=11 package.",
        },
        {
            "claim_label": "DISC-N11-OUTER-CONFINEMENT",
            "statement": "First outer-confinement search results suggest minimal nonlocal complete-blocking points collapse toward the local regime, but the naive clamp theorem fails at endpoint witness loss.",
            "scope": "n=11 outer route",
            "support_level": "mechanism insight",
            "source_of_truth": p(CLAUDE_LIBRARY / "lrc_n11_outer_confinement_results_v1.md"),
            "corroborating_artifacts": p(CLAUDE_LIBRARY / "lrc_n11_outer_confinement_search_v1.py"),
            "conflicts": "",
            "literature_comparator": "No external comparator located; this is an internal route-discovery memo rather than a theorem claim.",
            "novelty_verdict": "candidate new structural insight",
            "next_action": "Keep in the mechanism catalogue only; not a publication claim.",
        },
        {
            "claim_label": "DISC-N11-EXACT-PAIR-CARRIER-SPLIT",
            "statement": "The exact-pair computation refines the branch target to a carrier-6 local-collapse family versus carrier-5 real-obstruction family, while explicitly refusing closure.",
            "scope": "n=11 exact-pair route",
            "support_level": "mechanism insight",
            "source_of_truth": p(CLAUDE_LIBRARY / "lrc_n11_exact_pair_decision_memo_v1.md"),
            "corroborating_artifacts": p(CLAUDE_LIBRARY / "lrc_n11_exact_pair_probe_results_v1.json"),
            "conflicts": "",
            "literature_comparator": "No external comparator located; this is an internal route-compression result rather than a settled mathematical theorem.",
            "novelty_verdict": "candidate new structural insight",
            "next_action": "Retain as a route memo and do not fold into canonical n=11 status.",
        },
    ]


def write_discovery_ledger(rows: List[Dict[str, str]]) -> None:
    with DISCOVERY_LEDGER.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "claim_label",
                "statement",
                "scope",
                "support_level",
                "source_of_truth",
                "corroborating_artifacts",
                "conflicts",
                "literature_comparator",
                "novelty_verdict",
                "next_action",
            ],
        )
        writer.writeheader()
        writer.writerows(rows)


def build_conflict_rows() -> List[Dict[str, str]]:
    p = lambda path: str(path.resolve())
    return [
        {
            "issue": "CONFLICT-N11-001",
            "artifacts": " | ".join(
                [
                    p(CLAUDE_LIBRARY / "lrc_n11_canonical_status_ledger_v1.md"),
                    p(CLAUDE_LIBRARY / "lrc_n11_mechanism_audit_report_v1.md"),
                    p(ROOT / "lrc_n11_canonical_status_ledger_v2.md"),
                    p(ROOT / "lrc_n11_ap_paper_v22.md"),
                ]
            ),
            "scope_mismatch_or_true_conflict": "true conflict",
            "preferred_authority": p(ROOT / "lrc_n11_canonical_status_ledger_v2.md"),
            "resolution": "Treat the March 26 ledger/audit as pre-extraction snapshots and use the March 27 v2 ledger plus v22 paper as the local canonical n=11 authority.",
        },
        {
            "issue": "CONFLICT-N11-002",
            "artifacts": " | ".join(
                [
                    p(ROOT / "lrc_n11_slot_economy_theorem_v1.md"),
                    p(ROOT / "lrc_n11_lemma_wit_analytic_v1.md"),
                    p(CLAUDE_LIBRARY / "lrc_n11_mechanism_audit_report_v1.md"),
                    p(ROOT / "lrc_n11_periodicity_lemma_v1.md"),
                    p(ROOT / "lrc_n11_canonical_status_ledger_v2.md"),
                ]
            ),
            "scope_mismatch_or_true_conflict": "true conflict",
            "preferred_authority": p(ROOT / "lrc_n11_canonical_status_ledger_v2.md"),
            "resolution": "Keep SET/WIT as invalid or superseded historical routes; they no longer control the canonical n=11 proof chain once periodicity/W_ref is accepted.",
        },
        {
            "issue": "CONFLICT-ALLN-001",
            "artifacts": " | ".join(
                [
                    p(CLAUDE_LIBRARY / "lrc_project_review_2026-03-06.md"),
                    p(ROOT / "lrc_proof_v7_8_preprint.md"),
                ]
            ),
            "scope_mismatch_or_true_conflict": "true conflict",
            "preferred_authority": p(ROOT / "lrc_proof_v7_8_preprint.md"),
            "resolution": "Use v7.8 as the direct all-n theorem claim, but mark it packaging-conflicted until the older open-program review and trackers are reconciled or retired.",
        },
        {
            "issue": "CONFLICT-ALLN-002",
            "artifacts": " | ".join(
                [
                    p(ROOT / "lrc_proof_status.md"),
                    p(CLAUDE_LIBRARY / "lrc_prime_power_tier2_closure_v1.md"),
                    p(ROOT / "lrc_proof_v7_8_preprint.md"),
                ]
            ),
            "scope_mismatch_or_true_conflict": "true conflict",
            "preferred_authority": p(ROOT / "lrc_proof_v7_8_preprint.md"),
            "resolution": "Treat the v6.3 status file as stale on prime-power Tier 2 and use the later closure memo plus v7.8 theorem chain for the local branch verdict.",
        },
        {
            "issue": "CONFLICT-ALLN-003",
            "artifacts": " | ".join(
                [
                    p(ROOT / "reports/publication_bar_assessment_cycle_003.md"),
                    p(ROOT / "lrc_proof_v7_8_preprint.md"),
                ]
            ),
            "scope_mismatch_or_true_conflict": "scope mismatch",
            "preferred_authority": p(ROOT / "lrc_proof_v7_8_preprint.md"),
            "resolution": "The publication-bar report evaluates claim-pipeline readiness, not the truth of the theorem manuscript; keep both, but do not merge their verdicts.",
        },
        {
            "issue": "CONFLICT-LIT-001",
            "artifacts": " | ".join(
                [
                    p(ROOT / "reports/citations/CLAIM-LRC-000055/related_work_note.md"),
                    p(ROOT / "lrc_n11_ap_paper_v22.md"),
                    p(ROOT / "lrc_n11_paper_v12.md"),
                ]
            ),
            "scope_mismatch_or_true_conflict": "true conflict",
            "preferred_authority": p(ROOT / "lrc_n11_ap_paper_v22.md"),
            "resolution": "Do not use the cycle-003 citation notes as the sole novelty baseline; refresh the literature screen to include the 2025 survey and the 8/9/10 runner arXiv papers.",
        },
        {
            "issue": "CONFLICT-DUP-001",
            "artifacts": "Top-level Math Ex/Claude Library overlap group (18 shared basenames, see source ledger duplicate groups)",
            "scope_mismatch_or_true_conflict": "true conflict",
            "preferred_authority": str(ROOT),
            "resolution": "Prefer the Math Ex copy when a duplicate basename exists and either matches exactly or has the lower authority rank; treat the Claude Library copy as spillover unless it is the only surviving source.",
        },
        {
            "issue": "CONFLICT-SCOPE-001",
            "artifacts": " | ".join(
                [
                    p(ROOT / "reports/proofs/lrc_proof_pack_2026-03-01/lrc_gap_status_n_all_v1.md"),
                    p(ROOT / "lrc_proof_v7_8_preprint.md"),
                ]
            ),
            "scope_mismatch_or_true_conflict": "scope mismatch",
            "preferred_authority": p(ROOT / "lrc_proof_v7_8_preprint.md"),
            "resolution": "Treat the March 4 gap-status file as a historical phi-target map; the v7.8 preprint changes the primary theorem scope to x_0(E) >= 1 with partial Tier 2 add-ons.",
        },
    ]


def write_conflict_ledger(rows: List[Dict[str, str]]) -> None:
    with CONFLICT_LEDGER.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "issue",
                "artifacts",
                "scope_mismatch_or_true_conflict",
                "preferred_authority",
                "resolution",
            ],
        )
        writer.writeheader()
        writer.writerows(rows)


def markdown_table(headers: Iterable[str], rows: Iterable[Iterable[str]]) -> str:
    headers = list(headers)
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join(["---"] * len(headers)) + " |",
    ]
    for row in rows:
        safe_row = [cell.replace("\n", " ").replace("|", "\\|") for cell in row]
        lines.append("| " + " | ".join(safe_row) + " |")
    return "\n".join(lines)


def write_dossier(
    source_records: List[ArtifactRecord],
    discovery_rows: List[Dict[str, str]],
    conflict_rows: List[Dict[str, str]],
) -> None:
    bucket_counts = Counter(record.bucket for record in source_records)
    scope_counts = Counter(record.scope for record in source_records)
    dup_counts = Counter(record.duplicate_group != "unique" for record in source_records)
    duplicate_classes = Counter()
    for record in source_records:
        if "duplicate_class=" in record.notes:
            match = re.search(r"duplicate_class=([a-z_]+)", record.notes)
            if match:
                duplicate_classes[match.group(1)] += 1

    canonical_rows = [
        (
            "n=11 AP chain",
            "Complete locally",
            "proved/dependency-clean",
            ROOT / "lrc_n11_canonical_status_ledger_v2.md",
            "Static front + periodicity/W_ref; SET/WIT explicitly superseded.",
        ),
        (
            "all-n preprint chain",
            "Full proof claimed locally",
            "proved but packaging-conflicted",
            ROOT / "lrc_proof_v7_8_preprint.md",
            "Direct theorem claim exists, but older packet reviews and some status files still conflict.",
        ),
        (
            "odd prime-power Tier 2",
            "Closed locally",
            "proved but packaging-conflicted",
            CLAUDE_LIBRARY / "lrc_prime_power_tier2_closure_v1.md",
            "Later closure text conflicts with the stale v6.3 status ledger.",
        ),
        (
            "D3 finite-window certification",
            "Certified only",
            "exact certified empirical",
            ROOT / "reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_d3_batch_summary_n7n11_v2.md",
            "Strong exact evidence, but not asymptotic theorem closure.",
        ),
        (
            "multidiv finite-window certification",
            "Certified only",
            "exact certified empirical",
            ROOT / "reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_multidiv_batch_summary_n13_d23_f1234_m100_v1.md",
            "Explicitly tagged as finite-window computation only.",
        ),
        (
            "spillover route memos",
            "Non-canonical",
            "mechanism insight",
            CLAUDE_LIBRARY / "lrc_n11_outer_confinement_results_v1.md",
            "Useful route compression, but not theorem authority.",
        ),
    ]

    discovery_preview = discovery_rows[:8]
    novelty_rows = [
        (row["claim_label"], row["support_level"], row["novelty_verdict"], row["next_action"])
        for row in discovery_rows
    ]
    conflict_preview = [
        (row["issue"], row["scope_mismatch_or_true_conflict"], row["preferred_authority"], row["resolution"])
        for row in conflict_rows
    ]

    lines: List[str] = []
    lines.append("# LRC Master Review and Novelty Audit")
    lines.append("")
    lines.append(f"Generated: 2026-03-30")
    lines.append(f"Corpus roots: `{ROOT}` and `{CLAUDE_LIBRARY}`")
    lines.append("")
    lines.append("Deliverables:")
    lines.append(f"- Source ledger: `{SOURCE_LEDGER}`")
    lines.append(f"- Discovery ledger: `{DISCOVERY_LEDGER}`")
    lines.append(f"- Conflict ledger: `{CONFLICT_LEDGER}`")
    lines.append("")

    lines.append("## 1. Source Map")
    lines.append("")
    lines.append(f"- Total inventoried artifacts: **{len(source_records)}**")
    lines.append(f"- Artifacts with duplicate basenames: **{dup_counts[True]}**")
    lines.append(f"- Duplicate classes: identical copies = **{duplicate_classes.get('identical_copy', 0)}**, divergent forks = **{duplicate_classes.get('divergent_fork', 0)}**")
    lines.append("")
    lines.append("### Bucket counts")
    lines.append("")
    lines.append(
        markdown_table(
            ["Bucket", "Count"],
            [[bucket, str(count)] for bucket, count in sorted(bucket_counts.items())],
        )
    )
    lines.append("")
    lines.append("### Scope counts")
    lines.append("")
    lines.append(
        markdown_table(
            ["Scope", "Count"],
            [[scope, str(count)] for scope, count in sorted(scope_counts.items())],
        )
    )
    lines.append("")
    lines.append("Key reading of the map:")
    lines.append("- `Math Ex` holds the active canonical n=11 chain, the current all-n preprint chain, and the proof-pack / claim-pipeline infrastructure.")
    lines.append("- `Claude Library` holds a larger spillover archive of n=11 route memos plus multidiv and SV56 branch material.")
    lines.append("- Duplicate basenames occur across the two roots; the source ledger resolves these with duplicate groups and preferred copies.")
    lines.append("")

    lines.append("## 2. Canonical Status")
    lines.append("")
    lines.append(
        markdown_table(
            ["Scope", "Verdict", "Support", "Preferred source", "Notes"],
            [
                [
                    scope,
                    verdict,
                    support,
                    str(source),
                    notes,
                ]
                for scope, verdict, support, source, notes in canonical_rows
            ],
        )
    )
    lines.append("")
    lines.append("Canonical reading:")
    lines.append("- The strongest clean local result is the n=11 AP chain in `Math Ex` after the March 27 extraction.")
    lines.append("- The strongest broad claim is the v7.8 all-n preprint, but it sits above older open-status reviews and stale branch ledgers that still need reconciliation.")
    lines.append("- Finite certifications remain evidence packs, not theorem closure, unless promoted by a separate analytic writeup.")
    lines.append("")

    lines.append("## 3. Discovery Catalogue")
    lines.append("")
    lines.append(
        markdown_table(
            ["Claim label", "Scope", "Support", "Novelty verdict", "Source of truth"],
            [
                [
                    row["claim_label"],
                    row["scope"],
                    row["support_level"],
                    row["novelty_verdict"],
                    row["source_of_truth"],
                ]
                for row in discovery_preview
            ],
        )
    )
    lines.append("")
    lines.append("High-signal discoveries by class:")
    lines.append("- Candidate theorem-grade local results: the n=11 AP completion chain, Theorem U, the S2/periodicity closure, the all-n Theorem A claim, dropped-runner targeting, odd prime-power Tier 2, and the proved G4.A Lipschitz lemma.")
    lines.append("- Exact-certified but non-theorem results: the D3 finite-window pack and the multidiv finite-window n=13 pack.")
    lines.append("- Route-level structural insights: the n=11 actual-state theorem summary, outer-confinement ownership signal, and exact-pair carrier split.")
    lines.append("")

    lines.append("## 4. Novelty Screen")
    lines.append("")
    lines.append("Comparison corpus used for March 30, 2026 novelty calls:")
    lines.append("- Classical journal chain already cited locally: Wills 1967, Cusick 1973, Bienia et al. 1998, Bohman-Holzman-Kleitman 2001, Barajas-Serra 2008, Renault 2004, Dubickas 2011, Goncalves-Ramos 2022, Tao 2018.")
    lines.append("- Survey baseline: [Perarnau and Serra, *The Lonely Runner Conjecture turns 60*](https://arxiv.org/abs/2409.20160).")
    lines.append("- Runner-count preprints verified against arXiv: [Rosenfeld, eight runners](https://arxiv.org/abs/2509.14111), [Rosenfeld, nine runners](https://arxiv.org/abs/2512.01912), and [Trakulthongchai, nine and ten runners](https://arxiv.org/abs/2511.22427).")
    lines.append("")
    lines.append(
        markdown_table(
            ["Claim label", "Support", "Novelty verdict", "Action"],
            novelty_rows,
        )
    )
    lines.append("")
    lines.append("Conservative novelty verdicts:")
    lines.append("- No locally theorem-grade claim was downgraded to `known in literature` by this baseline.")
    lines.append("- Several strong local claims remain only `candidate new theorem-grade result` because the local corpus still contains unresolved packaging or authority conflicts.")
    lines.append("- Empirical and route-discovery artifacts stay out of the new-knowledge section unless promoted to dependency-clean theorem text.")
    lines.append("")

    lines.append("## 5. Conflict Register")
    lines.append("")
    lines.append(
        markdown_table(
            ["Issue", "Type", "Preferred authority", "Resolution"],
            conflict_preview,
        )
    )
    lines.append("")
    lines.append("Conflict pattern summary:")
    lines.append("- The sharpest true conflicts are status conflicts: n=11 incomplete vs complete, all-n open vs full-proof claimed, and prime-power Tier 2 open vs closed.")
    lines.append("- Several apparent conflicts are really scope conflicts: theorem truth vs governance readiness, or phi-target historical maps vs x_0>=1 theorem claims.")
    lines.append("- Duplicate-file conflicts are manageable because the active workspace usually contains either the preferred copy or the later canonical ledger.")
    lines.append("")

    lines.append("## 6. Promotion Queue")
    lines.append("")
    lines.append("### Publication-ready locally")
    lines.append("- n=11 AP chain: keep `lrc_n11_canonical_status_ledger_v2.md` and `lrc_n11_ap_paper_v22.md` as the canonical local package.")
    lines.append("- Branch theorem candidates worth external review: dropped-runner targeting, odd prime-power Tier 2 closure, and the proved G4.A Lipschitz lemma.")
    lines.append("")
    lines.append("### High-value but unresolved")
    lines.append("- v7.8 all-n theorem claim: reconcile against the March 6 project review, stale gap/status files, and publication/governance reports.")
    lines.append("- Gap-4 complementarity run cap (`G4.B`) and composite multidiv asymptotic closure remain open targets despite strong certification.")
    lines.append("- Spillover n=11 route memos (outer confinement, exact-pair, DRWT/CPOT plans) should remain quarantined unless they re-enter the active canonical chain.")
    lines.append("")
    lines.append("### Demote or archive")
    lines.append("- Dynamic SET and WIT closure routes for n=11 should remain archived or clearly marked superseded.")
    lines.append("- `lrc_proof_status.md` should be treated as a stale v6.3-era status file, not the current branch authority.")
    lines.append("- Cycle-003 citation notes should not be reused as the current novelty baseline without refresh.")
    lines.append("- Claude Library duplicate copies should be treated as spillover unless the source ledger marks them as preferred.")
    lines.append("")

    DOSSIER.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    source_records = build_source_ledger()
    discovery_rows = build_discovery_rows()
    conflict_rows = build_conflict_rows()

    write_source_ledger(source_records)
    write_discovery_ledger(discovery_rows)
    write_conflict_ledger(conflict_rows)
    write_dossier(source_records, discovery_rows, conflict_rows)

    print(f"Wrote {SOURCE_LEDGER}")
    print(f"Wrote {DISCOVERY_LEDGER}")
    print(f"Wrote {CONFLICT_LEDGER}")
    print(f"Wrote {DOSSIER}")


if __name__ == "__main__":
    main()
