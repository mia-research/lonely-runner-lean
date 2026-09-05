# ride_v40_lib/rungs.py — benchmark rung loader
# v1.0 — 2026-04-15
#
# Four rungs, in order of difficulty:
#   Rung 0 (synthetic): a target generated from a known θ in the same
#     space being tested. Every θ-space should solve its own construction;
#     this catches bugs in constructor / mutation operators.
#   Rung 1 (text-slice): v24's 3-page text slice (~17k cities), fast iter.
#   Rung 2 (pdf-page): v24's raw first-PDF-page (~565k cities).
#   Rung 3 (lrc-pdf): the v28–v30 falsification target (~895k cities).
#     Breaking the 87% wall here is the decisive experiment.
#
# Inputs come from /Users/trentpalelei/Desktop/Math Ex/ — we locate them
# by glob relative to that directory.

from __future__ import annotations

import random
import sys
from array import array
from dataclasses import dataclass
from pathlib import Path

import numpy as np

# Allow "import ride_v13_..." by making Math Ex/ importable.
_MATH_EX = Path(__file__).resolve().parent.parent
if str(_MATH_EX) not in sys.path:
    sys.path.insert(0, str(_MATH_EX))

from ride_v13_canterbury_recipe_bench import build_perm_target_to_source  # noqa: E402
from ride_v18_cycle_rsn import materialise_source_and_target  # noqa: E402

from .core import Perm


@dataclass
class Rung:
    name: str
    description: str
    source: Perm          # as int64 array of digits 0..9
    target: Perm          # as int64 array of digits 0..9
    target_perm: Perm     # π such that target[i] = source[π[i]] (int64)
    n: int                # == len(target_perm)
    raw_path: Path | None # None for synthetic


# --------------------------------------------------------------------------
# Rung 0 — synthetic (space-specific; built by main driver)
# --------------------------------------------------------------------------

def build_synthetic_rung(space_name: str, theta_perm: Perm, n: int) -> Rung:
    """
    Construct a synthetic target from a known permutation. source = [0..n),
    target = theta_perm applied to source. Used for self-consistency check:
    the space that generated theta_perm should be able to find it.
    """
    source = np.arange(n, dtype=np.int64)
    target = source[theta_perm]  # == theta_perm since source is identity
    return Rung(
        name=f"synthetic_{space_name}",
        description=f"Identity source, target = σ applied, n={n}",
        source=source,
        target=target,
        target_perm=theta_perm.astype(np.int64),
        n=n,
        raw_path=None,
    )


# --------------------------------------------------------------------------
# Rungs 1-3 — real files via v18's materialise_source_and_target
# --------------------------------------------------------------------------

def _load_real_rung(name: str, description: str, raw: bytes,
                    slice_len: int | None = None) -> Rung:
    source_list, target_list, _params, _l1 = materialise_source_and_target(raw)
    if slice_len is not None:
        # Slice to size — both source and target get same slice; permutation
        # inferred fresh from sliced bytes so it's a valid permutation of
        # the sliced multiset.
        source_list = source_list[:slice_len]
        target_list = target_list[:slice_len]
    source = np.array(source_list, dtype=np.int64)
    target = np.array(target_list, dtype=np.int64)
    # build_perm_target_to_source expects bytearrays of digit values.
    perm_arr = build_perm_target_to_source(bytearray(target_list), bytearray(source_list))
    target_perm = np.frombuffer(perm_arr, dtype=np.uint32).astype(np.int64)
    return Rung(
        name=name,
        description=description,
        source=source,
        target=target,
        target_perm=target_perm,
        n=len(target_perm),
        raw_path=None,
    )


def _find_file(*candidates: str) -> Path | None:
    for c in candidates:
        p = Path(c)
        if p.exists():
            return p
    return None


def load_text_slice_rung(slice_len: int = 20_000) -> Rung | None:
    """Rung 1: 3-page text slice (~17k digits). v24 test bed."""
    # Try Canterbury alice29.txt first, then any .txt in Math Ex.
    path = _find_file(
        str(_MATH_EX / "alice29.txt"),
        str(_MATH_EX / "plrabn12.txt"),
        str(_MATH_EX / "sample.txt"),
    )
    if path is None:
        # last-ditch: any .txt under Math Ex
        for p in _MATH_EX.glob("*.txt"):
            path = p
            break
    if path is None:
        return None
    raw = path.read_bytes()
    if len(raw) > slice_len // 3:
        raw = raw[: max(slice_len // 3, 5000)]
    rung = _load_real_rung(
        name="text_slice",
        description=f"Text slice from {path.name} (~{slice_len} digits)",
        raw=raw,
        slice_len=slice_len,
    )
    rung.raw_path = path
    return rung


def load_pdf_page_rung() -> Rung | None:
    """Rung 2: raw first PDF page (~565k digits). v24 binary bed."""
    path = _find_file(
        str(_MATH_EX / "eleven_lonely_runners.pdf"),
        str(_MATH_EX / "eleven_lonely_runners_v31.pdf"),
    )
    if path is None:
        # any pdf under Math Ex
        for p in _MATH_EX.glob("*.pdf"):
            path = p
            break
    if path is None:
        return None
    raw = path.read_bytes()
    # Slice to roughly first-page size — 50KB of raw bytes
    slice_bytes = raw[: 50_000]
    rung = _load_real_rung(
        name="pdf_page",
        description=f"First ~50KB of {path.name}",
        raw=slice_bytes,
        slice_len=None,
    )
    rung.raw_path = path
    return rung


def load_lrc_pdf_rung() -> Rung | None:
    """Rung 3: LRC PDF full — the v28–v30 target. ~895k digits."""
    path = _find_file(
        str(_MATH_EX / "eleven_lonely_runners.pdf"),
    )
    if path is None:
        # most recent PDF
        pdfs = sorted(_MATH_EX.glob("eleven_lonely_runners*.pdf"),
                      key=lambda p: p.stat().st_mtime, reverse=True)
        if not pdfs:
            return None
        path = pdfs[0]
    raw = path.read_bytes()
    rung = _load_real_rung(
        name="lrc_pdf",
        description=f"Full LRC PDF {path.name}",
        raw=raw,
        slice_len=None,
    )
    rung.raw_path = path
    return rung


def load_all_real_rungs() -> list[Rung]:
    rungs = []
    for loader in (load_text_slice_rung, load_pdf_page_rung, load_lrc_pdf_rung):
        try:
            r = loader()
            if r is not None:
                rungs.append(r)
        except Exception as e:
            print(f"[rungs] skipped {loader.__name__}: {e}", file=sys.stderr)
    return rungs
