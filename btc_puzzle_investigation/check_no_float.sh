#!/usr/bin/env bash
# No-float-in-signal-path guard (CLAUDE.md). Thin wrapper over the AST checker.
# Usage: bash check_no_float.sh <file.py> [file.py ...]   (defaults to exact-era set)
exec python3 "$(dirname "$0")/check_no_float.py" "$@"
