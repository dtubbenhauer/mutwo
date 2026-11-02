#!/bin/sh
# Portable CI entrypoint after installing the pinned Lean/mathlib dependencies.
# verify.py builds both targets and fails on any axiom/interface/provenance drift.
set -eu
cd "$(dirname "$0")/.."
exec python3 scripts/verify.py
