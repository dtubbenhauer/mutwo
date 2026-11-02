#!/bin/sh
# Reproduce the pinned Lean build and its theorem/interface audits.
set -eu
cd "$(dirname "$0")"
exec python3 scripts/verify.py
