#!/usr/bin/env bash
set -euo pipefail

scripts/check_solution_statements.py
exec lake -R -Kwarn.sorry=false build Solutions/**/*.lean
