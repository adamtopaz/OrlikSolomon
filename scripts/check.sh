#!/usr/bin/env bash
# The checks that keep `main` trustworthy. CI runs this same script.
#
# `lake build` only compiles what the root module imports, so the audit also confirms that the
# root imports everything. See `scripts/Audit.lean` for what it checks.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

lake build --wfail OrlikSolomon audit
lake exe audit
