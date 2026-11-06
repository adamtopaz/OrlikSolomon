#!/usr/bin/env bash
# Replays the library through the kernel, proofs included, and fails unless the kernel accepts every
# module of the library. A declaration that reached the `.olean` files without the kernel accepting
# it fails here, and `scripts/check.sh` would not notice one. Mathlib is not replayed. CI runs this
# after `scripts/check.sh`. See `scripts/Audit.lean` for how it works.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

lake build --wfail OrlikSolomon audit
lake exe audit --replay
