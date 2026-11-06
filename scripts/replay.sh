#!/usr/bin/env bash
# Replays the library through the kernel with `leanchecker`, proofs included. A declaration that
# reached the `.olean` files without the kernel accepting it fails here. The audit only reads what
# the build recorded, so it would not notice one. Mathlib is not replayed. CI runs this after
# `scripts/check.sh`.
#
# Each module gets its own process, because on Lean v4.36.0-rc2 `leanchecker` crashes when one
# process replays two modules. Its argument is a prefix, so a module that has submodules cannot be
# replayed alone. The root has them, and the audit requires that it declares nothing.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

lake build --wfail OrlikSolomon

modules=()
while IFS= read -r file; do
  if [ -e "${file%.lean}" ]; then
    echo "replay: error: $file has submodules, so leanchecker cannot replay it alone" >&2
    exit 1
  fi
  module="${file%.lean}"
  modules+=("${module//\//.}")
done < <(find OrlikSolomon -name '*.lean' | sort)

# Listing the modules from their sources also skips any stale `.olean` restored by the CI cache.
printf '%s\n' "${modules[@]}" | lake env xargs -n 1 -P 4 leanchecker
echo "replay: the kernel accepted all ${#modules[@]} modules under OrlikSolomon/"
