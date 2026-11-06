#!/usr/bin/env bash
# Prepare a git worktree for building: share the dependency builds of the main checkout
# through a symlink, so that worktrees do not each download a copy of Mathlib.
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
main="$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")"

if [ "$root" = "$main" ]; then
  echo "This is the main checkout: nothing to do." >&2
  exit 0
fi

if [ ! -d "$main/.lake/packages" ]; then
  echo "Dependencies missing: run 'lake exe cache get' in $main first." >&2
  exit 1
fi

mkdir -p "$root/.lake"
ln -sfn "$main/.lake/packages" "$root/.lake/packages"
echo "Linked $root/.lake/packages -> $main/.lake/packages"
