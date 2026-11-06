/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import OrlikSolomonBook

/-!
# The executable that renders the book

`lake exe book --output _out/book` writes the site to `_out/book/html-multi`. It exits with an error
if rendering reports an error or the completeness check fails.
-/

open Verso.Genre.Manual OrlikSolomonBook

/-- Renders the book and checks that it covers the blueprint. -/
def main (args : List String) : IO UInt32 :=
  manualMain (%doc OrlikSolomonBook) (options := args)
    (config := { sourceLink := some repositoryUrl, issueLink := some s!"{repositoryUrl}/issues" })
    (extraSteps := [checkCompleteness])
