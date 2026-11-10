/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import Lean.Data.Json

/-!
# Reading the blueprint

The nodes of the blueprint are its theorem-like environments, each named by a `\label`. This
module extracts them from the TeX source, so that the book can check its coverage against the
blueprint itself rather than against a list that could drift from it.

The parser is deliberately strict. A `\label` that is attached neither to a theorem-like
environment, a sectioning command nor a tagged display is an error, and so is a theorem-like
environment without a `\label`. So is a label used by two nodes, even in different files, because
a copied label would otherwise add a node with a new statement and no new coverage obligation.
This way no node can drop out of the completeness check unnoticed.
-/

open Lean

namespace OrlikSolomonBook.Blueprint

/-- A node of the blueprint: a theorem-like environment together with its `\label`. -/
structure Node where
  /-- The `\label`, such as `lem:gm`. -/
  label : String
  /-- The name of the environment, capitalized, such as `Lemma`. -/
  kind : String
  /-- The optional argument of the environment, with TeX accents and dashes resolved. -/
  title : String
  /-- The blueprint file that contains the node, such as `de_rham_instance_blueprint.tex`. -/
  source : String := ""
deriving Repr, Inhabited, BEq, ToJson, FromJson

/-- The environments that count as nodes of the blueprint. -/
private def theoremLikeEnvs : List String :=
  ["definition", "lemma", "theorem", "proposition", "corollary", "remark"]

/-- Sectioning commands, whose labels name parts of the document rather than nodes. -/
private def sectioningCommands : List String :=
  ["\\part", "\\section", "\\subsection", "\\subsubsection", "\\paragraph"]

/-- Removes a TeX comment from one line, respecting the escape `\%`. -/
private def stripLineComment (line : String) : String :=
  let rec go : List Char → List Char
    | [] => []
    | '\\' :: c :: rest => '\\' :: c :: go rest
    | '%' :: _ => []
    | c :: rest => c :: go rest
  String.ofList (go line.toList)

/-- Resolves the TeX that occurs in the titles of nodes. -/
private def cleanTitle (title : String) : String :=
  (title.replace "---" "—").replace "--" "–" |>.replace "\\'e" "é" |>.replace "\\\"u" "ü"

/-- Capitalizes the first letter of an environment name. -/
private def capitalize (s : String) : String :=
  match s.toList with
  | [] => ""
  | c :: rest => String.ofList (c.toUpper :: rest)

/-- The text following the last `\begin{` in `before`, which precedes a `\label`. -/
private def afterLastBegin? (before : String) : Option String :=
  match before.splitOn "\\begin{" with
  | [] | [_] => none
  | parts => parts.getLast?

/-- A tag immediately before a label must belong to the current or just-closed display.
This recognizes display metadata by its TeX context, never by the label's spelling. -/
private def isTaggedDisplayLabel (before : String) : Bool := Id.run do
  let parts := before.trimAscii.copy.splitOn "\\tag{"
  if parts.length < 2 then return false
  let arg := parts.getLast?.getD ""
  if !arg.endsWith "}" then return false
  let tag := arg.dropEnd 1 |>.copy
  if tag.isEmpty || tag.toList.any (fun c => c == '{' || c == '}') then return false
  let beforeTag := "\\tag{".intercalate (parts.take (parts.length - 1))
  let displays := beforeTag.splitOn "\\["
  if displays.length < 2 then return false
  match (displays.getLast?.getD "").splitOn "\\]" with
  | [_] => return true
  | [_, afterClose] => return afterClose.trimAscii.isEmpty
  | _ => return false

/--
Classifies the text that precedes a `\label`. Returns `some (some node)` if the label is on a
theorem-like environment, `some none` for section or tagged-display metadata, and `none` otherwise.
-/
private def classify (label before : String) : Option (Option Node) := do
  -- A section label may follow its heading on a new line, including after blank lines.
  -- Trim only whitespace: intervening prose must still make the label an error.
  let lastLine := ((before.trimAscii.copy.splitOn "\n").getLast?.getD "").trimAscii.copy
  if sectioningCommands.any (lastLine.startsWith ·) then
    return none
  if isTaggedDisplayLabel before then
    return none
  let tail ← afterLastBegin? before
  match tail.splitOn "}" with
  | [] => failure
  | env :: rest =>
    guard (env ∈ theoremLikeEnvs)
    let arg := ("}".intercalate rest).trimAscii.copy
    if arg.isEmpty then
      return some { label, kind := capitalize env, title := "" }
    guard (arg.startsWith "[" && arg.endsWith "]")
    let title := (arg.drop 1).dropEnd 1 |>.copy
    return some { label, kind := capitalize env, title := cleanTitle title }

/-- The name of the `\label` at the start of `chunk`, and the text following it. -/
private def splitLabel (chunk : String) : String × String :=
  match chunk.splitOn "}" with
  | [] => ("", "")
  | label :: rest => (label, "}".intercalate rest)

/-- Extracts the nodes of a TeX source, in the order they occur. -/
def parseNodes (src : String) : Except String (Array Node) := do
  let src := "\n".intercalate ((src.splitOn "\n").map stripLineComment)
  let mut nodes : Array Node := #[]
  let mut before := ""
  let mut first := true
  for chunk in src.splitOn "\\label{" do
    if first then
      before := chunk
      first := false
      continue
    let (label, after) := splitLabel chunk
    match classify label before with
    | none =>
      throw s!"\\label\{{label}} is on neither a theorem-like environment, a section nor a tagged display"
    | some none => pure ()
    | some (some node) => nodes := nodes.push node
    before := after
  let envCount := theoremLikeEnvs.foldl (init := 0) fun n env =>
    n + ((src.splitOn s!"\\begin\{{env}}").length - 1)
  unless envCount == nodes.size do
    throw s!"found {envCount} theorem-like environments but {nodes.size} labelled nodes"
  return nodes

/-- The labels used by more than one node, each listed once. -/
def duplicateLabels (nodes : Array Node) : List String :=
  let labels := (nodes.map (·.label)).toList
  (labels.filter (labels.count · > 1)).eraseDups

/-- The directory of the blueprint, relative to the root of the repository. -/
def directory : System.FilePath := "blueprint"

/--
Reads the nodes of every TeX file in `blueprint/`, each recording its file, and fails if two of them
have the same label. The working directory must be the root of the repository, which it is for
`lake build` and `lake exe book`.
-/
def readNodes : IO (Array Node) := do
  unless ← directory.isDir do
    throw <| .userError s!"no directory '{directory}': run from the root of the repository"
  let files := (← directory.readDir).map (·.path) |>.filter (·.extension == some "tex")
  let files := files.qsort (·.toString < ·.toString)
  if files.isEmpty then
    throw <| .userError s!"no TeX files in '{directory}'"
  let mut nodes := #[]
  for file in files do
    match parseNodes (← IO.FS.readFile file) with
    | .ok found =>
      let source := file.fileName.getD file.toString
      nodes := nodes ++ found.map ({ · with source })
    | .error e => throw <| .userError s!"{file}: {e}"
  match duplicateLabels nodes with
  | [] => return nodes
  | labels => throw <| .userError s!"the blueprint uses these labels more than once: {labels}"

end OrlikSolomonBook.Blueprint
