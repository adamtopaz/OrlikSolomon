/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import VersoManual
import OrlikSolomonBook.Blueprint

/-!
# Tying the book to the code

This module defines what makes the book more than prose:

* The `node` directive presents one node of the blueprint. It names the node's `\label` and the
  Lean declarations that formalize it. The build **fails** if a name does not resolve, or if a
  declaration depends on `sorryAx` or on any axiom other than `propext`, `Classical.choice` and
  `Quot.sound`. A node that names no declaration renders as planned, and there is no other way to
  obtain the status "formalized". Those are the only checks: the directive cannot tell whether the
  declarations cover the node's statement, and it accepts any proved declaration. That coverage,
  and all prose, are the responsibility of review, and the book says so to its readers.
* The `bp` role links to a node by its label, and shows its status.
* The `statusOverview` and `statusSummary` commands render the status of all nodes.
* `checkCompleteness` compares the labels covered by the book with those of the blueprint.

Book modules are not Lean `module`s, unlike those of the library, and that is deliberate. A plain
`import` of a library module gives the private level of its data. With `module`, a batch build would
not see the declaration ranges and docstrings that the book renders.
-/

open Lean Elab
open Verso Doc Elab ArgParse Genre Manual
open Verso.Output Html
open Verso.Doc.Html (HtmlT)

namespace OrlikSolomonBook

/-- The repository whose source the book links to. -/
def repositoryUrl : String := "https://github.com/adamtopaz/OrlikSolomon"

/-- The only axioms a declaration may depend on and still be presented as formalized. -/
def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- The domain of the cross-reference database that records the nodes of the book. -/
def nodeDomain : Name := `OrlikSolomonBook.node

/-- The status of a node. Only the `node` directive can determine it. -/
inductive Status where
  /-- In scope, with no declarations yet. -/
  | planned
  /-- Out of scope for now: see "Scope" in `docs/ARCHITECTURE.md`. -/
  | deferred
  /-- Some declarations are checked, but part of the node is still missing. -/
  | partly
  /-- Every named declaration resolved and depends only on the standard axioms, and the directive
  does not say that part of the node is missing. Review, not the build, judges that they cover it. -/
  | formalized
deriving Repr, BEq, ToJson, FromJson

/-- The word used for a status in overview tables and in CSS classes. -/
def Status.word : Status → String
  | .planned => "planned"
  | .deferred => "deferred"
  | .partly => "partial"
  | .formalized => "formalized"

/-- The location of a declaration that has passed the checks of the `node` directive. -/
structure DeclData where
  /-- The full name of the declaration. -/
  name : Name
  /-- The module that defines it. -/
  module : Name
  /-- The line range of its source, when Lean records one. -/
  lines : Option (Nat × Nat)
deriving Repr, ToJson, FromJson

/-- What the `node` directive records about a node. -/
structure NodeData where
  /-- The position of the node in the blueprint, used to order the overview. -/
  index : Nat
  /-- The node as the blueprint presents it. -/
  node : Blueprint.Node
  /-- The status, as determined by the directive. -/
  status : Status
  /-- The declarations named by the directive. -/
  decls : Array DeclData
  /-- For a partly formalized node, what is still missing. -/
  remaining : Option String
deriving Repr, ToJson, FromJson

/-- The URL of a line range of a library module, at a given commit. -/
def sourceUrl (commit : String) (module : Name) (lines : Option (Nat × Nat)) : String :=
  let path := "/".intercalate (module.components.map (·.toString))
  let anchor := match lines with
    | .some (first, last) => s!"#L{first}-L{last}"
    | .none => ""
  s!"{repositoryUrl}/blob/{commit}/{path}.lean{anchor}"

/-- The key under which the traversal stores the commit being built. -/
private def commitKey : Name := `OrlikSolomonBook.commit

/-- The commit checked out in the working directory, which is the one being built. -/
private def currentCommit : IO (Except String String) := do
  try
    let out ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
    if out.exitCode == 0 then
      return .ok out.stdout.trimAscii.copy
    return .error s!"'git rev-parse HEAD' failed: {out.stderr}"
  catch e =>
    return .error s!"could not run git: {e}"

/-- Records the commit being built in the traversal state, once. -/
private def saveCommit : ReaderT TraverseContext (StateT TraverseState (BuildLogT IO)) Unit := do
  if ((← get).get? commitKey : Option (Except String String)).isNone then
    match ← currentCommit with
    | .ok commit => modify (·.set commitKey commit)
    | .error e => reportError s!"Cannot link to the source: {e}"

/-- The commit recorded by `saveCommit`. -/
private def savedCommit? (state : TraverseState) : Option String :=
  (state.get? commitKey : Option (Except String String)).bind (·.toOption)

/-- The styles of nodes and of the status overview. -/
def nodeCss : String := r#"
.bp-node {
  border-left: 0.25rem solid var(--bp-accent);
  background: var(--bp-background);
  margin: 1.25rem 0;
  padding: 0.5rem 0.75rem;
}
.bp-node.bp-planned { --bp-accent: #9a6700; --bp-background: #fff8e5; border-left-style: dashed; }
.bp-node.bp-deferred { --bp-accent: #6e7781; --bp-background: #f6f8fa; border-left-style: dotted; }
.bp-node.bp-partial { --bp-accent: #0969da; --bp-background: #eef6ff; }
.bp-node.bp-formalized { --bp-accent: #1a7f37; --bp-background: #eefbf1; }
.bp-head, .bp-badge, .bp-overview-table { font-family: var(--verso-text-font-family); }
.bp-head {
  display: flex;
  flex-wrap: wrap;
  align-items: baseline;
  gap: 0.25rem 0.75rem;
}
.bp-head .bp-name { font-weight: bold; }
.bp-head .bp-label { font-size: 0.85em; }
.bp-badge {
  border: 1px solid currentColor;
  border-radius: 0.75rem;
  font-size: 0.8em;
  padding: 0 0.5rem;
  white-space: nowrap;
}
.bp-badge.bp-planned { color: #7d4e00; }
.bp-badge.bp-deferred { color: #57606a; }
.bp-badge.bp-partial { color: #0550ae; }
.bp-badge.bp-formalized { color: #116329; }
.bp-remaining { font-style: italic; }
.bp-summary { font-weight: bold; }
a + .bp-badge, .bp-overview .bp-badge { font-size: 0.7em; }
.bp-source { font-size: 0.85em; margin: 0.25rem 0; }
.bp-overview-table { border-collapse: collapse; width: 100%; }
.bp-overview-table th, .bp-overview-table td {
  border-bottom: 1px solid #d0d7de;
  padding: 0.25rem 0.5rem;
  text-align: left;
  vertical-align: top;
}
.bp-overview-table td:last-child code { overflow-wrap: anywhere; }
"#

/-- Escaped text, as an HTML fragment. -/
private def txt (s : String) : Html := .text s

/-- The badge that states the status of a node. This text is the book's claim about the node. -/
def statusBadge (data : NodeData) : Html :=
  let text := match data.status with
    | .planned => "Planned: not yet formalized"
    | .deferred => "Deferred: out of scope for now"
    | .partly => "Partly formalized"
    | .formalized => "Formalized: declarations checked, coverage reviewed"
  html%{<span class={s!"bp-badge bp-{data.status.word}"}>{txt text}</span>}

/-- The title of a node, as "Lemma (Title)". -/
def nodeName (node : Blueprint.Node) : String :=
  if node.title.isEmpty then node.kind else s!"{node.kind} ({node.title})"

/-
A node of the blueprint. Its contents are the prose of the book, followed by one `Block.formal` for
each declaration. The data is passed as a JSON string because that is easy to quote.
-/
block_extension Block.node (json : String) where
  data := (Json.parse json).toOption.getD .null
  extraCss := {⟨nodeCss⟩}
  traverse id data _ := do
    saveCommit
    let .ok (node : NodeData) := fromJson? data
      | reportError "Failed to deserialize a blueprint node"; return none
    let path := (← read).path
    let _ ← externalTag id path node.node.label
    modify fun st => st
      |>.saveDomainObject nodeDomain node.node.label id
      |>.saveDomainObjectData nodeDomain node.node.label data
    return none
  localContentItem _ data _ := do
    let node : NodeData ← fromJson? data
    let name := nodeName node.node
    return #[(name, txt name)]
  toTeX := none
  toHtml := some fun _ goB id data contents => do
    let .ok (node : NodeData) := fromJson? data
      | reportError "Failed to deserialize a blueprint node"; return .empty
    let state ← HtmlT.state
    let remaining : Html := match node.remaining with
      | .some r => html%{<p class="bp-remaining">{txt s!"Still missing: {r}."}</p>}
      | .none => .empty
    return html%{
      <div class={s!"bp-node bp-{node.status.word}"} {... state.htmlId id}>
        <div class="bp-head">
          <span class="bp-name">{txt (nodeName node.node)}</span>
          <code class="bp-label">{txt node.node.label}</code>
          {statusBadge node}
          {permalink id state}
        </div>
        {← contents.mapM goB}
        {remaining}
      </div>
    }

/-
The formal statement of a declaration inside a node, with a link to its source at the commit being
built. Its contents render the statement itself.
-/
block_extension Block.formal (json : String) where
  data := (Json.parse json).toOption.getD .null
  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some fun _ goB _ data contents => do
    let .ok (decl : DeclData) := fromJson? data
      | reportError "Failed to deserialize a declaration of a blueprint node"; return .empty
    let state ← HtmlT.state
    let source : Html :=
      if decl.module.getRoot == `OrlikSolomon then
        match savedCommit? state with
        | .some commit =>
          let short := (commit.take 8).copy
          html%{
            <a href={sourceUrl commit decl.module decl.lines}>
              {txt s!"Source at commit {short}"}
            </a>
          }
        | .none => .empty
      else
        txt "This module is not part of this repository."
    return html%{
      <div class="bp-formal">
        {← contents.mapM goB}
        <p class="bp-source">
          {txt "In "}<code>{txt decl.module.toString}</code>{txt ". "}{source}
        </p>
      </div>
    }

/-- The arguments of the `node` directive. -/
structure NodeConfig where
  /-- The `\label` of the node in the blueprint. -/
  label : String
  /-- The Lean declarations that formalize the node. -/
  decls : List Ident
  /-- The node is out of scope for now, rather than planned. -/
  deferred : Bool
  /-- What is still missing, if the declarations do not cover the whole node. -/
  remaining : Option String

instance : FromArgs NodeConfig DocElabM where
  fromArgs :=
    NodeConfig.mk <$>
      .positional `label .string <*>
      .many (.named `decl .ident false) <*>
      .flag `deferred false <*>
      .named `remaining .string true

/--
Checks that a declaration may be presented as formalized, and records where it lives. This is the
guarantee that the text cannot drift from the code.
-/
def checkDecl (x : Ident) : DocElabM (Name × DeclData) := withRef x do
  -- Resolving here rather than in the argument parser matters: `ArgParse.many` treats a failure as
  -- the end of the list, which would turn an unknown name into a misleading error about arguments.
  let (_, name) ← ValDesc.documentableName.get (.name x)
  let env ← getEnv
  let some idx := env.getModuleIdxFor? name
    | throwErrorAt x m!"'{name}' is declared in the book itself, so it formalizes nothing."
  let module := env.header.moduleNames[idx.toNat]!
  if module.getRoot == `OrlikSolomonBook then
    throwErrorAt x m!"'{name}' is declared in the book itself, so it formalizes nothing."
  let axioms ← collectAxioms name
  if axioms.contains ``sorryAx then
    throwErrorAt x m!"'{name}' depends on `sorryAx`, so it cannot be presented as formalized. \
      Finish the proof, or remove the name from this node."
  let others := axioms.filter (!standardAxioms.contains ·)
  unless others.isEmpty do
    throwErrorAt x m!"'{name}' depends on the nonstandard axioms {others}, so it cannot be \
      presented as formalized."
  let lines := (← findDeclarationRanges? name).map fun r =>
    (r.range.pos.line, r.range.endPos.line)
  return (name, { name, module, lines })

/--
Runs `act`, dropping Verso's warnings that a declaration has no docstring. Verso has no option for
this: `verso.docstring.allowMissing` only chooses between a warning and an error. Whether the
library documents something is for the library's own checks, and Mathlib declarations often do not.
Every other message is kept.
-/
private def withoutMissingDocWarnings {α : Type} (act : DocElabM α) : DocElabM α := do
  let saved ← Core.getMessageLog
  Core.setMessageLog {}
  try
    act
  finally
    let mut log := saved
    for msg in (← Core.getMessageLog).toList do
      let text ← msg.data.toString
      unless msg.severity == .warning && (text.splitOn "is not documented.").length > 1 do
        log := log.add msg
    Core.setMessageLog log

/--
The block that renders the statement of a declaration. Its docstring is included, unless it uses
Markdown that Verso cannot render. A docstring is written for the library and its readers, so it
must never be able to break the book.
-/
def statementBlock (x : Ident) (name : Name) : DocElabM Term :=
  -- Verso's heuristic elaboration of code in docstrings would log noise for things like blueprint
  -- labels, and the book's own prose is the place for elaborated Lean.
  withoutMissingDocWarnings <| withOptions (verso.docstring.elabMarkdown.set · false) do
    try
      docstring ⟨(x, name), true, false, true, none⟩
    catch e =>
      logWarningAt x m!"Rendering '{name}' without its docstring: {e.toMessageData}"
      let declType ← Block.Docstring.DeclType.ofName name (hideFields := true)
        (hideStructureConstructor := true)
      let signature ← Signature.forName name
      ``(Verso.Doc.Block.other
          (Verso.Genre.Manual.Block.docstring $(quote name) $(quote declType) $(quote signature)
            none #[])
          #[])

/-- Finds a node of the blueprint by its label, with its position. -/
def findNode (label : String) : DocElabM (Nat × Blueprint.Node) := do
  let nodes ← Blueprint.readNodes
  match nodes.findIdx? (·.label == label) with
  | .some i => return (i, nodes[i]!)
  | .none => throwError m!"The blueprint has no node with the label '{label}'."

/--
Presents a node of the blueprint:

```
:::node "lem:gm" (decl := OrlikSolomon.foo) (decl := OrlikSolomon.bar)
Prose about the lemma.
:::
```

With no `decl`, the node renders as planned, or as deferred with the flag `+deferred`. If the named
declarations cover only part of the node, say what is missing with `(remaining := "...")`.
-/
@[directive]
def node : DirectiveExpanderOf NodeConfig
  | { label, decls, deferred, remaining }, contents => do
    let (index, bpNode) ← findNode label
    let status : Status ←
      match decls, deferred, remaining with
      | [], false, .none => pure .planned
      | [], true, .none => pure .deferred
      | [], _, .some _ =>
        throwError "`remaining` describes a partly formalized node, but this node names no \
          declaration."
      | _ :: _, true, _ => throwError "A deferred node cannot name declarations."
      | _ :: _, false, .none => pure .formalized
      | _ :: _, false, .some _ => pure .partly
    let checked ← decls.toArray.mapM checkDecl
    let body ← contents.mapM elabBlock
    let formal ← (decls.toArray.zip checked).mapM fun (x, name, decl) => do
      let statement ← statementBlock x name
      ``(Verso.Doc.Block.other
          (Block.formal $(quote (toJson decl).compress))
          #[$statement])
    let data : NodeData :=
      { index, node := bpNode, status, decls := checked.map (·.2), remaining }
    ``(Verso.Doc.Block.other
        (Block.node $(quote (toJson data).compress))
        #[$(body ++ formal),*])

/-- The nodes covered by the book, ordered as in the blueprint. -/
def coveredNodes (state : TraverseState) : Array NodeData := Id.run do
  let some domain := state.domains.get? nodeDomain | return #[]
  let nodes := domain.objects.toArray.filterMap fun (_, obj) =>
    (fromJson? obj.data : Except String NodeData).toOption
  return nodes.qsort (·.index < ·.index)

/-- Counts the nodes that have a given status. -/
def countStatus (nodes : Array NodeData) (status : Status) : Nat :=
  (nodes.filter (·.status == status)).size

/-- A sentence that summarizes the status of the nodes. -/
def summarizeStatus (nodes : Array NodeData) : String :=
  let inScope := nodes.size - countStatus nodes .deferred
  s!"Status of the {inScope} blueprint nodes in scope: {countStatus nodes .formalized} formalized, \
    {countStatus nodes .partly} partly formalized, {countStatus nodes .planned} planned. \
    Deferred nodes, out of scope for now: {countStatus nodes .deferred}."

/--
The name under which the book counts the nodes of a blueprint file. A file with no name here is
listed under its file name, so that the nodes of a new blueprint are never added to another's count.
-/
def blueprintName (source : String) : String :=
  match source with
  | "arrangement_cohomology_lean_blueprint.tex" => "Main theorem"
  | "de_rham_instance_blueprint.tex" => "De Rham instance"
  | other => other

/-- The nodes of each blueprint file, in the order in which the files first occur. -/
def nodesByBlueprint (nodes : Array NodeData) : List (String × Array NodeData) :=
  (nodes.toList.map (·.node.source)).eraseDups.map fun source =>
    (source, nodes.filter (·.node.source == source))

/-- One sentence for each blueprint file, under its name, so that no count mixes two of them. -/
def summarizeByBlueprint (nodes : Array NodeData) : List String :=
  (nodesByBlueprint nodes).map fun (source, group) =>
    s!"{blueprintName source}. {summarizeStatus group}"

/-
A link to a node. The status of the node is shown next to the link, so that no reference in the
prose can suggest more than the node's own box claims.
-/
inline_extension Inline.bp (label : String) where
  data := .str label
  extraCss := {⟨nodeCss⟩}
  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some fun go _ data content => do
    let .str label := data
      | reportError "Failed to deserialize a reference to a blueprint node"; content.mapM go
    let state ← HtmlT.state
    let found := (coveredNodes state).find? (·.node.label == label)
    match state.resolveDomainObject nodeDomain label, found with
    | .ok dest, .some data =>
      return html%{
        <a href={dest.link}>{← content.mapM go}</a>
        {txt " "}<span class={s!"bp-badge bp-{data.status.word}"}>{txt data.status.word}</span>
      }
    | .error e, _ =>
      reportError s!"Cannot link to blueprint node '{label}': {e}"
      content.mapM go
    | _, .none =>
      reportError s!"Cannot link to blueprint node '{label}': it has no data"
      content.mapM go

/-- The argument of the `bp` role. -/
structure BpConfig where
  /-- The `\label` of the node to link to. -/
  label : String

instance : FromArgs BpConfig DocElabM where
  fromArgs := BpConfig.mk <$> .positional `label .string

/--
Links to a node of the blueprint, as in `{bp "lem:gm"}[the cohomology of the multiplicative group]`,
and shows its status. With empty text, as in `{bp "lem:gm"}[]`, the link shows the name of the node.
A label that the blueprint does not have is an error when the document is elaborated, and one that
the book does not cover is an error when the document is rendered.
-/
@[role]
def bp : RoleExpanderOf BpConfig
  | { label }, content => do
    let (_, bpNode) ← findNode label
    let content ← content.mapM elabInline
    let content ←
      if content.isEmpty then
        pure #[← ``(Verso.Doc.Inline.text $(quote (nodeName bpNode)))]
      else
        pure content
    ``(Verso.Doc.Inline.other (Inline.bp $(quote label)) #[$content,*])

/- The sentences that summarize the status of the nodes, generated like the overview. -/
block_extension Block.statusSummary where
  data := .null
  extraCss := {⟨nodeCss⟩}
  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some fun _ _ _ _ _ => do
    let nodes := coveredNodes (← HtmlT.state)
    let sentences := (summarizeByBlueprint nodes).toArray.map fun sentence =>
      html%{<p class="bp-summary">{txt sentence}</p>}
    return .seq sentences

/-- Renders one generated sentence for each blueprint that summarizes the status of its nodes. -/
@[block_command]
def statusSummary : BlockCommandOf Unit
  | () => ``(Verso.Doc.Block.other Block.statusSummary #[])

/- The table of all nodes, generated from what the `node` directives recorded. -/
block_extension Block.statusOverview where
  data := .null
  extraCss := {⟨nodeCss⟩}
  traverse _ _ _ := do
    saveCommit
    return none
  toTeX := none
  toHtml := some fun _ _ _ _ _ => do
    let state ← HtmlT.state
    let nodes := coveredNodes state
    let commit : Html := match savedCommit? state with
      | .some c =>
        html%{
          <p>{txt "Built from commit "}
          <a href={s!"{repositoryUrl}/tree/{c}"}><code>{txt (c.take 8).copy}</code></a>
          {txt "."}</p>
        }
      | .none => .empty
    let row (data : NodeData) : Html :=
      let link := match state.resolveDomainObject nodeDomain data.node.label with
        | .ok dest => dest.link
        | .error _ => "#"
      let decls : Array Html := data.decls.map fun d =>
        html%{<div><code>{txt d.name.toString}</code></div>}
      html%{
        <tr>
          <td><a href={link}><code>{txt data.node.label}</code></a></td>
          <td>{txt (nodeName data.node)}</td>
          <td><span class={s!"bp-badge bp-{data.status.word}"}>{txt data.status.word}</span></td>
          <td>{decls}</td>
        </tr>
      }
    let part : String × Array NodeData → Html := fun (source, group) =>
      html%{
        <h2>{txt (blueprintName source)}</h2>
        <p>{txt (summarizeStatus group)}</p>
        <table class="bp-overview-table">
          <thead>
            <tr>
              <th>{txt "Label"}</th>
              <th>{txt "Node"}</th>
              <th>{txt "Status"}</th>
              <th>{txt "Lean declarations"}</th>
            </tr>
          </thead>
          <tbody>{group.map row}</tbody>
        </table>
      }
    return html%{
      <div class="bp-overview">
        {commit}
        {(nodesByBlueprint nodes).toArray.map part}
      </div>
    }

/-- Renders one table of nodes and their status for each blueprint. -/
@[block_command]
def statusOverview : BlockCommandOf Unit
  | () => ``(Verso.Doc.Block.other Block.statusOverview #[])

/-- The labels of the book that are not unique. -/
private def duplicatedLabels (state : TraverseState) : Array String := Id.run do
  let some domain := state.domains.get? nodeDomain | return #[]
  return domain.objects.toArray.filterMap fun (label, obj) =>
    if obj.ids.size > 1 then some label else none

/--
The completeness check: every node of the blueprint must be presented exactly once in the book, and
the book must present nothing else. It reads the blueprint afresh, and runs after rendering, using
the labels that were actually seen in the document.
-/
def checkCompleteness : ExtraStep := fun _ _ state _ => do
  let blueprint ← Blueprint.readNodes
  let covered := (coveredNodes state).map (·.node.label)
  let labels := blueprint.map (·.label)
  for label in labels do
    unless covered.contains label do
      reportError s!"Blueprint node '{label}' is not covered by the book."
  for label in covered do
    unless labels.contains label do
      reportError s!"The book has a node '{label}' that the blueprint does not."
  for label in duplicatedLabels state do
    reportError s!"The book presents blueprint node '{label}' more than once."
  let summary := " ".intercalate (summarizeByBlueprint (coveredNodes state))
  IO.println s!"{blueprint.size} blueprint nodes. {summary}"

end OrlikSolomonBook
