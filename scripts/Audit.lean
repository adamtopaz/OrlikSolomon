/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

import Lean

/-!
# The project audit

`lake exe audit`, run from the root of the repository after building the library, fails if

* `OrlikSolomon.lean` does not publicly import every module in `OrlikSolomon/`;
* a module of the project declares an `axiom` or an `unsafe` constant;
* a declaration of the project depends on an axiom other than `propext`, `Classical.choice` and
  `Quot.sound`, which is how `sorry`, `admit` and `native_decide` show up.

Use `scripts/check.sh`, which builds the library first, so that the audit cannot read stale files.

Modules and declarations are discovered, so there is no list to maintain. The library does not
import this file and this file does not import the library, which is read from its `.olean` files
at run time.

## Implementation notes

* The library must be loaded at `OLeanLevel.private`. Under the module system the plain `.olean`
  holds theorems as axioms, with no proofs, and omits private declarations. Those are only in
  `.olean.private`, so at a lower level a `sorry` in a proof would be out of sight.
* A declaration audited here is any constant stored in a module of the project. This includes
  private and auxiliary constants, as well as those declared outside the `OrlikSolomon` namespace.
* We avoid `Lean.collectAxioms`. It starts afresh on each call unless environment extensions are
  loaded, which would run every initializer in Mathlib through the interpreter, and it ignores
  constants that it cannot find. Instead, one walk covers the dependencies of all declarations, it
  reads the proofs themselves, and a constant it cannot find is an error.
-/

open Lean System

namespace Audit

/-- The root module of the library. A module is in the project if this is a prefix of its name. -/
def rootModule : Name := `OrlikSolomon

/-- The only axioms that a declaration of the project may depend on. -/
def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `c` is the unsafe `T.ctorIdx._impl` that Lean generates for every inductive type `T`
with several constructors, which nobody wrote and which must not fail the audit. The test is exact
on purpose: `Name.isInternal` would also let through every `private unsafe def`, because private
names start with `_private`. -/
def isGeneratedUnsafe : Name → Bool
  | .str (.str _ "ctorIdx") "_impl" => true
  | _ => false

/-- The modules with a source file under `OrlikSolomon/`, a directory which need not exist. -/
def sourceModules : IO (Array Name) := do
  let dir : FilePath := rootModule.toString
  unless ← dir.isDir do
    return #[]
  let files ← dir.walkDir
  let leanFiles := files.filter (·.extension == some "lean")
  let modules := leanFiles.map fun file =>
    (file.withExtension "").components.foldl Name.mkStr .anonymous
  return modules.qsort Name.lt

/-- Checks that the root file publicly imports every module with a source file, returning the
problems found and the number of modules. Reading the header with Lean's own parser means that a
commented-out import does not count. A `public meta import` does count, as in Mathlib's root file,
since it suits a module of metaprograms. -/
def checkRootImports : IO (Array String × Nat) := do
  let rootFile : FilePath := s!"{rootModule}.lean"
  let (imports, _, messages) ← Elab.parseImports (← IO.FS.readFile rootFile) rootFile.toString
  let mut problems := #[]
  if messages.hasErrors then
    problems := problems.push s!"{rootFile}: cannot parse the imports"
  let modules ← sourceModules
  for mod in modules do
    unless imports.any fun i => i.module == mod && i.isExported do
      problems := problems.push s!"{rootFile} does not publicly import {mod}"
  return (problems, modules.size)

/-- The constants that `info` refers to directly, which are those that `Lean.collectAxioms` follows.
The cases are listed in full so that a new kind of constant is a compile error here. -/
def references (info : ConstantInfo) : Array Name :=
  let body := match info with
    | .defnInfo v => v.value.getUsedConstants
    | .thmInfo v => v.value.getUsedConstants
    | .opaqueInfo v => v.value.getUsedConstants
    | .inductInfo v => v.ctors.toArray
    | .axiomInfo _ | .quotInfo _ | .ctorInfo _ | .recInfo _ => #[]
  info.type.getUsedConstants ++ body

/-- The result of walking the dependencies of some constants. -/
structure Closure where
  /-- Every constant reached, with the constants that it refers to directly. -/
  references : Std.HashMap Name (Array Name) := {}
  /-- The axioms reached. -/
  axioms : Array Name := #[]
  /-- The constants reached that are not in the environment. -/
  missing : Array Name := #[]

/-- Walks the dependencies of `roots`, visiting each constant once however many roots reach it. -/
def closure (env : Environment) (roots : Array Name) : Closure := Id.run do
  let mut stack := roots
  let mut result : Closure := {}
  repeat
    let some c := stack.back? | break
    stack := stack.pop
    if result.references.contains c then
      continue
    let some info := env.find? c
      | result := { result with
          references := result.references.insert c #[]
          missing := result.missing.push c }
    let refs := references info
    result := { result with references := result.references.insert c refs }
    if info.isAxiom then
      result := { result with axioms := result.axioms.push c }
    for r in refs do
      unless result.references.contains r do
        stack := stack.push r
  return result

/-- Reverses the arrows of the graph in `Closure.references`. -/
def invert (references : Std.HashMap Name (Array Name)) : Std.HashMap Name (Array Name) :=
  references.fold (init := {}) fun users c refs =>
    refs.foldl (init := users) fun users r =>
      users.alter r fun old? => some ((old?.getD #[]).push c)

/-- The constants that depend on `target`, given the output of `invert`. -/
def dependents (users : Std.HashMap Name (Array Name)) (target : Name) : NameSet := Id.run do
  let mut stack := #[target]
  let mut seen : NameSet := {}
  repeat
    let some c := stack.back? | break
    stack := stack.pop
    for user in users.getD c #[] do
      unless seen.contains user do
        seen := seen.insert user
        stack := stack.push user
  return seen

/-- Throws if the walk cannot see through proofs, in which case it would pass whatever the library
contains. `Classical.em` uses all of the allowed axioms, and only in its proof, so this keeps the
audit honest across toolchain bumps without planting anything in the library. -/
def checkWalkSeesProofs (env : Environment) : IO Unit := do
  let { axioms, missing, .. } := closure env #[``Classical.em]
  unless missing.isEmpty && allowedAxioms.all axioms.contains do
    throw <| .userError s!"the audit cannot see through proofs: from `Classical.em` it reached \
      the axioms {axioms} and the missing constants {missing}"

/-- Checks every declaration in every module of the project, returning the problems found and a
one-line summary. Failures are explained by a second search, so passing runs do not pay for it. -/
def checkDeclarations : IO (Array String × String) := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := rootModule }] {} (leakEnv := true) (level := .private)
  checkWalkSeesProofs env
  -- A set, because a generated constant can be stored in more than one module.
  let mut ours : NameSet := {}
  let mut numModules := 0
  for mod in env.allImportedModuleNames, data in env.header.moduleData do
    if rootModule.isPrefixOf mod then
      numModules := numModules + 1
      ours := data.constNames.foldl .insert ours
  let declarations := ours.toArray.qsort Name.lt
  let mut problems := #[]
  for c in declarations do
    let some info := env.find? c | continue -- reported as missing by the walk below
    if info.isAxiom then
      problems := problems.push s!"{c} is declared as an axiom"
    if info.isUnsafe && !isGeneratedUnsafe c then
      problems := problems.push s!"{c} is declared unsafe"
  let { references, axioms, missing } := closure env declarations
  for c in missing.qsort Name.lt do
    problems := problems.push s!"{c} is not in the environment"
  let forbidden := axioms.filter (!allowedAxioms.contains ·)
  if !forbidden.isEmpty then
    let users := invert references
    for ax in forbidden.qsort Name.lt do
      for c in (dependents users ax).toArray.qsort Name.lt do
        if ours.contains c then
          problems := problems.push s!"{c} depends on the axiom {ax}"
  let summary := s!"{declarations.size} declaration(s) in {numModules} module(s) use only the \
    axioms {axioms.qsort Name.lt}"
  return (problems, summary)

end Audit

/-- Runs both checks, reporting everything found, and exits with a failure if there is a problem. -/
public def main : IO UInt32 := do
  let (importProblems, numSources) ← Audit.checkRootImports
  let (declarationProblems, summary) ← Audit.checkDeclarations
  let problems := importProblems ++ declarationProblems
  for problem in problems do
    IO.eprintln s!"audit: error: {problem}"
  if problems.isEmpty then
    IO.println s!"audit: {Audit.rootModule}.lean imports all {numSources} modules under \
      {Audit.rootModule}/"
    IO.println s!"audit: {summary}"
    return 0
  IO.eprintln s!"audit: FAILED with {problems.size} problem(s)"
  return 1
