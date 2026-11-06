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
* the library imports this tool;
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
* Each of these is read from the data of its own module, not from the merged environment. When
  several modules prove a theorem of the same name and statement, the import keeps one proof without
  comparing them, and a theorem can replace an axiom. A `sorry` or an `axiom` could otherwise hide
  behind a clean copy in another module.
* We avoid `Lean.collectAxioms`. It starts afresh on each call unless environment extensions are
  loaded, which would run every initializer in Mathlib through the interpreter, and it ignores
  constants that it cannot find. Instead, one walk covers the dependencies of all declarations, it
  reads the proofs themselves, and a constant it cannot find is an error.
-/

open Lean System

namespace Audit

/-- The root module of the library. A module is in the project if this is a prefix of its name. -/
def rootModule : Name := `OrlikSolomon

/-- This module. Lake would let the library import it, and the library must not depend on it. -/
def toolModule : Name := `Audit

/-- The only axioms that a declaration of the project may depend on. -/
def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `type` is `∀ xs, self → Nat` and `value` is `fun xs x => body`, for `n` binders `xs`,
with `self` under `xs` and with `body` under `xs` and `x`, satisfying `isBody`. -/
def isIndexFunction (self : Expr) (isBody : Expr → Bool) : Nat → Expr → Expr → Bool
  | 0, .forallE _ x (.const ``Nat []) _, .lam _ x' body _ =>
    x == self && x' == self && isBody body
  | n + 1, .forallE _ d type _, .lam _ d' value _ =>
    d == d' && isIndexFunction self isBody n type value
  | _, _, _ => false

/-- Removes all leading lambdas. -/
def stripLambdas : Expr → Expr
  | .lam _ _ body _ => stripLambdas body
  | e => e

/-- Whether `info` is the unsafe `T.ctorIdx._impl` that `Lean.mkCtorIdx` generates for an inductive
type `T`, unless `T` has exactly one constructor. Such types are common, so the audit has to accept
it. A name proves nothing, since anybody can write `unsafe def Foo.ctorIdx._impl`, so this asks for
what Lean generates, term for term:

* `T` is an inductive type without exactly one constructor, and `T.ctorIdx` is a safe definition;
* `T.ctorIdx` is `fun xs x => T.casesOn x 0 1 ...`, with `implemented_by T.ctorIdx._impl`;
* `T.ctorIdx._impl` is `fun xs x => getObjTagNat x`.

The `.olean` does not record who wrote a declaration, so a handwritten exact copy of all this also
passes. But that copy has no freedom left in which to do anything else. -/
def isGeneratedCtorIdxImpl (env : Environment) (info : ConstantInfo) : Bool := Id.run do
  let .defnInfo impl := info | return false
  let .str ctorIdxName@(.str indName "ctorIdx") "_impl" := impl.name | return false
  let some (.inductInfo ind) := env.find? indName | return false
  let some (.defnInfo ctorIdx) := env.find? ctorIdxName | return false
  let us := ind.levelParams.map mkLevelParam
  let n := ind.numParams + ind.numIndices
  -- `T.{us} xs`, under the binders `xs`.
  let self := mkAppN (.const indName us) ((Array.range n).reverse.map .bvar)
  let isImplBody : Expr → Bool
    | .app (.app (.const ``getObjTagNat [_]) α) (.bvar 0) => α == self.liftLooseBVars 0 1
    | _ => false
  -- The arguments of `casesOn` are the parameters, motive, indices, major premise and alternatives.
  let major := ind.numParams + 1 + ind.numIndices
  let isCtorIdxBody (body : Expr) : Bool :=
    let args := body.getAppArgs
    body.getAppFn == .const (mkCasesOnName indName) (Level.one :: us) &&
      args.size == major + 1 + ind.numCtors && args[major]! == .bvar 0 &&
      (args.extract (major + 1)).zipIdx.all fun (alt, i) => stripLambdas alt == mkRawNatLit i
  return ind.numCtors != 1 && impl.safety == .unsafe && ctorIdx.safety == .safe &&
    impl.levelParams == ind.levelParams && ctorIdx.levelParams == ind.levelParams &&
    Compiler.getImplementedBy? env ctorIdxName == some impl.name &&
    isIndexFunction self isImplBody n impl.type impl.value &&
    isIndexFunction self isCtorIdxBody n ctorIdx.type ctorIdx.value

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

/-- Walks the dependencies of the constants in `seed`, which come with the constants that they refer
to, looking up anything else in the environment. Each constant is visited once however many others
reach it. -/
def closure (env : Environment) (seed : Std.HashMap Name (Array Name)) : Closure := Id.run do
  let mut stack := seed.fold (init := #[]) fun stack _ refs => stack ++ refs
  let mut visited := seed
  let mut missing := #[]
  repeat
    let some c := stack.back? | break
    stack := stack.pop
    if visited.contains c then
      continue
    let some info := env.find? c
      | visited := visited.insert c #[]
        missing := missing.push c
    let refs := references info
    visited := visited.insert c refs
    for r in refs do
      unless visited.contains r do
        stack := stack.push r
  let axioms := visited.fold (init := #[]) fun axioms c _ =>
    if (env.find? c).any (·.isAxiom) then axioms.push c else axioms
  return { references := visited, axioms, missing }

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
  let refs := (env.find? ``Classical.em).elim #[] references
  let { axioms, missing, .. } := closure env (({} : Std.HashMap _ _).insert ``Classical.em refs)
  unless missing.isEmpty && allowedAxioms.all axioms.contains do
    throw <| .userError s!"the audit cannot see through proofs: from `Classical.em` it reached \
      the axioms {axioms} and the missing constants {missing}"

/-- Checks every declaration in every module of the project, returning the problems found and a
one-line summary. Failures are explained by a second search, so passing runs do not pay for it. -/
def checkDeclarations : IO (Array String × String) := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := rootModule }] {} (leakEnv := true) (level := .private)
  checkWalkSeesProofs env
  -- Each constant with what it refers to, in all the modules that store a constant of that name.
  let mut ours : Std.HashMap Name (Array Name) := {}
  let mut numModules := 0
  let mut problems := #[]
  if env.allImportedModuleNames.contains toolModule then
    problems := problems.push s!"{rootModule} must not import the audit tool, {toolModule}"
  for mod in env.allImportedModuleNames, data in env.header.moduleData do
    unless rootModule.isPrefixOf mod do
      continue
    numModules := numModules + 1
    for info in data.constants do
      ours := ours.alter info.name fun old? => some (old?.getD #[] ++ references info)
      if info.isAxiom then
        problems := problems.push s!"{info.name} is declared as an axiom"
      if info.isUnsafe && !isGeneratedCtorIdxImpl env info then
        problems := problems.push s!"{info.name} is declared unsafe"
  let { references, axioms, missing } := closure env ours
  for c in missing.qsort Name.lt do
    problems := problems.push s!"{c} is not in the environment"
  let forbidden := axioms.filter (!allowedAxioms.contains ·)
  if !forbidden.isEmpty then
    let users := invert references
    for ax in forbidden.qsort Name.lt do
      for c in (dependents users ax).toArray.qsort Name.lt do
        if ours.contains c then
          problems := problems.push s!"{c} depends on the axiom {ax}"
  let summary := s!"{ours.size} declaration(s) in {numModules} module(s) use only the axioms \
    {axioms.qsort Name.lt}"
  return (problems.qsort (· < ·), summary)

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
