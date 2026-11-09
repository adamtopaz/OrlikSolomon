/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
module

public import Lean

/-!
# The project audit

`lake exe audit`, run from the root of the repository after building the library, fails if

* `OrlikSolomon.lean` does not publicly import every module in `OrlikSolomon/`;
* the library imports a module with no source file in `OrlikSolomon/`, unless it comes from a
  dependency. This covers a stale `.olean`, this tool, and a module elsewhere in this package;
* a module of the project declares anything other than a theorem, a safe definition, a safe opaque
  constant, or a safe inductive type with its constructors and recursor. This rules out `axiom`,
  `unsafe` and `partial def`. The only exceptions are two kinds of constant that Lean itself
  generates for safe code: see `isGeneratedCtorIdxImpl` and `isGeneratedUnsafeRec`;
* a declaration of the project depends on an axiom other than `propext`, `Classical.choice` and
  `Quot.sound`, which is how `sorry`, `admit` and `native_decide` show up;
* Parts I and II of `OrlikSolomon.MainTheorem`, the file that states the main theorem, mention a
  declaration of the library. See `checkInterface`.

`lake exe audit --interface` makes only the last check. Given the components of a module name, as in
`lake exe audit --interface OrlikSolomon MainTheorem`, it checks that module instead, loading it on
its own, which is how the check is tested on a module that breaks the rule.

`lake exe audit --replay` makes the same checks of the modules, then sends every constant of each
one back through the kernel, proofs included, and leaves nothing out. It fails unless the kernel
accepts every module of the library, and what it then holds is what the `.olean` files say. The
first command only reads what the build recorded, so it would not notice a declaration that reached
the `.olean` files without the kernel accepting it.

Use `scripts/check.sh` and `scripts/replay.sh`, which build the library first, so that these cannot
read stale files.

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
* The modules of the library are what the root imports, read from the environment. They are compared
  with the source files as `Name`s in both directions, and passed to a child process as separate
  arguments, one for each component. No module name is parsed from text, so a name may contain
  spaces, quotes or dots. A stale `.olean` that nothing imports is not part of the library.
* The replay calls `Lean.Kernel.Environment.replay`, as the `leanchecker` binary does, and replays
  each module into the environment of its own imports, as it also does. It does not run that binary,
  because its argument is a module prefix, which also selects any submodules and stale `.olean`
  files, and because it crashes when one process replays two modules: see #47. Each module has its
  own process for that reason.
* `Lean.Kernel.Environment.replay` leaves out some constants and does not compare others, so
  `replayConstants` deals with these itself. See there for the list.
* The library has no `partial def`, and a mathematical library has no need of one, so the audit
  rejects it. It cannot reject every partial constant, because Lean generates one to compile each
  recursive definition, and the library has several.
* The interface boundary checks every stored declaration outside its proof namespace, including
  private and auxiliary declarations. Every type is checked, and definition and opaque bodies are
  checked after erasing proof subterms. A predicate returning `Prop` is data, so it is checked.
  Bound variables are opened before asking Lean whether a subterm is a proof. References into the
  proof namespace are forbidden as data even though they come from the same module.
-/

open Lean System

namespace Audit

/-- The root module of the library. A module is in the project if this is a prefix of its name. -/
def rootModule : Name := `OrlikSolomon

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

/-- Whether `v` is the partial `f._unsafe_rec` that Lean generates in order to compile a recursive
definition `f`. It has the type of `f`, and `f` has to be a safe definition, which the kernel checks
separately. A `partial def f` gets one too, but makes `f` opaque, so it is not accepted here.

Safe code cannot refer to a partial constant, so this can never affect what is provable. -/
def isGeneratedUnsafeRec (env : Environment) (v : DefinitionVal) : Bool := Id.run do
  let some name := Compiler.isUnsafeRecName? v.name | return false
  let some (.defnInfo f) := env.find? name | return false
  let opaqueHints := v.hints matches .opaque
  return opaqueHints && f.safety == .safe && f.type == v.type && f.levelParams == v.levelParams

/-- What is wrong with a module of the project declaring `info`, if anything. This is an allowlist.
The cases are listed in full so that a new kind of constant, or of safety, is a compile error. -/
def constantProblem (env : Environment) (info : ConstantInfo) : Option String :=
  let ifUnsafe (isUnsafe : Bool) := if isUnsafe then some "is declared unsafe" else none
  match info with
  | .thmInfo _ => none
  | .defnInfo v =>
    match v.safety with
    | .safe => none
    | .partial => if isGeneratedUnsafeRec env v then none else some "is declared partial"
    | .unsafe => if isGeneratedCtorIdxImpl env info then none else some "is declared unsafe"
  | .opaqueInfo v => ifUnsafe v.isUnsafe
  | .inductInfo v => ifUnsafe v.isUnsafe
  | .ctorInfo v => ifUnsafe v.isUnsafe
  | .recInfo v => ifUnsafe v.isUnsafe
  | .axiomInfo _ => some "is declared as an axiom"
  | .quotInfo _ => some "is declared as a quotient primitive"

/-- The library, as the build recorded it. -/
structure Library where
  /-- The environment of the root module, at `OLeanLevel.private`. -/
  env : Environment
  /-- The root and each module it imports that is not from a dependency, with its data. -/
  modules : Array (Name × ModuleData)
  /-- The reasons that `modules` is not what the source files say it should be, or holds a constant
  that it may not. -/
  problems : Array String

/-- The entries of the search path that belong to dependencies, which are the packages and the
toolchain. A worktree shares `.lake/packages` through a symlink, hence the real paths. An entry that
does not exist holds no modules. -/
def dependencyEntries : IO (List FilePath) := do
  let roots := [← IO.FS.realPath ".lake/packages", ← IO.FS.realPath (← findSysroot)]
  (← searchPathRef.get).filterM fun entry => do
    try
      let real ← IO.FS.realPath entry
      return roots.any (·.components.isPrefixOf real.components)
    catch _ =>
      return false

/-- Loads the library and compares its modules with the source files, in both directions. Anything
else that is imported has to come from a dependency. Otherwise it would escape every check here,
which only look at the modules of the library, and the linters too. It also checks the kind of each
constant in the library. -/
def loadLibrary : IO Library := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := rootModule }] {} (leakEnv := true) (level := .private)
  let sources ← sourceModules
  let dependencies ← dependencyEntries
  let mut modules := #[]
  let mut problems := #[]
  for mod in env.allImportedModuleNames, data in env.header.moduleData do
    if rootModule.isPrefixOf mod then
      modules := modules.push (mod, data)
      unless mod == rootModule || sources.contains mod do
        problems := problems.push s!"{mod} is imported, but it has no source file in {rootModule}/"
      for info in data.constants do
        if let some problem := constantProblem env info then
          problems := problems.push s!"{info.name} {problem}"
    else
      let olean ← findOLean mod
      unless dependencies.any (·.components.isPrefixOf olean.components) do
        problems := problems.push
          s!"{mod} is imported, but it is neither in {rootModule}/ nor from a dependency"
  for mod in sources do
    unless modules.any (·.1 == mod) do
      problems := problems.push s!"{mod} has a source file, but the library does not import it"
  return { env, modules, problems }

/-- Checks every declaration in every module of the project, returning the problems found and a
one-line summary. Failures are explained by a second search, so passing runs do not pay for it. -/
def checkDeclarations (library : Library) : IO (Array String × String) := do
  let env := library.env
  checkWalkSeesProofs env
  -- Each constant with what it refers to, in all the modules that store a constant of that name.
  let mut ours : Std.HashMap Name (Array Name) := {}
  let mut problems := library.problems
  for (_, data) in library.modules do
    for info in data.constants do
      ours := ours.alter info.name fun old? => some (old?.getD #[] ++ references info)
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
  let summary := s!"{ours.size} declaration(s) in {library.modules.size} module(s) use only the \
    axioms {axioms.qsort Name.lt}"
  return (problems.qsort (· < ·), summary)

/-- The module that states the main theorem. Its Parts I and II are what an auditor reads, so they
may mention only Mathlib, Lean core and the module itself. -/
def interfaceModule : Name := `OrlikSolomon.MainTheorem

/-- The namespace of Part III of `interfaceModule`, the proofs, which may use the whole library. -/
def interfaceProofNamespace : Name := `OrlikSolomon.MainTheorem.Proof

/-- Whether a constant of the interface module belongs to its Part III. A private name is read
through its user-facing name, so that `private` cannot move a declaration out of Part III. -/
def isInterfaceProof (c : Name) : Bool :=
  interfaceProofNamespace.isPrefixOf (privateToUserName c)

/-- The constants in the data of an expression, with proof subterms erased. A proposition is
itself data: `P : Prop` is scanned, whereas a term `h : P` is not. In particular, aliases of
library predicates cannot hide behind proof irrelevance.

Recursion follows the original expression, so it is structural. `opened` records the free
variables introduced for its bound variables. Only the expression passed to type inference is
instantiated, preventing loose-bound-variable errors beneath dependent binders. -/
def interfaceExprReferences (e : Expr) (opened : Array Expr := #[]) : Meta.MetaM (Array Name) := do
  if ← Meta.isProof (e.instantiateRev opened) then
    return #[]
  match e with
  | .const c _ => return #[c]
  | .app f a =>
    return (← interfaceExprReferences f opened) ++ (← interfaceExprReferences a opened)
  | .lam n d b bi | .forallE n d b bi =>
    let refs ← interfaceExprReferences d opened
    Meta.withLocalDecl n bi (d.instantiateRev opened) fun x => do
      return refs ++ (← interfaceExprReferences b (opened.push x))
  | .letE n t v b _ =>
    -- A local proof's annotation belongs to that proof, not to the surrounding data. Its
    -- proposition is still checked if exposed in the declaration's type or elsewhere as data.
    let refs ← if ← Meta.isProof (v.instantiateRev opened) then pure #[] else
      return (← interfaceExprReferences t opened) ++ (← interfaceExprReferences v opened)
    Meta.withLetDecl n (t.instantiateRev opened) (v.instantiateRev opened) fun x => do
      return refs ++ (← interfaceExprReferences b (opened.push x))
  | .proj n _ s => return #[n] ++ (← interfaceExprReferences s opened)
  | .mdata _ b => interfaceExprReferences b opened
  | .mvar _ => throwError "an interface declaration contains an unresolved metavariable"
  | .bvar _ | .fvar _ | .sort _ | .lit _ => return #[]

/-- Every declaration's type is checked. Safe definitions and opaque declarations additionally
have their values checked, with proof subterms erased. A definition returning `Prop` is a
predicate, not a proof, and its value is checked. -/
def interfaceReferences (info : ConstantInfo) : Meta.MetaM (Array Name) := do
  let refs ← interfaceExprReferences info.type
  let value := match info with
    | .defnInfo v => some v.value
    | .opaqueInfo v => some v.value
    | .thmInfo _ | .inductInfo _ | .axiomInfo _ | .quotInfo _ | .ctorInfo _ | .recInfo _ => none
  match value with
  | some value => return refs ++ (← interfaceExprReferences value)
  | none => return refs

/-- Checks every stored declaration outside the proof namespace, including private declarations,
auxiliaries, constructors, projections and recursors. Module provenance, rather than a constant's
namespace, determines whether a reference is from the library. A data reference into Part III is
also forbidden, although Part III is in the same module.

The declarations are read from their own module data, not selected from the merged environment.
Failed type inference or missing provenance is an error, never an exemption. -/
def checkInterfaceM (env : Environment) (module : Name) (data : ModuleData) :
    Meta.MetaM (Array String × Nat) := do
  let mut problems := #[]
  let mut checked := 0
  for info in data.constants do
    if isInterfaceProof info.name then
      continue
    checked := checked + 1
    let refs ← try interfaceReferences info catch ex =>
      problems := problems.push s!"{info.name}: cannot inspect interface data: {← ex.toMessageData.toString}"
      pure #[]
    for r in refs do
      unless (env.find? r).isSome do
        problems := problems.push s!"{info.name} refers to {r}, which is not in the environment"
        continue
      let some idx := env.getModuleIdxFor? r
        | problems := problems.push s!"{info.name} refers to {r}, which belongs to no module"
          continue
      let some rModule := env.header.moduleNames[idx.toNat]?
        | problems := problems.push s!"{info.name} refers to {r}, whose module index is invalid"
          continue
      if rModule == module then
        if isInterfaceProof r then
          problems := problems.push s!"{info.name} refers to {r}, a declaration of Part III of {module}"
      else if rootModule.isPrefixOf rModule then
        problems := problems.push s!"{info.name} refers to {r}, from the library module {rModule}"
  return (problems.qsort (· < ·), checked)

/-- Runs the interface boundary check on an imported module's stored data. This entry point also
allows compiled scratch modules to exercise the same checker as the default project audit. -/
public def checkInterface (env : Environment) (module : Name) (data : ModuleData) :
    IO (Array String × Nat) := do
  let (result, _) ← (checkInterfaceM env module data).run'.toIO
    { fileName := "<interface audit>", fileMap := default } { env }
  return result

/-- The data of `module`, if the environment imports it. -/
def moduleData? (env : Environment) (module : Name) : Option ModuleData := do
  let idx ← env.getModuleIdx? module
  env.header.moduleData[idx.toNat]?

/-- Checks Parts I and II of `interfaceModule`, which the library must contain, returning the
problems found and a one-line summary. -/
def checkLibraryInterface (library : Library) : IO (Array String × String) := do
  match moduleData? library.env interfaceModule with
  | none => return (#[s!"the library does not import {interfaceModule}"], "")
  | some data =>
    let (problems, n) ← checkInterface library.env interfaceModule data
    return (problems, s!"{n} declaration(s) of Parts I and II of {interfaceModule} use only Mathlib, \
      Lean core and {interfaceModule} in their types and data")

/-- Loads `module` alone, at `OLeanLevel.private`, and checks its Parts I and II as if it were the
interface module. This is how the check is tested on a module that breaks the rule. -/
public def checkModuleInterface (module : Name) : IO (Array String × String) := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module }] {} (leakEnv := true) (level := .private)
  let some data := moduleData? env module
    | return (#[s!"{module} was not loaded"], "")
  let (problems, n) ← checkInterface env module data
  return (problems, s!"{n} declaration(s) of Parts I and II of {module} use only Mathlib, \
    Lean core and {module} in their types and data")

/-- The number of modules to replay at once. Each one loads its imports, about 2 GB, and a GitHub
runner has four cores. -/
def replayJobs : Nat := 4

/-- The argument that asks a child process to replay one module. The components of its name follow,
one in each argument. -/
def replayModuleFlag : String := "--replay-module"

/-- The components of a module name. A module with a source file has only string components, and
`loadLibrary` reports any other. -/
def nameComponents : Name → List String
  | .anonymous => []
  | .str p s => nameComponents p ++ [s]
  | .num p n => nameComponents p ++ [toString n]

/-- Sends a declaration to the kernel, throwing if it is rejected. -/
def addChecked (env : Kernel.Environment) (decl : Declaration) : IO Kernel.Environment := do
  match env.addDeclCore 0 0 decl (cancelTk? := none) with
  | .ok env => return env
  | .error ex => throw <| .userError (← (ex.toMessageData {}).toString)

/-- Sends all these constants to the kernel, on top of `imported`, leaving nothing out. Throws if it
rejects one. `Lean.Kernel.Environment.replay` does most of the work, with these gaps:

* It leaves out partial and unsafe constants. These are sent here in one mutual block for each kind,
  which is how Lean adds them, so the kernel checks every body with all of them in scope. A partial
  constant cannot refer to an unsafe one, so the partial block goes first.
* It leaves out a theorem whose name and statement are already in `imported`. These are checked here
  under a fresh name, so that the proof in this module is not taken on trust.
* It regenerates an inductive type without comparing the result with what is stored, and the kernel
  relies on what is stored, once it has been imported. So every constant must end up in the
  environment exactly as stored, which also catches any constant that nothing above sent. -/
def replayConstants (imported : Kernel.Environment) (constants : Std.HashMap Name ConstantInfo) :
    IO Unit := do
  let mut env ← imported.replay constants
  let definitions := constants.toList.filterMap fun (_, info) =>
    match info with
    | .defnInfo v => some v
    | _ => none
  for safety in [DefinitionSafety.partial, .unsafe] do
    let block := definitions.filter (·.safety == safety)
    unless block.isEmpty do
      env ← addChecked env (.mutualDefnDecl block)
  for (name, info) in constants do
    if let (.thmInfo v, some _) := (info, imported.find? name) then
      let fresh := name.str "_auditDuplicate"
      discard <| addChecked env (.thmDecl { v with name := fresh, all := [fresh] })
    else unless env.find? name == some info do
      throw <| .userError s!"{name} is not stored as the kernel would store it"

/-- Replays exactly this module into the environment of its imports, and prints the number of
constants it holds. All three files of the module are required, since without the last there would
be no proofs to replay. Returning without an exception means that the kernel accepted them all. -/
def replayModule (module : Name) : IO Unit := do
  initSearchPath (← findSysroot)
  let olean ← findOLean module
  let parts ← readModuleDataParts #[olean, OLeanLevel.server.adjustFileName olean,
    OLeanLevel.private.adjustFileName olean]
  let some (public_, _) := parts[0]? | throw <| .userError s!"no data for {module}"
  let some (private_, _) := parts.back? | throw <| .userError s!"no data for {module}"
  let env ← importModules public_.imports {} (leakEnv := true) (level := .private)
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for name in private_.constNames, info in private_.constants do
    constants := constants.insert name info
  replayConstants env.toKernelEnv constants
  IO.println constants.size

/-- Throws if the replay accepts a bad constant of any of the kinds that `replayConstants` has to
treat differently, in which case it would pass whatever the library contains. This keeps it honest
across toolchain bumps without planting anything in the library. -/
def checkReplayRejectsBadConstants (env : Environment) : IO Unit := do
  let badValue := mkConst ``True.intro
  let theorem_ : ConstantInfo := .thmInfo
    { name := `Audit.falseTheorem, levelParams := [], type := mkConst ``False, value := badValue }
  let definition (name : Name) (safety : DefinitionSafety) : ConstantInfo := .defnInfo
    { name, safety, levelParams := [], type := mkConst ``False, value := badValue
      hints := .opaque }
  let some (.thmInfo trivialVal) := env.find? ``trivial
    | throw <| .userError "`trivial` is not a theorem, so the audit needs updating"
  let duplicate : ConstantInfo := .thmInfo { trivialVal with value := mkConst ``Nat.zero }
  for info in [theorem_, definition `Audit.falsePartial .partial,
      definition `Audit.falseUnsafe .unsafe, duplicate] do
    let accepted ←
      try
        replayConstants env.toKernelEnv (({} : Std.HashMap _ _).insert info.name info)
        pure true
      catch _ =>
        pure false
    if accepted then
      throw <| .userError s!"the kernel replay accepted the bad constant {info.name}"

/-- Replays a module in a child process, returning the problem if there is one. The child has to
report the number of constants that the data of the module holds. -/
def replayInChild (tool : FilePath) (module : Name) (numConstants : Nat) : IO (Option String) := do
  let args := #[replayModuleFlag] ++ (nameComponents module).toArray
  let output ← IO.Process.output { cmd := tool.toString, args }
  if output.exitCode != 0 then
    return some s!"the replay of {module} failed with exit code {output.exitCode}:\n{output.stderr}"
  let reported := output.stdout.trimAscii.toString
  if reported != toString numConstants then
    return some s!"the replay of {module} reported {reported} constant(s), not {numConstants}"
  return none

/-- Replays every module of the library, returning the problems found and a one-line summary. The
workers record each module they finish, and it is a problem if that is not exactly the library. -/
def checkReplay (library : Library) : IO (Array String × String) := do
  checkReplayRejectsBadConstants library.env
  let tool ← IO.appPath
  let next ← IO.mkRef 0
  let tasks ← (Array.range replayJobs).mapM fun _ => IO.asTask (prio := .dedicated) do
    let mut finished : Array (Name × Option String) := #[]
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      let some (mod, data) := library.modules[i]? | break
      finished := finished.push (mod, ← replayInChild tool mod data.constants.size)
    return finished
  let mut finished := #[]
  for task in tasks do
    finished := finished ++ (← IO.ofExcept task.get)
  let mut problems := finished.filterMap (·.2)
  let replayed := (finished.map (·.1)).qsort Name.lt
  unless replayed == (library.modules.map (·.1)).qsort Name.lt do
    problems := problems.push s!"replayed {replayed}, which are not the modules of the library"
  let numConstants := library.modules.foldl (init := 0) fun n (_, data) => n + data.constants.size
  return (problems.qsort (· < ·), s!"the kernel accepted all {numConstants} declaration(s) in \
    {replayed.size} module(s)")

/-- Prints the problems and the lines that describe a clean run, and returns the exit code. -/
def report (tool : String) (problems : Array String) (clean : Array String) : IO UInt32 := do
  for problem in problems do
    IO.eprintln s!"{tool}: error: {problem}"
  if problems.isEmpty then
    for line in clean do
      IO.println s!"{tool}: {line}"
    return 0
  IO.eprintln s!"{tool}: FAILED with {problems.size} problem(s)"
  return 1

end Audit

open Audit in
/-- With no arguments, runs the audit. With `--replay`, replays the library through the kernel. Both
check the modules first. With `--interface`, checks only Parts I and II of the interface module, or
of the module whose name components follow. Any other arguments are an error, so that a mistyped
flag cannot pass for a clean run. -/
public def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    let (importProblems, numSources) ← checkRootImports
    let library ← loadLibrary
    let (declarationProblems, summary) ← checkDeclarations library
    let (interfaceProblems, interfaceSummary) ← checkLibraryInterface library
    report "audit" (importProblems ++ declarationProblems ++ interfaceProblems)
      #[s!"{rootModule}.lean imports all {numSources} modules under {rootModule}/", summary,
        interfaceSummary]
  | ["--interface"] =>
    let (problems, summary) ← checkLibraryInterface (← loadLibrary)
    report "interface" problems #[summary]
  | "--interface" :: name@(_ :: _) =>
    let (problems, summary) ← checkModuleInterface (name.foldl Name.mkStr .anonymous)
    report "interface" problems #[summary]
  | ["--replay"] =>
    let (importProblems, _) ← checkRootImports
    let library ← loadLibrary
    let moduleProblems := importProblems ++ library.problems
    unless moduleProblems.isEmpty do
      return ← report "replay" moduleProblems #[]
    let (replayProblems, summary) ← checkReplay library
    report "replay" replayProblems #[summary]
  | flag :: name@(_ :: _) =>
    unless flag == replayModuleFlag do
      IO.eprintln s!"audit: error: unknown arguments {args}"
      return 2
    replayModule (name.foldl Name.mkStr .anonymous)
    return 0
  | _ =>
    IO.eprintln s!"audit: error: unknown arguments {args}"
    return 2
