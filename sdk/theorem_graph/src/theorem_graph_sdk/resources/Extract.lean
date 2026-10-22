/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean
import Lean.Util.FoldConsts

open Lean Core

/-- A project whose compiled environment should be inspected for theorem-map data. -/
structure ProjectSpec where
  id : String
  rootModule : String
  /-- Optional isolated batch of already compiled modules; no aggregate compilation. -/
  rootModules : Array String := #[]
  deriving FromJson

/-- Input accepted by the theorem-map environment extractor. -/
structure ExtractConfig where
  projects : Array ProjectSpec
  deriving FromJson

/-- Declaration metadata exported from a compiled Lean environment. -/
structure RawDeclaration where
  name : String
  moduleName : String
  line : Nat
  kind : String
  docString : String
  /-- Constants referenced by the declaration's proposition or result type. -/
  statementDependencies : Array String
  /-- Constants referenced by a theorem proof or a definition's body. -/
  proofDependencies : Array String
  /-- Backward-compatible union of statement and proof/body dependencies. -/
  dependencies : Array String
  deriving ToJson

/-- Environment data for one ReasBook project. -/
structure RawProject where
  id : String
  rootModule : String
  declarations : Array RawDeclaration
  deriving ToJson

/-- Whether a Lean module belongs to the requested ReasBook project. -/
private def moduleBelongsTo (projectId : String) (moduleName : Name) : Bool :=
  moduleName.toString.splitOn "." |>.contains projectId

/-- A stable display category for a Lean constant. -/
private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- The imported module in which a declaration was compiled. -/
private def moduleOf? (env : Environment) (declName : Name) : Option Name := do
  let moduleIdx ← env.const2ModIdx[declName]?
  env.allImportedModuleNames[moduleIdx.toNat]?

/-- Direct constant names that stay inside one ReasBook project. -/
private def projectDependencyNames (env : Environment) (projectId : String)
    (names : NameSet) : Array String :=
  names.toArray.filterMap fun name => do
    let moduleName ← moduleOf? env name
    if moduleBelongsTo projectId moduleName then
      some name.toString
    else
      none

/-- Constants used by the proof/value side of a declaration.

For theorem-like declarations this is the proof term.  For definitions it is
the implementation body.  The structural cases mirror
`ConstantInfo.getUsedConstantsAsSet`, without mixing in `info.type`.
-/
private def proofUsedConstants (info : ConstantInfo) : NameSet :=
  match info.value? (allowOpaque := true) with
  | some value => value.getUsedConstantsAsSet
  | none => match info with
    | .inductInfo value => .ofList value.ctors
    | .ctorInfo value => ({} : NameSet).insert value.name
    | .recInfo value => .ofList value.all
    | _ => {}

/-- Convert one environment constant to exported metadata when it belongs to a project. -/
private def extractDeclaration? (env : Environment) (spec : ProjectSpec)
    (name : Name) (info : ConstantInfo) : CoreM (Option RawDeclaration) := do
  let some moduleName := moduleOf? env name
    | return none
  unless moduleBelongsTo spec.id moduleName do
    return none
  let docString := (← findDocString? env name (includeBuiltin := false)).getD ""
  let ranges? ← findDeclarationRanges? name
  let line := ranges?.map (·.range.pos.line) |>.getD 1
  let statementDependencies :=
    projectDependencyNames env spec.id info.type.getUsedConstantsAsSet
  let proofDependencies :=
    projectDependencyNames env spec.id (proofUsedConstants info)
  let dependencies :=
    projectDependencyNames env spec.id info.getUsedConstantsAsSet
  return some {
    name := name.toString
    moduleName := moduleName.toString
    line
    kind := declarationKind info
    docString
    statementDependencies
    proofDependencies
    dependencies
  }

/-- Extract every imported and locally added declaration for one project. -/
private def extractProjectCore (spec : ProjectSpec) : CoreM (Array RawDeclaration) := do
  let env ← getEnv
  let mut declarations := #[]
  for (name, info) in env.constants.map₁ do
    if let some declaration ← extractDeclaration? env spec name info then
      declarations := declarations.push declaration
  for (name, info) in env.constants.map₂ do
    if let some declaration ← extractDeclaration? env spec name info then
      declarations := declarations.push declaration
  return declarations

/-- Import the requested project roots and extract each project from the environment.

The Python SDK intentionally invokes this program with exactly one project per
process.  Keeping an array in the wire format preserves compatibility with the
original extractor while the process boundary keeps independent projects from
sharing one unbounded Lean environment.
-/
private unsafe def extractProjects (specs : Array ProjectSpec) : IO (Array RawProject) := do
  let imports : Array Import := specs.flatMap fun spec =>
    let roots := if spec.rootModules.isEmpty then #[spec.rootModule] else spec.rootModules
    roots.map fun root => { module := root.toName }
  IO.println s!"Importing {imports.size} theorem-map project roots"
  let env ← importModules imports {}
  let context : Core.Context := {
    fileName := "<theorem-map-extract>"
    fileMap := default
  }
  let state : Core.State := { env }
  let extractAll : CoreM (Array RawProject) := specs.mapM fun spec => do
    let declarations ← extractProjectCore spec
    return { id := spec.id, rootModule := spec.rootModule, declarations }
  let (projects, _) ← CoreM.toIO extractAll context state
  return projects

/-- Decode an extractor configuration from JSON. -/
private def parseConfig (path : System.FilePath) : IO ExtractConfig := do
  let text ← IO.FS.readFile path
  let json ← match Json.parse text with
    | .ok value => pure value
    | .error message => throw <| IO.userError s!"Invalid extractor JSON: {message}"
  match fromJson? json with
  | .ok config => pure config
  | .error message => throw <| IO.userError s!"Invalid extractor config: {message}"

/-- Export project declaration metadata as JSON for the generic theorem-map generator. -/
unsafe def main (args : List String) : IO UInt32 := do
  try
    let [configPath, outputPath] := args
      | throw <| IO.userError "Usage: Extract.lean CONFIG.json OUTPUT.json"
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let config ← parseConfig configPath
    let projects ← extractProjects config.projects
    if let some parent := (outputPath : System.FilePath).parent then
      IO.FS.createDirAll parent
    IO.FS.writeFile outputPath (toJson projects).pretty
    IO.println s!"Exported {projects.size} theorem-map project environments"
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"theorem-map extractor failed: {error}"
    return (1 : UInt32)
