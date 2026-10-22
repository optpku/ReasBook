/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Cli
import DocGen4
import Lean

open DocGen4 Lean

private def readMappings (path : String) : IO (Array (Name × String)) := do
  let source ← IO.FS.readFile path
  let mut mappings := #[]
  for raw in source.splitOn "\n" do
    if raw.isEmpty then
      continue
    match raw.splitOn "\t" with
    | [module, sourceUrl] =>
        if module.isEmpty || sourceUrl.isEmpty then
          throw <| IO.userError "project documentation mapping is incomplete"
        mappings := mappings.push (module.toName, sourceUrl)
    | _ =>
        throw <| IO.userError "invalid project documentation mapping"
  if mappings.isEmpty then
    throw <| IO.userError "project documentation mapping is empty"
  return mappings

/--
Load one project's module closure once, then render each module with its own
immutable source URL.  This adapter is for pre-database doc-gen4 releases.
-/
def main (args : List String) : IO UInt32 := do
  match args with
  | [buildDir, mappingFile] =>
      let mappings ← readMappings mappingFile
      let modules := mappings.map fun entry => entry.1
      let (doc, hierarchy) ← load <| .analyzeConcreteModules modules
      let baseConfig ← getSimpleBaseContext buildDir hierarchy
      for (module, sourceUrl) in mappings do
        let moduleInfo := doc.moduleInfo[module]!
        let selected : Std.HashMap Name Process.Module :=
          Std.HashMap.emptyWithCapacity 1 |>.insert module moduleInfo
        let selectedDoc : Process.AnalyzerResult := {
          doc with moduleInfo := selected
        }
        discard <| htmlOutputResults baseConfig selectedDoc (some sourceUrl)
      return 0
  | _ =>
      throw <| IO.userError
        "usage: ProjectDocsLegacy.lean BUILD_DIR MAPPING_FILE"
