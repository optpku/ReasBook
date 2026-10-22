/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Cli
import DocGen4
import Lean

open DocGen4 DocGen4.DB Lean

private def readModules (path : String) : IO (Array Name) := do
  let source ← IO.FS.readFile path
  let mut modules := #[]
  for raw in source.splitOn "\n" do
    let module := raw.trimAscii.toString
    if !module.isEmpty then
      modules := modules.push module.toName
  if modules.isEmpty then
    throw <| IO.userError "project documentation module list is empty"
  return modules

/--
Analyze a bounded set of project modules in one Lean environment and append
their documentation data to doc-gen4's SQLite database.  External imports are
loaded so declarations elaborate correctly, but they are not analyzed or
written to the database.
-/
def main (args : List String) : IO UInt32 := do
  match args with
  | [buildDir, dbFile, moduleFile] =>
      let modules ← readModules moduleFile
      let doc ← load <| .analyzeConcreteModules modules
      updateModuleDb builtinDocstringValues doc buildDir dbFile none
      return 0
  | _ =>
      throw <| IO.userError
        "usage: ProjectDocsDatabase.lean BUILD_DIR DB_FILE MODULE_FILE"
