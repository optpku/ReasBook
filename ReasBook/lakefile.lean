import Lake
open Lake DSL

package «ReasBook» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩,
    ⟨`weak.linter.style.longLine, false⟩,
    ⟨`weak.linter.style.emptyLine, false⟩,
    ⟨`weak.linter.style.cdot, false⟩,
    ⟨`weak.linter.style.maxHeartbeats, false⟩,
    ⟨`weak.linter.unnecessarySimpa, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.0"

-- Register doc-gen4's `docs` facet in this main project.
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.32.0"

require subverso from git "https://github.com/leanprover/subverso" @ "verso-v4.32.0"
require MD4Lean from git "https://github.com/acmepjz/md4lean" @ "main"

@[default_target]
lean_lib «ReasBook» where

-- Books from ALLBOOKS (sources live under Books/<LibName>/)
-- lean_lib ComputationalMethodsInverseProblems_Vogel_2002 where
--   srcDir := "Books"
-- (Vogel book commented out: 57 mathlib v4.32.0 API incompatibilities;
--  needs contributor adaptation.)

/-- Reusable infrastructure for the DFP Wolfe counterexample formalization. -/
lean_lib «DFP_wolfe_ReasLib» where
  srcDir := "Papers/DFP_wolfe_local"
  roots := #[`ReasLib]

/-- Paper-facing modules for the DFP Wolfe counterexample formalization. -/
lean_lib «DFP_wolfe_DFPWolfe» where
  srcDir := "Papers/DFP_wolfe_local"
  roots := #[`DFPWolfe]

/-- The ReasBook entry point for the DFP Wolfe counterexample formalization. -/
lean_lib «DFP_wolfe_local» where
  srcDir := "Papers"
  roots := #[`DFP_wolfe_local.Paper]

/-- The counterexample on c₀, with project-prefixed modules to coexist with DFP. -/
lean_lib «RockafellarSum_2026» where
  srcDir := "Papers"
  roots := #[`RockafellarSum_2026.Paper]
  globs := #[.submodules `RockafellarSum_2026]

lean_exe "literate-extract" where
  root := `LiterateExtract
  supportInterpreter := true

module_facet literate mod : System.FilePath := do
  let ws ← getWorkspace

  let exeJob ← «literate-extract».fetch
  let modJob ← mod.olean.fetch

  let buildDir := ws.root.buildDir
  let hlFile := mod.filePath (buildDir / "literate") "json"

  exeJob.bindM fun exeFile =>
    modJob.mapM fun _oleanPath => do
      buildFileUnlessUpToDate' (text := true) hlFile <|
        proc {
          cmd := exeFile.toString
          args :=  #[mod.name.toString, hlFile.toString]
          env := ← getAugmentedEnv
        }
      pure hlFile

library_facet literate lib : Array System.FilePath := do
  let mods ← (← lib.modules.fetch).await
  let modJobs ← mods.mapM (·.facet `literate |>.fetch)
  let out ← modJobs.mapM (·.await)
  pure (.pure out)
