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
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.2"

-- Register doc-gen4's `docs` facet in this main project.
-- Keep it aligned with the Lean/mathlib version used by the formalization.
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.32.2"

-- These revisions are the dependencies selected by Verso v4.32.0.
require subverso from git "https://github.com/leanprover/subverso" @ "0076a9e8a3670d83c54c93414b2b26d3a8aba08d"
require MD4Lean from git "https://github.com/acmepjz/md4lean" @ "31907cc18f48a95384f99cee5582c00fb39e0f67"

@[default_target]
lean_lib «ReasBook» where

/-- The TR-LALM formalization, stored under `Papers/` without changing its module names. -/
lean_lib «TR_LALM_theory» where
  srcDir := "Papers"
  roots := #[`TR_LALM_theory]

/-- BFGS minimum-Q-order formalization imported from the contributor repository. -/
lean_lib «BFGSMinimumQOrder_Liu_2026» where
  srcDir := "Papers/BFGSMinimumQOrder_Liu_2026"
  roots := #[`BFGSMinimumQOrder, `Book, `ReasLib, `DFPWolfe, `Paper]

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
