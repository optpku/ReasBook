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
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

-- Register doc-gen4's `docs` facet in this main project.
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.30.0"

require subverso from git "https://github.com/leanprover/subverso" @ "verso-v4.30.0"
require MD4Lean from git "https://github.com/acmepjz/md4lean" @ "main"

@[default_target]
lean_lib «ReasBook» where

-- Books from ALLBOOKS (sources live under Books/<LibName>/)
lean_lib ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017 where
  srcDir := "Books"
lean_lib CombinatorialGroupTheory_Magnus_2004 where
  srcDir := "Books"
lean_lib FirstOrderMethodsOptimization_Beck_2017 where
  srcDir := "Books"
lean_lib AlgebraicTopology_May_1999 where
  srcDir := "Books"
lean_lib RiemannSurfaces_Forster_1981 where
  srcDir := "Books"

-- Books living under Books/<LibName>/ with a Book.lean entry point
lean_lib Analysis2_Tao_2022 where
  srcDir := "Books"
lean_lib IntroductiontoRealAnalysisVolumeI_JiriLebl_2025 where
  srcDir := "Books"
lean_lib OptimizationTheoryAndMethods_SunYuan_2006 where
  srcDir := "Books"

-- Papers living under Papers/<LibName>/ with a Paper.lean entry point
lean_lib OnSomeLocalRings_Maassaran_2025 where
  srcDir := "Papers"
lean_lib SmoothMinimization_Nesterov_2004 where
  srcDir := "Papers"

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

lean_lib IntroductoryLecturesOnConvexOptimization_Nesterov_2004 where
  srcDir := "Books"
