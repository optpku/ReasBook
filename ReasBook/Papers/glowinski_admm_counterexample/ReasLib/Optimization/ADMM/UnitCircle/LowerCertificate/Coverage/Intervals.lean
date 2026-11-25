/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Coverage.Generic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Coverage

/-- Exact pinned subdivision endpoints for the Diagonal certificate. -/
def diagonalCuts : Fin 8 → ℚ :=
  ![-1, (-3 / 4), (-1 / 2), 0, (1 / 2), (3 / 4), (7 / 8), 1]

theorem diagonal_cover {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ i : Fin 7, x ∈ Set.Icc ((diagonalCuts i.castSucc : ℚ) : ℝ)
      ((diagonalCuts i.succ : ℚ) : ℝ) := by
  apply interval_chain_cover 6 (fun i ↦ (diagonalCuts i : ℝ))
  · simpa [diagonalCuts] using hx.1
  · simpa [diagonalCuts] using hx.2

/-- Exact pinned subdivision endpoints for the StartDeterminant certificate. -/
def startDeterminantCuts : Fin 10 → ℚ :=
  ![-1, (-7 / 8), (-3 / 4), (-1 / 2), 0, (1 / 2), (3 / 4), (7 / 8), (15 / 16), 1]

theorem startDeterminant_cover {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ i : Fin 9, x ∈ Set.Icc ((startDeterminantCuts i.castSucc : ℚ) : ℝ)
      ((startDeterminantCuts i.succ : ℚ) : ℝ) := by
  apply interval_chain_cover 8 (fun i ↦ (startDeterminantCuts i : ℝ))
  · simpa [startDeterminantCuts] using hx.1
  · simpa [startDeterminantCuts] using hx.2

/-- Exact pinned subdivision endpoints for the LowerDeterminant certificate. -/
def lowerDeterminantCuts : Fin 25 → ℚ :=
  ![-1, (-31 / 32), (-15 / 16), (-7 / 8), (-3 / 4), (-23 / 32), (-91 / 128), (-45 / 64), (-11 / 16), (-5 / 8), (-1 / 2), 0, (1 / 2), (5 / 8), (11 / 16), (45 / 64), (91 / 128), (729 / 1024), (365 / 512), (183 / 256), (23 / 32), (3 / 4), (7 / 8), (15 / 16), 1]

theorem lowerDeterminant_cover {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ i : Fin 24, x ∈ Set.Icc ((lowerDeterminantCuts i.castSucc : ℚ) : ℝ)
      ((lowerDeterminantCuts i.succ : ℚ) : ℝ) := by
  apply interval_chain_cover 23 (fun i ↦ (lowerDeterminantCuts i : ℝ))
  · simpa [lowerDeterminantCuts] using hx.1
  · simpa [lowerDeterminantCuts] using hx.2

end ADMM.UnitCircle.LowerCertificate.Coverage
