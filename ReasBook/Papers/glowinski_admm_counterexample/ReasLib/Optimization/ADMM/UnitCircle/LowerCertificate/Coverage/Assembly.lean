/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Coverage.Intervals
public import Mathlib.Tactic.FinCases
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.Diagonal
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.StartDeterminant
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.LowerDeterminant

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Coverage

/-- Verified finite gluing for the exact Diagonal subdivision. -/
theorem diagonal_positive_of_leaves
    (h00 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) ((-3 / 4) : ℝ) →
      0 < evaluate Data.Diagonal x)
    (h01 : ∀ x : ℝ, x ∈ Set.Icc ((-3 / 4) : ℝ) ((-1 / 2) : ℝ) →
      0 < evaluate Data.Diagonal x)
    (h02 : ∀ x : ℝ, x ∈ Set.Icc ((-1 / 2) : ℝ) (0 : ℝ) →
      0 < evaluate Data.Diagonal x)
    (h03 : ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) ((1 / 2) : ℝ) →
      0 < evaluate Data.Diagonal x)
    (h04 : ∀ x : ℝ, x ∈ Set.Icc ((1 / 2) : ℝ) ((3 / 4) : ℝ) →
      0 < evaluate Data.Diagonal x)
    (h05 : ∀ x : ℝ, x ∈ Set.Icc ((3 / 4) : ℝ) ((7 / 8) : ℝ) →
      0 < evaluate Data.Diagonal x)
    (h06 : ∀ x : ℝ, x ∈ Set.Icc ((7 / 8) : ℝ) (1 : ℝ) →
      0 < evaluate Data.Diagonal x)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : 0 < evaluate Data.Diagonal x := by
  obtain ⟨i, hi⟩ := diagonal_cover hx
  fin_cases i
  · exact h00 x (by simpa [diagonalCuts] using hi)
  · exact h01 x (by simpa [diagonalCuts] using hi)
  · exact h02 x (by simpa [diagonalCuts] using hi)
  · exact h03 x (by simpa [diagonalCuts] using hi)
  · exact h04 x (by simpa [diagonalCuts] using hi)
  · exact h05 x (by simpa [diagonalCuts] using hi)
  · exact h06 x (by simpa [diagonalCuts] using hi)

/-- Verified finite gluing for the exact StartDeterminant subdivision. -/
theorem startDeterminant_positive_of_leaves
    (h00 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) ((-7 / 8) : ℝ) →
      0 < evaluate Data.StartDeterminant x)
    (h01 : ∀ x : ℝ, x ∈ Set.Icc ((-7 / 8) : ℝ) ((-3 / 4) : ℝ) →
      0 < evaluate Data.StartDeterminant x)
    (h02 : ∀ x : ℝ, x ∈ Set.Icc ((-3 / 4) : ℝ) ((-1 / 2) : ℝ) →
      0 < evaluate Data.StartDeterminant x)
    (h03 : ∀ x : ℝ, x ∈ Set.Icc ((-1 / 2) : ℝ) (0 : ℝ) →
      0 < evaluate Data.StartDeterminant x)
    (h04 : ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) ((1 / 2) : ℝ) →
      0 < evaluate Data.StartDeterminant x)
    (h05 : ∀ x : ℝ, x ∈ Set.Icc ((1 / 2) : ℝ) ((3 / 4) : ℝ) →
      0 < evaluate Data.StartDeterminant x)
    (h06 : ∀ x : ℝ, x ∈ Set.Icc ((3 / 4) : ℝ) ((7 / 8) : ℝ) →
      0 < evaluate Data.StartDeterminant x)
    (h07 : ∀ x : ℝ, x ∈ Set.Icc ((7 / 8) : ℝ) ((15 / 16) : ℝ) →
      0 < evaluate Data.StartDeterminant x)
    (h08 : ∀ x : ℝ, x ∈ Set.Icc ((15 / 16) : ℝ) (1 : ℝ) →
      0 < evaluate Data.StartDeterminant x)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : 0 < evaluate Data.StartDeterminant x := by
  obtain ⟨i, hi⟩ := startDeterminant_cover hx
  fin_cases i
  · exact h00 x (by simpa [startDeterminantCuts] using hi)
  · exact h01 x (by simpa [startDeterminantCuts] using hi)
  · exact h02 x (by simpa [startDeterminantCuts] using hi)
  · exact h03 x (by simpa [startDeterminantCuts] using hi)
  · exact h04 x (by simpa [startDeterminantCuts] using hi)
  · exact h05 x (by simpa [startDeterminantCuts] using hi)
  · exact h06 x (by simpa [startDeterminantCuts] using hi)
  · exact h07 x (by simpa [startDeterminantCuts] using hi)
  · exact h08 x (by simpa [startDeterminantCuts] using hi)

/-- Verified finite gluing for the exact LowerDeterminant subdivision. -/
theorem lowerDeterminant_positive_of_leaves
    (h00 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) ((-31 / 32) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h01 : ∀ x : ℝ, x ∈ Set.Icc ((-31 / 32) : ℝ) ((-15 / 16) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h02 : ∀ x : ℝ, x ∈ Set.Icc ((-15 / 16) : ℝ) ((-7 / 8) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h03 : ∀ x : ℝ, x ∈ Set.Icc ((-7 / 8) : ℝ) ((-3 / 4) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h04 : ∀ x : ℝ, x ∈ Set.Icc ((-3 / 4) : ℝ) ((-23 / 32) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h05 : ∀ x : ℝ, x ∈ Set.Icc ((-23 / 32) : ℝ) ((-91 / 128) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h06 : ∀ x : ℝ, x ∈ Set.Icc ((-91 / 128) : ℝ) ((-45 / 64) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h07 : ∀ x : ℝ, x ∈ Set.Icc ((-45 / 64) : ℝ) ((-11 / 16) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h08 : ∀ x : ℝ, x ∈ Set.Icc ((-11 / 16) : ℝ) ((-5 / 8) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h09 : ∀ x : ℝ, x ∈ Set.Icc ((-5 / 8) : ℝ) ((-1 / 2) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h10 : ∀ x : ℝ, x ∈ Set.Icc ((-1 / 2) : ℝ) (0 : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h11 : ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) ((1 / 2) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h12 : ∀ x : ℝ, x ∈ Set.Icc ((1 / 2) : ℝ) ((5 / 8) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h13 : ∀ x : ℝ, x ∈ Set.Icc ((5 / 8) : ℝ) ((11 / 16) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h14 : ∀ x : ℝ, x ∈ Set.Icc ((11 / 16) : ℝ) ((45 / 64) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h15 : ∀ x : ℝ, x ∈ Set.Icc ((45 / 64) : ℝ) ((91 / 128) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h16 : ∀ x : ℝ, x ∈ Set.Icc ((91 / 128) : ℝ) ((729 / 1024) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h17 : ∀ x : ℝ, x ∈ Set.Icc ((729 / 1024) : ℝ) ((365 / 512) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h18 : ∀ x : ℝ, x ∈ Set.Icc ((365 / 512) : ℝ) ((183 / 256) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h19 : ∀ x : ℝ, x ∈ Set.Icc ((183 / 256) : ℝ) ((23 / 32) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h20 : ∀ x : ℝ, x ∈ Set.Icc ((23 / 32) : ℝ) ((3 / 4) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h21 : ∀ x : ℝ, x ∈ Set.Icc ((3 / 4) : ℝ) ((7 / 8) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h22 : ∀ x : ℝ, x ∈ Set.Icc ((7 / 8) : ℝ) ((15 / 16) : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    (h23 : ∀ x : ℝ, x ∈ Set.Icc ((15 / 16) : ℝ) (1 : ℝ) →
      0 < evaluate Data.LowerDeterminant x)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : 0 < evaluate Data.LowerDeterminant x := by
  obtain ⟨i, hi⟩ := lowerDeterminant_cover hx
  fin_cases i
  · exact h00 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h01 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h02 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h03 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h04 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h05 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h06 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h07 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h08 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h09 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h10 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h11 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h12 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h13 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h14 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h15 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h16 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h17 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h18 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h19 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h20 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h21 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h22 x (by simpa [lowerDeterminantCuts] using hi)
  · exact h23 x (by simpa [lowerDeterminantCuts] using hi)

end ADMM.UnitCircle.LowerCertificate.Coverage
