/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_3

public section

open scoped Matrix.Energy

namespace Matrix

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Exercise 3.4. For an SPD matrix `A`, the energy norm is bounded between the
Euclidean norm scaled by the square roots of the smallest and largest spectral
values. In the Chapter 3 formalization, the book's `λ_min(A)` and `λ_max(A)`
are represented by `sInf (spectrum ℝ A)` and `sSup (spectrum ℝ A)`. -/
theorem energyNorm_spectralBounds (A : Matrix n n ℝ) (hA : A.PosDef)
    (f : EuclideanSpace ℝ n) :
    Real.sqrt (sInf (spectrum ℝ A)) * ‖f‖ ≤ ‖f‖_[A, hA] ∧
      ‖f‖_[A, hA] ≤ Real.sqrt (sSup (spectrum ℝ A)) * ‖f‖ := by
  exact ⟨A.energyNorm_lowerBound hA f, A.energyNorm_upperBound hA f⟩

end Matrix
