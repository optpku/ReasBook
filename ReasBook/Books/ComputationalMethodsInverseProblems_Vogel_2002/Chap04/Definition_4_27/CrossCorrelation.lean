/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_27.SecondMoment

public section

noncomputable section

open scoped ProbabilityTheory

namespace ProbabilityTheory

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v}
variable {m : Type w}

/-- The cross-correlation matrix `Γ[X, Z; μ]` of real random vectors `X` and `Z`, that is, the
textbook object `ΓXZ`, is the rectangular matrix with entries `E (X_i * Z_j)`. -/
def crossCorrelationMatrix (μ : MeasureTheory.Measure Ω) (X : Ω → EuclideanSpace ℝ n)
    (Z : Ω → EuclideanSpace ℝ m) : Matrix n m ℝ :=
  fun i j ↦ ∫ ω, X ω i * Z ω j ∂μ

/-- Scoped notation for the cross-correlation matrix `Γ[X, Z; μ]` from Definition 4.27. -/
scoped notation "Γ[" X ", " Z "; " μ "]" => crossCorrelationMatrix μ X Z

/-- The entries of `Γ[X, Z; μ]` are `∫ ω, X ω i * Z ω j ∂μ`. -/
theorem crossCorrelationMatrix_apply
    {μ : MeasureTheory.Measure Ω} {X : Ω → EuclideanSpace ℝ n}
    {Z : Ω → EuclideanSpace ℝ m} (i : n) (j : m) :
    Γ[X, Z; μ] i j = ∫ ω, X ω i * Z ω j ∂μ := by
  simp [crossCorrelationMatrix]

/-- Swapping the random vectors transposes `Γ[X, Z; μ]`. -/
theorem crossCorrelationMatrix_transpose
    {μ : MeasureTheory.Measure Ω} {X : Ω → EuclideanSpace ℝ n}
    {Z : Ω → EuclideanSpace ℝ m} :
    Γ[Z, X; μ] = Matrix.transpose Γ[X, Z; μ] := by
  ext i j
  simp [crossCorrelationMatrix, mul_comm]

/-- The square self-case identifies `Γ[X, X; μ]` with `Γ[X; μ]`. -/
theorem crossCorrelationMatrix_self
    {μ : MeasureTheory.Measure Ω} {X : Ω → EuclideanSpace ℝ n} :
    Γ[X, X; μ] = Γ[X; μ] := by
  ext i j
  rw [crossCorrelationMatrix_apply, secondMomentMatrix_apply]

end

end ProbabilityTheory
