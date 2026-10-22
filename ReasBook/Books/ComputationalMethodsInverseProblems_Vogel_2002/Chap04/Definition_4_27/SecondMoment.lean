/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

public section

noncomputable section

open scoped ProbabilityTheory

namespace ProbabilityTheory

universe u v

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v}

/-- The autocorrelation matrix `Γ[X; μ]` of a real random vector, that is, the textbook
object `ΓXX` with entries given by the uncentered coordinate second moments
`∫ ω, X ω i * X ω j ∂μ`. -/
def secondMomentMatrix (μ : MeasureTheory.Measure Ω) (X : Ω → EuclideanSpace ℝ n) :
    Matrix n n ℝ :=
  fun i j ↦ ∫ ω, X ω i * X ω j ∂μ

/-- Scoped notation for the autocorrelation matrix `Γ[X; μ]` from Definition 4.27. -/
scoped notation "Γ[" X "; " μ "]" => secondMomentMatrix μ X

/-- The entries of `Γ[X; μ]` are the uncentered coordinate second moments
`∫ ω, X ω i * X ω j ∂μ`. -/
theorem secondMomentMatrix_apply
    {μ : MeasureTheory.Measure Ω} {X : Ω → EuclideanSpace ℝ n} (i j : n) :
    Γ[X; μ] i j = ∫ ω, X ω i * X ω j ∂μ := by
  simp [secondMomentMatrix]

/-- Transposing `Γ[X; μ]` does not change it. -/
theorem secondMomentMatrix_transpose
    {μ : MeasureTheory.Measure Ω} {X : Ω → EuclideanSpace ℝ n} :
    Matrix.transpose Γ[X; μ] = Γ[X; μ] := by
  ext i j
  simp [secondMomentMatrix, mul_comm]

end

end ProbabilityTheory
