/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_5.Filters
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_9.Scaling
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

public section

noncomputable section

namespace ContinuousLinearMap.SingularSystem

universe u v

variable {H₁ : Type u} {H₂ : Type v}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
variable {K : H₁ →L[ℝ] H₂}

/-- The generalized Fourier coefficients of `fTrue` along the right singular
vectors of `S`, indexed by positive integers with `i = 1` corresponding to the
first singular mode. -/
@[expose]
def generalizedFourierCoefficientSequence
    (S : SingularSystem K) (h_length : S.length = ⊤) (fTrue : H₁) : ℕ+ → ℝ :=
  fun i ↦ inner ℝ (S.rightBasis (S.positiveIndex h_length i) : H₁) fTrue

@[simp] theorem generalizedFourierCoefficientSequence_apply
    (S : SingularSystem K) (h_length : S.length = ⊤) (fTrue : H₁) (i : ℕ+) :
    S.generalizedFourierCoefficientSequence h_length fTrue i =
      inner ℝ (S.rightBasis (S.natIndex h_length i.natPred) : H₁) fTrue := by
  simp [generalizedFourierCoefficientSequence]

/-- The generalized Fourier coefficients of `fTrue` along the right singular
vectors of `S` satisfy the Chapter 7 algebraic square-decay law from `(7.53)`. -/
abbrev HasAlgebraicFourierCoefficientSquareDecay
    (S : SingularSystem K) (h_length : S.length = ⊤) (fTrue : H₁)
    (b q : ℝ) : Prop :=
  ∀ i : ℕ+,
    S.generalizedFourierCoefficientSequence h_length fTrue i ^ 2 =
      b * (i : ℝ) ^ (-q)

@[simp] theorem hasAlgebraicFourierCoefficientSquareDecay_iff
    (S : SingularSystem K) (h_length : S.length = ⊤) (fTrue : H₁) (b q : ℝ) :
    S.HasAlgebraicFourierCoefficientSquareDecay h_length fTrue b q ↔
      ∀ i : ℕ+,
        S.generalizedFourierCoefficientSequence h_length fTrue i ^ 2 =
          b * (i : ℝ) ^ (-q) :=
  Iff.rfl

/-- The singular-system filter series with scalar filter `w` applied to the
datum `g`. -/
@[expose]
def filterSeries
    (S : SingularSystem K) (w : ℝ → ℝ) (g : H₂) : S.Index → H₁ :=
  fun j ↦
    (((w (S.singularValue j ^ 2) / S.singularValue j) *
        inner ℝ (S.leftBasis j : H₂) g) •
      (S.rightBasis j : H₁))

@[simp] theorem filterSeries_apply
    (S : SingularSystem K) (w : ℝ → ℝ) (g : H₂) (j : S.Index) :
    S.filterSeries w g j =
      (((w (S.singularValue j ^ 2) / S.singularValue j) *
          inner ℝ (S.leftBasis j : H₂) g) •
        (S.rightBasis j : H₁)) :=
  rfl

/-- A reconstruction operator `R` has the Chapter 7 filter-series
representation relative to `S` with scalar filter `w`. -/
abbrev HasFilterRepresentation
    (S : SingularSystem K) (w : ℝ → ℝ) (R : H₂ →L[ℝ] H₁) : Prop :=
  ∀ g : H₂, HasSum (S.filterSeries w g) (R g)

@[simp] theorem hasFilterRepresentation_iff
    (S : SingularSystem K) (w : ℝ → ℝ) (R : H₂ →L[ℝ] H₁) :
    S.HasFilterRepresentation w R ↔
      ∀ g : H₂, HasSum (S.filterSeries w g) (R g) :=
  Iff.rfl

/-- The reconstruction operator `R` has the Tikhonov filter-series
representation `(7.36)` relative to `S`. -/
abbrev HasTikhonovFilterRepresentation
    (S : SingularSystem K) (α : ℝ) (R : H₂ →L[ℝ] H₁) : Prop :=
  S.HasFilterRepresentation (SpectralFilter.tikhonov α) R

@[simp] theorem hasTikhonovFilterRepresentation_iff
    (S : SingularSystem K) (α : ℝ) (R : H₂ →L[ℝ] H₁) :
    S.HasTikhonovFilterRepresentation α R ↔
      ∀ g : H₂,
        HasSum (S.filterSeries (SpectralFilter.tikhonov α) g) (R g) :=
  Iff.rfl

/-- Evaluate a filter-series representation on a specific datum. -/
theorem HasFilterRepresentation.hasSum
    {S : SingularSystem K} {w : ℝ → ℝ} {R : H₂ →L[ℝ] H₁}
    (hR : S.HasFilterRepresentation w R) (g : H₂) :
    HasSum (S.filterSeries w g) (R g) :=
  hR g

/-- Evaluate a Tikhonov filter-series representation on a specific datum. -/
theorem HasTikhonovFilterRepresentation.hasSum
    {S : SingularSystem K} {α : ℝ} {R : H₂ →L[ℝ] H₁}
    (hR : S.HasTikhonovFilterRepresentation α R) (g : H₂) :
    HasSum (S.filterSeries (SpectralFilter.tikhonov α) g) (R g) :=
  hR g

end ContinuousLinearMap.SingularSystem
