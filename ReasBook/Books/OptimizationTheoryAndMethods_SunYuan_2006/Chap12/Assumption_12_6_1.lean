/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

noncomputable section

open Filter

section

-- Semantic recall: `lean_leansearch` surfaced generic injectivity/rank lemmas for full-column-
-- rank maps, while nearby Chapter 12 files use `ContinuousLinearMap.adjoint` for formulas of
-- the form `A(x)ᵀ d = 0`. This item therefore keeps the source assumptions as three atomic
-- direct Prop-valued declarations on the continuous-linear-map surface.

section Convergence

variable {Point : Type*} [TopologicalSpace Point]

/-- Chapter12 Assumption 12.6.1 (1): the SQP iterates `x k` converge to the limit point
`xStar`. -/
abbrev secondOrderCorrectionIteratesConverge
    (x : ℕ → Point) (xStar : Point) : Prop :=
  Tendsto x atTop (nhds xStar)

/-- Unfolding `secondOrderCorrectionIteratesConverge x xStar` gives the convergence condition
`Tendsto x atTop (nhds xStar)`. -/
theorem secondOrderCorrectionIteratesConverge_iff
    (x : ℕ → Point) (xStar : Point) :
    secondOrderCorrectionIteratesConverge x xStar ↔
      Tendsto x atTop (nhds xStar) := Iff.rfl

end Convergence

section FullColumnRank

variable {Point Multiplier : Type*}
variable [NormedAddCommGroup Point] [NormedSpace ℝ Point]
variable [NormedAddCommGroup Multiplier] [NormedSpace ℝ Multiplier]

/-- Chapter12 Assumption 12.6.1 (2): the active-constraint Jacobian `A(xStar)` has full column
rank, encoded as injectivity of the continuous linear map `A xStar`. -/
abbrev secondOrderCorrectionJacobianHasFullColumnRankAt
    (A : Point → Multiplier →L[ℝ] Point) (xStar : Point) : Prop :=
  Function.Injective (A xStar)

/-- Unfolding `secondOrderCorrectionJacobianHasFullColumnRankAt A xStar` gives the injectivity
condition expressing that `A xStar` has full column rank. -/
theorem secondOrderCorrectionJacobianHasFullColumnRankAt_iff
    (A : Point → Multiplier →L[ℝ] Point) (xStar : Point) :
    secondOrderCorrectionJacobianHasFullColumnRankAt A xStar ↔
      Function.Injective (A xStar) := Iff.rfl

/-- Under the full-column-rank hypothesis at `xStar`, any vector in the kernel of `A xStar`
must vanish. -/
theorem secondOrderCorrectionJacobianHasFullColumnRankAt.eq_zero_of_apply_eq_zero
    {A : Point → Multiplier →L[ℝ] Point} {xStar : Point}
    (hAstar : secondOrderCorrectionJacobianHasFullColumnRankAt A xStar)
    {y : Multiplier} (hy : A xStar y = 0) :
    y = 0 :=
  hAstar (by simpa using hy)

end FullColumnRank

section UniformBounds

variable {Point Multiplier : Type*}
variable [NormedAddCommGroup Point] [InnerProductSpace ℝ Point] [CompleteSpace Point]
variable [NormedAddCommGroup Multiplier] [InnerProductSpace ℝ Multiplier]
  [CompleteSpace Multiplier]

/-- `IsSecondOrderCorrectionUniformModelBounds x A B mBar MBar` records the source uniform
operator-norm and nullspace-curvature conditions for fixed positive constants `mBar` and
`MBar`. -/
class IsSecondOrderCorrectionUniformModelBounds
    (x : ℕ → Point)
    (A : Point → Multiplier →L[ℝ] Point)
    (B : ℕ → Point →L[ℝ] Point)
    (mBar MBar : ℝ) : Prop where
  mBar_pos : 0 < mBar
  MBar_pos : 0 < MBar
  operator_norm_le (k : ℕ) : ‖B k‖ ≤ MBar
  nullspace_curvature_le (k : ℕ) (d : Point) :
    (A (x k)).adjoint d = 0 →
      mBar * ‖d‖ ^ (2 : ℕ) ≤ inner ℝ d (B k d)

/-- Unfolding `IsSecondOrderCorrectionUniformModelBounds x A B mBar MBar` gives the fixed-constant
uniform operator-norm and nullspace-curvature conditions from the source assumption. -/
theorem isSecondOrderCorrectionUniformModelBounds_iff
    (x : ℕ → Point)
    (A : Point → Multiplier →L[ℝ] Point)
    (B : ℕ → Point →L[ℝ] Point)
    (mBar MBar : ℝ) :
    IsSecondOrderCorrectionUniformModelBounds x A B mBar MBar ↔
      0 < mBar ∧
        0 < MBar ∧
        (∀ k : ℕ, ‖B k‖ ≤ MBar) ∧
        ∀ k : ℕ, ∀ d : Point,
          (A (x k)).adjoint d = 0 →
            mBar * ‖d‖ ^ (2 : ℕ) ≤ inner ℝ d (B k d) := by
  constructor
  · intro h
    exact ⟨h.mBar_pos, h.MBar_pos, h.operator_norm_le, h.nullspace_curvature_le⟩
  · rintro ⟨hmBar, hMBar, hNorm, hCurvature⟩
    exact ⟨hmBar, hMBar, hNorm, hCurvature⟩

/-- Chapter12 Assumption 12.6.1 (3): there exist positive constants `mBar` and `MBar` such
that `‖B k‖ ≤ MBar` for every `k`, and for every `k` and every direction `d` satisfying
`A(x_k)ᵀ d = 0`, the nullspace curvature bound
`mBar * ‖d‖^2 ≤ ⟪d, B_k d⟫` holds. -/
abbrev secondOrderCorrectionUniformModelBounds
    (x : ℕ → Point)
    (A : Point → Multiplier →L[ℝ] Point)
    (B : ℕ → Point →L[ℝ] Point) : Prop :=
  ∃ mBar MBar : ℝ, IsSecondOrderCorrectionUniformModelBounds x A B mBar MBar

/-- Unfolding `secondOrderCorrectionUniformModelBounds x A B` gives the existence of positive
uniform bounds `mBar` and `MBar` with the source operator-norm and nullspace-curvature
inequalities. -/
theorem secondOrderCorrectionUniformModelBounds_iff
    (x : ℕ → Point)
    (A : Point → Multiplier →L[ℝ] Point)
    (B : ℕ → Point →L[ℝ] Point) :
    secondOrderCorrectionUniformModelBounds x A B ↔
      ∃ mBar MBar : ℝ,
        0 < mBar ∧
          0 < MBar ∧
          (∀ k : ℕ, ‖B k‖ ≤ MBar) ∧
          ∀ k : ℕ, ∀ d : Point,
            (A (x k)).adjoint d = 0 →
              mBar * ‖d‖ ^ (2 : ℕ) ≤ inner ℝ d (B k d) := by
  constructor
  · rintro ⟨mBar, MBar, hBounds⟩
    rw [isSecondOrderCorrectionUniformModelBounds_iff] at hBounds
    exact ⟨mBar, MBar, hBounds⟩
  · rintro ⟨mBar, MBar, hBounds⟩
    exact ⟨mBar, MBar, (isSecondOrderCorrectionUniformModelBounds_iff x A B mBar MBar).2 hBounds⟩

/-- A source-uniform bound assumption yields explicit constants `mBar, MBar` together with their
positivity, operator-norm bounds, and nullspace-curvature inequalities. -/
theorem secondOrderCorrectionUniformModelBounds.exists_spec
    {x : ℕ → Point}
    {A : Point → Multiplier →L[ℝ] Point}
    {B : ℕ → Point →L[ℝ] Point}
    (h : secondOrderCorrectionUniformModelBounds x A B) :
    ∃ mBar MBar : ℝ,
      0 < mBar ∧
        0 < MBar ∧
        (∀ k : ℕ, ‖B k‖ ≤ MBar) ∧
        ∀ k : ℕ, ∀ d : Point,
          (A (x k)).adjoint d = 0 →
            mBar * ‖d‖ ^ (2 : ℕ) ≤ inner ℝ d (B k d) :=
  (secondOrderCorrectionUniformModelBounds_iff x A B).1 h

end UniformBounds

end
