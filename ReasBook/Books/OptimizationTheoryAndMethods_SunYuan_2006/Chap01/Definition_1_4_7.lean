/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Example_2_57
import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic

-- Semantic recall hits verified for this item: `HasGradientAt`, `gradient`,
-- `DifferentiableAt.hasGradientAt`.

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Chapter01 Definition 1.4.7: a point `xStar` is a stationary (critical) point for `f` when
the Fréchet derivative of `f` vanishes at `xStar`. On complete spaces this is equivalent to the
usual gradient-zero formulation `HasGradientAt f 0 xStar`. -/
def IsStationaryPoint (f : E → ℝ) (xStar : E) : Prop :=
  HasFDerivAt f (0 : E →L[ℝ] ℝ) xStar

/-- `HasGradientVectorAt f g x` records that the derivative of `f` at `x` is represented by the
vector `g` through the Riesz map `InnerProductSpace.toDualMap ℝ E`. It is kept only as a thin
Fréchet-derivative bridge to the canonical `HasGradientAt` owner on complete inner-product
spaces. -/
def HasGradientVectorAt (f : E → ℝ) (g x : E) : Prop :=
  HasFDerivAt f (InnerProductSpace.toDualMap ℝ E g) x

/-- A stationary point gives the zero-derivative witness in Fréchet form. -/
theorem IsStationaryPoint.hasFDerivAt {f : E → ℝ} {xStar : E}
    (h : IsStationaryPoint f xStar) :
    HasFDerivAt f (0 : E →L[ℝ] ℝ) xStar :=
  h

/-- A stationary point is a point of differentiability. -/
theorem IsStationaryPoint.differentiableAt {f : E → ℝ} {xStar : E}
    (h : IsStationaryPoint f xStar) :
    DifferentiableAt ℝ f xStar :=
  h.hasFDerivAt.differentiableAt

/-- A gradient-vector witness gives the corresponding Fréchet derivative. -/
theorem HasGradientVectorAt.hasFDerivAt {f : E → ℝ} {g x : E}
    (h : HasGradientVectorAt f g x) :
    HasFDerivAt f (InnerProductSpace.toDualMap ℝ E g) x :=
  h

/-- A gradient-vector witness implies differentiability. -/
theorem HasGradientVectorAt.differentiableAt {f : E → ℝ} {g x : E}
    (h : HasGradientVectorAt f g x) :
    DifferentiableAt ℝ f x :=
  h.hasFDerivAt.differentiableAt

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- On complete inner-product spaces, `HasGradientVectorAt` is exactly the usual
`HasGradientAt` predicate. -/
theorem hasGradientAt_iff_hasGradientVectorAt {f : E → ℝ} {g x : E} :
    HasGradientAt f g x ↔ HasGradientVectorAt f g x := by
  rw [HasGradientVectorAt]
  simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply (𝕜 := ℝ) (E := E) g] using
    (hasGradientAt_iff_hasFDerivAt :
      HasGradientAt f g x ↔ HasFDerivAt f (InnerProductSpace.toDual ℝ E g) x)

/-- Unfolding criterion for stationary points: the source condition `∇ f (xStar) = 0` together
with differentiability at `xStar`. -/
theorem isStationaryPoint_iff (f : E → ℝ) (xStar : E) :
    IsStationaryPoint f xStar ↔
      gradient f xStar = 0 ∧ DifferentiableAt ℝ f xStar := by
  constructor
  · intro h
    have hGrad : HasGradientAt f 0 xStar := by
      exact (hasGradientAt_iff_hasGradientVectorAt).2 <| by
        simpa [HasGradientVectorAt, IsStationaryPoint] using h
    exact ⟨by simpa using hGrad.gradient, h.differentiableAt⟩
  · rintro ⟨hGradient, hDifferentiable⟩
    have hGrad : HasGradientAt f 0 xStar := by
      simpa [hGradient] using hDifferentiable.hasGradientAt
    simpa [HasGradientVectorAt, IsStationaryPoint] using
      ((hasGradientAt_iff_hasGradientVectorAt).1 hGrad)

/-- A stationary point gives the zero-gradient witness in the `HasGradientAt` sense. -/
theorem IsStationaryPoint.hasGradientAt {f : E → ℝ} {xStar : E}
    (h : IsStationaryPoint f xStar) :
    HasGradientAt f 0 xStar := by
  have hZero : HasGradientVectorAt f (0 : E) xStar := by
    simpa [HasGradientVectorAt, IsStationaryPoint] using h
  exact (hasGradientAt_iff_hasGradientVectorAt).2 hZero

/-- A stationary point has vanishing gradient. -/
theorem IsStationaryPoint.gradient_eq_zero {f : E → ℝ} {xStar : E}
    (h : IsStationaryPoint f xStar) :
    gradient f xStar = 0 := by
  simpa using h.hasGradientAt.gradient

end
