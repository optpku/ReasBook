/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Example_2_60

universe u v
open ContinuousLinearMap
open InnerProductSpace
open scoped Gradient InnerProductSpace

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-
`_Probe260` is only a verification layer: the canonical least-squares residual API already lives in
`Example_2_60`, so this file reuses those declarations directly rather than restating them locally.
-/
example (L : H →L[ℝ] K) (r : K) (x : H) :
    HasGradientAt (leastSquaresResidual L r) ((2 : ℝ) • (L.adjoint (L x - r))) x := by
  exact leastSquaresResidual_hasGradientAt L r x

example (L : H →L[ℝ] K) (r : K) (x : H) :
    HasFDerivAt (leastSquaresResidual L r)
      (InnerProductSpace.toDual ℝ H ((2 : ℝ) • (L.adjoint (L x - r)))) x := by
  exact leastSquaresResidual_hasFDerivAt L r x

example (L : H →L[ℝ] K) (r : K) :
    ContDiff ℝ 2 (leastSquaresResidual L r) := by
  exact leastSquaresResidual_contDiff L r

example (L : H →L[ℝ] K) (r : K) (x : H) :
    HasFDerivAt (∇ (leastSquaresResidual L r)) ((2 : ℝ) • (L.adjoint.comp L)) x := by
  exact leastSquaresResidual_gradient_hasFDerivAt L r x

example (L : H →L[ℝ] K) (r : K) :
    ∇ (leastSquaresResidual L r) = fun x ↦ (2 : ℝ) • (L.adjoint (L x - r)) := by
  exact gradient_leastSquaresResidual L r
