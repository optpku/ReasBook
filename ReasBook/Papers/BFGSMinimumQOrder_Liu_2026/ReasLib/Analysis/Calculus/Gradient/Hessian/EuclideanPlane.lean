module

public import ReasLib.Analysis.Calculus.EuclideanPlaneHessian
public import ReasLib.Analysis.Calculus.Gradient.Hessian

public section

open scoped Matrix

namespace EuclideanPlane

/-- The Euclidean-plane Hessian agrees with the generic operator-valued Hessian on the
Euclidean plane. -/
theorem hessian_eq_genericHessian (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanPlane.hessian f x = _root_.hessian f x := by
  rw [EuclideanPlane.hessian_def, _root_.hessian_def]

/-- Pointwise operator-valued Hessian bounds are equivalent to the corresponding lower and
upper positive-semidefinite bounds on the Euclidean-plane Hessian matrix. -/
theorem hasHessianBoundsAt_iff_hessianMatrix
    {m M : ℝ} {f : EuclideanSpace ℝ (Fin 2) → ℝ} {x : EuclideanSpace ℝ (Fin 2)}
    (hf : ContDiffAt ℝ 2 f x) :
    HasHessianBoundsAt m M f x ↔
      (hessianMatrix f x - m • 1).PosSemidef ∧
        (M • 1 - hessianMatrix f x).PosSemidef := by
  constructor
  · intro h
    have hquad := h.quadraticForm
    constructor
    · rw [lowerBound_hessianMatrix_iff f x m hf]
      intro v
      rw [hessian_eq_genericHessian]
      exact (hquad v).1
    · rw [upperBound_hessianMatrix_iff f x M hf]
      intro v
      rw [hessian_eq_genericHessian]
      exact (hquad v).2
  · intro h
    have hlower := (lowerBound_hessianMatrix_iff f x m hf).mp h.1
    have hupper := (upperBound_hessianMatrix_iff f x M hf).mp h.2
    apply HasHessianBoundsAt.of_quadraticForm
    · exact _root_.hessian_isSelfAdjoint hf
    · intro v
      constructor
      · rw [← hessian_eq_genericHessian]
        exact hlower v
      · rw [← hessian_eq_genericHessian]
        exact hupper v

/-- Global operator-valued Hessian bounds are equivalent to pointwise lower and upper
positive-semidefinite bounds on every Euclidean-plane Hessian matrix. -/
theorem hasHessianBounds_iff_hessianMatrix
    {m M : ℝ} {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiff ℝ 2 f) :
    HasHessianBounds m M f ↔
      ∀ x, (hessianMatrix f x - m • 1).PosSemidef ∧
        (M • 1 - hessianMatrix f x).PosSemidef := by
  constructor
  · intro h x
    exact (hasHessianBoundsAt_iff_hessianMatrix hf.contDiffAt).mp (h.at x)
  · intro h
    apply HasHessianBounds.of_forall
    intro x
    exact (hasHessianBoundsAt_iff_hessianMatrix hf.contDiffAt).mpr (h x)

end EuclideanPlane
