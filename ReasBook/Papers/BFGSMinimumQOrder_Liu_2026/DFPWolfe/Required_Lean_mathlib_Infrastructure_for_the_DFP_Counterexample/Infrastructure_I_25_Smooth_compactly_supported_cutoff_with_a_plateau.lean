module

public import ReasLib.Analysis.Calculus.EuclideanPlaneSmoothCutoff

public section

open Set
open scoped ContDiff

/- Infrastructure I.25 (Smooth compactly supported cutoff with a plateau):
the selected cutoff on the real Euclidean plane. -/
#check (EuclideanPlane.smoothCutoff : EuclideanSpace ℝ (Fin 2) → ℝ)

#check (EuclideanPlane.contDiff_smoothCutoff :
  ContDiff ℝ ∞ EuclideanPlane.smoothCutoff)

#check (EuclideanPlane.hasCompactSupport_smoothCutoff :
  HasCompactSupport EuclideanPlane.smoothCutoff)

#check (EuclideanPlane.tsupport_smoothCutoff_subset :
  tsupport EuclideanPlane.smoothCutoff ⊆ Metric.ball 0 1)

#check (EuclideanPlane.smoothCutoff_eq_one :
  ∀ (x : EuclideanSpace ℝ (Fin 2)),
    x ∈ Metric.closedBall 0 (1 / 3 : ℝ) → EuclideanPlane.smoothCutoff x = 1)

#check (EuclideanPlane.smoothCutoffDerivBound : ℕ → ℝ)

#check (EuclideanPlane.smoothCutoffDerivBound_nonneg :
  ∀ n : ℕ, 0 ≤ EuclideanPlane.smoothCutoffDerivBound n)

#check (EuclideanPlane.norm_iteratedFDeriv_smoothCutoff_le :
  ∀ (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)),
    ‖iteratedFDeriv ℝ n EuclideanPlane.smoothCutoff x‖ ≤
      EuclideanPlane.smoothCutoffDerivBound n)

#check (EuclideanPlane.norm_smoothCutoff_le :
  ∀ x : EuclideanSpace ℝ (Fin 2),
    ‖EuclideanPlane.smoothCutoff x‖ ≤ EuclideanPlane.smoothCutoffDerivBound 0)

#check (EuclideanPlane.norm_fderiv_smoothCutoff_le :
  ∀ x : EuclideanSpace ℝ (Fin 2),
    ‖fderiv ℝ EuclideanPlane.smoothCutoff x‖ ≤
      EuclideanPlane.smoothCutoffDerivBound 1)

#check (EuclideanPlane.norm_secondFDeriv_smoothCutoff_le :
  ∀ x : EuclideanSpace ℝ (Fin 2),
    ‖fderiv ℝ (fderiv ℝ EuclideanPlane.smoothCutoff) x‖ ≤
      EuclideanPlane.smoothCutoffDerivBound 2)
