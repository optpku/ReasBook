/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Algorithm_9_3_1.Iterates
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_9.CriticalPoint
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Exercise_9_7
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Prop_9_15.Projector

public section

noncomputable section

namespace NonnegativeOrthant

variable {n : ℕ}
variable {J : EuclideanSpace ℝ (Fin n) → ℝ}
variable {fStar : EuclideanSpace ℝ (Fin n)}

/-- Helper for Proposition 9.15: each coordinate of a critical point is fixed by
the positive-step orthant clipping formula. -/
private lemma criticalCoordinateMaxSubEqSelf
    (hcrit : IsCriticalPoint J fStar)
    (τ : ℝ)
    (hτ : 0 < τ)
    (i : Fin n) :
    max (fStar i - τ * gradient J fStar i) 0 = fStar i := by
  -- Split on whether the `i`-th gradient coordinate vanishes.
  by_cases hgrad0 : gradient J fStar i = 0
  · -- When the gradient coordinate is zero, the clipping formula reduces to feasibility.
    simpa [hgrad0] using (max_eq_left (hcrit.feasible i) : max (fStar i) 0 = fStar i)
  · -- Otherwise gradient nonnegativity upgrades to strict positivity, forcing `fStar i = 0`.
    have hgrad_pos : 0 < gradient J fStar i := by
      exact lt_of_le_of_ne (hcrit.gradientNonneg i) (by simpa [eq_comm] using hgrad0)
    have hfzero : fStar i = 0 := hcrit.eq_zero_of_gradient_pos hgrad_pos
    have hsub_nonpos : fStar i - τ * gradient J fStar i ≤ 0 := by
      rw [hfzero]
      exact sub_nonpos.mpr (mul_nonneg hτ.le hgrad_pos.le)
    simpa [hfzero] using
      (max_eq_right hsub_nonpos : max (fStar i - τ * gradient J fStar i) 0 = 0)

namespace IsCriticalPoint

/-- A critical point for the nonnegative-orthant problem is fixed by every
positive-step projected-gradient update built from `projector n`. -/
theorem update_eq_self
    (hcrit : IsCriticalPoint J fStar)
    (τ : ℝ)
    (hτ : 0 < τ) :
    GradientProjection.update (projector n) J τ fStar = fStar := by
  -- Rewrite the update into the projector form used in Proposition 9.15.
  rw [GradientProjection.update_eq_projector_sub_smul_gradient]
  -- Compare the two vectors coordinatewise through the orthant max formula.
  ext i
  rw [projector_apply_eq_max]
  exact criticalCoordinateMaxSubEqSelf hcrit τ hτ i

/-- A critical point for the nonnegative-orthant problem satisfies the fixed-point
equation of Proposition 9.15 for every positive step size. -/
theorem eq_projector_sub_smul_gradient
    (hcrit : IsCriticalPoint J fStar)
    (τ : ℝ)
    (hτ : 0 < τ) :
    fStar = projector n (fStar - τ • gradient J fStar) := by
  simpa [GradientProjection.update_eq_projector_sub_smul_gradient] using
    (hcrit.update_eq_self τ hτ).symm

end IsCriticalPoint

/-- Proposition 9.15. If `fStar` is a local minimizer of `(9.16)`, then for
every `τ > 0` one has
`fStar = projector n (fStar - τ • gradient J fStar)`. -/
theorem eq_projector_sub_smul_gradient_of_isLocalMinOn
    (hJ : ContDiff ℝ 1 J)
    (hfStar : fStar ∈ feasibleSet n)
    (hmin : IsLocalMinOn J (feasibleSet n) fStar)
    (τ : ℝ)
    (hτ : 0 < τ) :
    fStar = projector n (fStar - τ • gradient J fStar) :=
  (isCriticalPoint_of_isLocalMinOn hJ hfStar hmin).eq_projector_sub_smul_gradient τ hτ

end NonnegativeOrthant
