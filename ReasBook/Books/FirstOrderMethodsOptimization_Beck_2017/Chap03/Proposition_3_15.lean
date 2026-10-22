/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open InnerProductSpace (toDualMap)
open Metric
open scoped Gradient

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Proposition 3.15 is `source-facing`: the book states the Euclidean subdifferential as a subset of
`ℝ^n`, so the main declaration should use the chapter Euclidean bridge/view owner
`euclideanSubdifferentialAt`. The continuous-dual owner `subdifferentialAt` remains upstream in
Theorem 3.4 and should only appear through derived bridge lemmas, not as the main public surface
of this proposition.
-/

-- Proof sketch: for `x = 0`, this is Proposition 3.1 specialized to Euclidean space. For
-- `x ≠ 0`, the Euclidean norm is differentiable at `x`, so Theorem 3.13 identifies the owner
-- dual subdifferential with the Riesz functional of the normalized vector, and transporting back
-- along `toDualMap` gives the vector-side singleton `{(‖x‖⁻¹) • x}`.
/-- Helper for Proposition 3.15: membership in the Euclidean norm subdifferential at the origin is
equivalent to the Euclidean norm bound `‖z‖ ≤ 1`. -/
lemma mem_euclideanSubdifferentialAt_l2_norm_zero_iff_norm_le_one
    {z : E} :
    z ∈ euclideanSubdifferentialAt (fun y : E ↦ ‖y‖) (0 : E) ↔ ‖z‖ ≤ 1 := by
  -- Transport the owner-side norm criterion from Proposition 3.1 across the Euclidean bridge.
  rw [mem_euclideanSubdifferentialAt_iff]
  simpa [subdifferentialAt] using
    (mem_strongDualSubdifferential_norm_zero_iff (g := toDualMap ℝ E z))

/-- Helper for Proposition 3.15: away from the origin, the Euclidean gradient of
`x ↦ ‖x‖` is the normalized vector `‖x‖⁻¹ • x`. -/
lemma gradient_l2_norm_eq_inv_smul {x : E} (hx : x ≠ 0) :
    ∇ (fun y : E ↦ ‖y‖) x = ‖x‖⁻¹ • x := by
  have hdiff : DifferentiableAt ℝ (fun y : E ↦ ‖y‖) x :=
    (contDiffAt_norm (𝕜 := ℝ) (n := 1) hx).differentiableAt one_ne_zero
  have hnormx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hnormalized_norm : ‖‖x‖⁻¹ • x‖ = 1 := by
    -- Normalize the scalar factor first so the unit-vector equality criterion applies cleanly.
    calc
      ‖‖x‖⁻¹ • x‖ = |‖x‖⁻¹| * ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ = ‖x‖⁻¹ * ‖x‖ := by
        rw [abs_of_nonneg]
        exact inv_nonneg.mpr (norm_nonneg x)
      _ = 1 := by
        rw [inv_mul_cancel₀ hnormx]
  have hgrad_norm_le : ‖∇ (fun y : E ↦ ‖y‖) x‖ ≤ 1 := by
    -- The gradient norm matches the derivative norm under the Riesz isometry, and the norm map is
    -- globally `1`-Lipschitz.
    calc
      ‖∇ (fun y : E ↦ ‖y‖) x‖ = ‖toDualMap ℝ E (∇ (fun y : E ↦ ‖y‖) x)‖ := by
        exact ((toDualMap ℝ E).norm_map (∇ (fun y : E ↦ ‖y‖) x)).symm
      _ = ‖fderiv ℝ (fun y : E ↦ ‖y‖) x‖ := by
        congr 1
        ext y
        simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using
          (hdiff.hasGradientAt.fderiv_apply (y := y)).symm
      _ ≤ 1 := by
        exact
          (norm_fderiv_le_of_lipschitz ℝ
            (f := fun y : E ↦ ‖y‖) (x₀ := x) lipschitzWith_one_norm)
  have hinner : inner ℝ (∇ (fun y : E ↦ ‖y‖) x) (‖x‖⁻¹ • x) = 1 := by
    -- Evaluate the derivative along the normalized direction and simplify with
    -- `DifferentiableAt.fderiv_norm_self`.
    calc
      inner ℝ (∇ (fun y : E ↦ ‖y‖) x) (‖x‖⁻¹ • x)
          = fderiv ℝ (fun y : E ↦ ‖y‖) x (‖x‖⁻¹ • x) := by
              simpa using
                (inner_gradient_left (𝕜 := ℝ) (f := fun y : E ↦ ‖y‖)
                  (x := x) (y := ‖x‖⁻¹ • x) hdiff)
      _ = ‖x‖⁻¹ * fderiv ℝ (fun y : E ↦ ‖y‖) x x := by
        rw [ContinuousLinearMap.map_smul]
        simp [smul_eq_mul]
      _ = ‖x‖⁻¹ * ‖x‖ := by
        rw [hdiff.fderiv_norm_self]
      _ = 1 := by
        rw [inv_mul_cancel₀ hnormx]
  have hgrad_norm_eq : ‖∇ (fun y : E ↦ ‖y‖) x‖ = 1 := by
    have hgrad_norm_ge : 1 ≤ ‖∇ (fun y : E ↦ ‖y‖) x‖ := by
      have hcs :
          inner ℝ (∇ (fun y : E ↦ ‖y‖) x) (‖x‖⁻¹ • x) ≤
            ‖∇ (fun y : E ↦ ‖y‖) x‖ * ‖‖x‖⁻¹ • x‖ := by
        simpa using real_inner_le_norm (∇ (fun y : E ↦ ‖y‖) x) (‖x‖⁻¹ • x)
      rw [hinner, hnormalized_norm, mul_one] at hcs
      exact hcs
    linarith
  -- Equality in Cauchy-Schwarz identifies the two unit vectors.
  exact (inner_eq_one_iff_of_norm_eq_one hgrad_norm_eq hnormalized_norm).mp hinner

/-- Proposition 3.15: for the Euclidean norm on `ℝ^n`, the Euclidean/vector-side
subdifferential is the singleton containing the normalized vector `(1 / ‖x‖) • x` away from the
origin, and it is the closed Euclidean unit ball at the origin. -/
theorem euclidean_subdifferentialAt_l2_norm_eq_piecewise (x : E) :
    euclideanSubdifferentialAt (fun y : E ↦ ‖y‖) x =
      if x = 0 then
        closedBall (0 : E) 1
      else
        {‖x‖⁻¹ • x} := by
  by_cases hx : x = 0
  · subst x
    -- At the origin, rewrite both sides to the same norm-bound membership condition.
    ext z
    simpa [Metric.mem_closedBall, dist_eq_norm] using
      (mem_euclideanSubdifferentialAt_l2_norm_zero_iff_norm_le_one (z := z))
  · -- Away from the origin, Proposition 3.14 reduces the subdifferential to the singleton of the
    -- gradient, and the explicit gradient formula supplies the normalized vector.
    have hdiff : DifferentiableAt ℝ (fun y : E ↦ ‖y‖) x :=
      (contDiffAt_norm (𝕜 := ℝ) (n := 1) hx).differentiableAt one_ne_zero
    rw [if_neg hx]
    simpa [gradient_l2_norm_eq_inv_smul hx] using
      (euclideanSubdifferentialAt_eq_singleton_gradient_of_differentiableAt
        (f := fun y : E ↦ ‖y‖) convexOn_univ_norm hdiff)

/-- At the origin, Proposition 3.15 identifies the Euclidean/vector-side norm subdifferential
with the closed Euclidean unit ball. -/
@[simp] theorem euclidean_subdifferentialAt_l2_norm_zero_eq_closedBall :
    euclideanSubdifferentialAt (fun y : E ↦ ‖y‖) (0 : E) = closedBall (0 : E) 1 := by
  simpa using euclidean_subdifferentialAt_l2_norm_eq_piecewise (0 : E)

/-- Away from the origin, Proposition 3.15 identifies the Euclidean/vector-side norm
subdifferential with the singleton containing the normalized vector. -/
theorem euclidean_subdifferentialAt_l2_norm_eq_singleton_of_ne_zero
    {x : E} (hx : x ≠ 0) :
    euclideanSubdifferentialAt (fun y : E ↦ ‖y‖) x = {‖x‖⁻¹ • x} := by
  simpa [hx] using euclidean_subdifferentialAt_l2_norm_eq_piecewise x

end
