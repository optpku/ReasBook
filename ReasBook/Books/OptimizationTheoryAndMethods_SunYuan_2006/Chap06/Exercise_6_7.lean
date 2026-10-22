/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Definition_6_1_extra_3

noncomputable section

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling for this refine pass:
-- * Primary domain: Chapter 6 trust-region step geometry on the owner
--   `TrustRegionSubproblem`.
-- * Inspected owner/data declarations:
--   `TrustRegionSubproblem.gradientCurvature`,
--   `TrustRegionSubproblem.cauchyPoint`,
--   `Matrix.PosDef.isUnit`,
--   and `IsUnit.invertible`.
-- * Core/canonical owner: `TrustRegionSubproblem`; primitive data is the quadratic model,
--   trust-region radius, and Hessian approximation.
-- * Derived API: the dogleg Newton step needs only the explicit Hessian-unit bridge, while the
--   monotonicity theorem keeps the positive-definite regime. The first dogleg breakpoint is
--   already canonically owned upstream by
--   `TrustRegionSubproblem.cauchyPoint`.
-- * This file therefore keeps only the source-facing dogleg path and its monotonicity theorem.
--   It reuses the upstream Cauchy-point owner instead of a parallel local Cauchy-step
--   definition.

namespace TrustRegionSubproblem

/-- The dogleg Newton step is `-B_k⁻¹ g_k`. -/
def newtonStep
    (P : TrustRegionSubproblem n) (h_hessianApprox_isUnit : IsUnit P.hessianApprox) : Point :=
  letI := h_hessianApprox_isUnit.invertible;
  -(Matrix.toEuclideanLin (⅟ P.hessianApprox) P.gradient)

/-- The dogleg path `s(τ)` first follows the ray from `0` to the trust-region Cauchy point and
then follows the segment from the Cauchy point to the Newton step. The standard parameter
interval is `τ ∈ [0, 2]`, with the breakpoint at `τ = 1`. -/
def doglegPath
    (P : TrustRegionSubproblem n) (h_hessianApprox_isUnit : IsUnit P.hessianApprox) (τ : ℝ) :
    Point :=
  if _ : τ ≤ 1 then
    τ • P.cauchyPoint
  else
    P.cauchyPoint + (τ - 1) • (P.newtonStep h_hessianApprox_isUnit - P.cauchyPoint)

/-- Helper for Chapter06 Exercise 6.7: on the first dogleg segment `τ ≤ 1`, the path is the ray
from `0` to the Cauchy point. -/
theorem doglegPath_eq_smul_cauchyPoint_of_le_one
    (P : TrustRegionSubproblem n) (h_hessianApprox_isUnit : IsUnit P.hessianApprox) (τ : ℝ)
    (hτ : τ ≤ 1) :
    P.doglegPath h_hessianApprox_isUnit τ = τ • P.cauchyPoint := by
  -- This unwraps only the first branch of the dogleg path.
  simp [doglegPath, hτ]

/-- Helper for Chapter06 Exercise 6.7: on the second dogleg segment `1 < τ`, the path is the
affine segment from the Cauchy point to the Newton step. -/
theorem doglegPath_eq_cauchyPoint_add_smul_of_one_lt
    (P : TrustRegionSubproblem n) (h_hessianApprox_isUnit : IsUnit P.hessianApprox) (τ : ℝ)
    (hτ : 1 < τ) :
    P.doglegPath h_hessianApprox_isUnit τ =
      P.cauchyPoint + (τ - 1) • (P.newtonStep h_hessianApprox_isUnit - P.cauchyPoint) := by
  -- This unwraps only the second branch of the dogleg path.
  simp [doglegPath, not_le_of_gt hτ]

/-- Helper for Chapter06 Exercise 6.7: converting the Newton step back to coordinate form gives
`-B_k⁻¹ g_k`. -/
theorem ofLp_newtonStep_eq_neg_mulVec_inv
    (P : TrustRegionSubproblem n) (h_hessianApprox_isUnit : IsUnit P.hessianApprox) :
    (P.newtonStep h_hessianApprox_isUnit).ofLp =
      -((P.hessianApprox⁻¹).mulVec P.gradient.ofLp) := by
  letI := h_hessianApprox_isUnit.invertible
  -- Evaluate `Matrix.toEuclideanLin` on coordinates and read off the inverse-Hessian action.
  rw [newtonStep]
  simp

/-- Helper for Chapter06 Exercise 6.7: on `Point = EuclideanSpace ℝ (Fin n)`, the real inner
product is the coordinate dot product. -/
theorem euclideanRealInner_eq_dotProduct (u v : Point) :
    (@inner ℝ Point _ u v) = dotProduct u.ofLp v.ofLp := by
  -- This is the single bridge from Euclidean inner products to coordinate dot products.
  simpa [dotProduct_comm] using (EuclideanSpace.inner_eq_star_dotProduct u v)

/-- Helper for Chapter06 Exercise 6.7: if the segment from `x` toward `y` initially points
outward from `x`, then the norm is monotone along that segment. -/
theorem norm_add_smul_sub_monotoneOn_of_inner_nonneg
    {x y : Point} (hxy : 0 ≤ dotProduct x.ofLp (y - x).ofLp) :
    MonotoneOn (fun t : ℝ ↦ ‖x + t • (y - x)‖) (Set.Ici (0 : ℝ)) := by
  intro a ha b hb hab
  let d : Point := y - x
  have hxd : 0 ≤ @inner ℝ Point _ x d := by
    -- Repackage the outward-pointing hypothesis using the segment direction `d`.
    simpa [euclideanRealInner_eq_dotProduct, d] using hxy
  have hsq : ‖x + a • d‖ ^ (2 : ℕ) ≤ ‖x + b • d‖ ^ (2 : ℕ) := by
    -- Compare the squared norms; after expansion the difference factors through `b - a`.
    rw [norm_add_sq_real, norm_add_sq_real]
    simp only [real_inner_smul_right, norm_smul, Real.norm_of_nonneg ha,
      Real.norm_of_nonneg hb]
    ring_nf
    have hslope : 0 ≤ 2 * (@inner ℝ Point _ x d) + (a + b) * ‖d‖ ^ (2 : ℕ) := by
      have hab_nonneg : 0 ≤ a + b := add_nonneg ha hb
      have hquad_nonneg : 0 ≤ (a + b) * ‖d‖ ^ (2 : ℕ) := by
        exact mul_nonneg hab_nonneg (sq_nonneg ‖d‖)
      nlinarith
    nlinarith [hab, hslope]
  -- Nonnegativity of norms lets us pass back from squared norms to norms.
  have hnorm_nonneg_a : 0 ≤ ‖x + a • d‖ := norm_nonneg _
  have hnorm_nonneg_b : 0 ≤ ‖x + b • d‖ := norm_nonneg _
  nlinarith

/-- Helper for Chapter06 Exercise 6.7: a positive-definite matrix satisfies the inverse-Hessian
Cauchy-Schwarz estimate in coordinates. -/
theorem dotProductSelf_sq_le_mulVec_mulVecInv_of_posDef
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef) (g : Fin n → ℝ) :
    (dotProduct g g) ^ (2 : ℕ) ≤
      dotProduct g (B.mulVec g) * dotProduct g ((B⁻¹).mulVec g) := by
  letI := hB.isUnit.invertible
  have hB_symm : B.IsSymm := by
    simpa [Matrix.isHermitian_iff_isSymm] using hB.1
  have hbil_nonneg : ∀ x, 0 ≤ Matrix.toBilin' B x x := by
    -- Positive definiteness gives the positive-semidefinite hypothesis for Cauchy-Schwarz.
    intro x
    simpa [Matrix.toBilin'_apply'] using hB.posSemidef.dotProduct_mulVec_nonneg x
  have hmul_inv : B.mulVec ((B⁻¹).mulVec g) = g := by
    -- Applying `B` after `B⁻¹` collapses to the identity on coordinate vectors.
    calc
      B.mulVec ((B⁻¹).mulVec g) = (B * B⁻¹).mulVec g := by
        exact Matrix.mulVec_mulVec g B B⁻¹
      _ = g := by simp
  -- Apply bilinear-form Cauchy-Schwarz to `g` and `B⁻¹ g`.
  have hbil_symm_form : (Matrix.toBilin' B).IsSymm :=
    (Matrix.isSymm_toBilin'_iff_isSymm).2 hB_symm
  have hbil_symm : LinearMap.IsSymm (Matrix.toBilin' B) :=
    (LinearMap.BilinForm.isSymm_iff).1 hbil_symm_form
  have hcs :=
    (Matrix.toBilin' B).apply_sq_le_of_symm hbil_nonneg hbil_symm g ((B⁻¹).mulVec g)
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.toBilin'_apply'] at hcs
  simpa [hmul_inv, dotProduct_comm] using hcs

/-- Helper for Chapter06 Exercise 6.7: the positive-definite Hessian bilinear form yields the
estimate `‖g_k‖^4 ≤ (g_kᵀ B_k g_k) (g_kᵀ B_k⁻¹ g_k)`. -/
theorem gradientNormFourth_le_gradientCurvature_mul_inverseQuadratic
    (P : TrustRegionSubproblem n) (h_hessianApprox_posDef : P.hessianApprox.PosDef) :
    ‖P.gradient‖ ^ (4 : ℕ) ≤
      P.gradientCurvature *
        dotProduct P.gradient.ofLp ((P.hessianApprox⁻¹).mulVec P.gradient.ofLp) := by
  let g : Fin n → ℝ := P.gradient.ofLp
  have hnorm_sq : ‖P.gradient‖ ^ (2 : ℕ) = dotProduct g g := by
    -- Normalize the Euclidean norm square to the coordinate dot product once.
    simpa [g, dotProduct, pow_two] using (EuclideanSpace.real_norm_sq_eq P.gradient)
  have hcoord :=
    dotProductSelf_sq_le_mulVec_mulVecInv_of_posDef P.hessianApprox h_hessianApprox_posDef g
  -- The remaining wrapper only rewrites the trust-region notation to the coordinate estimate.
  calc
    ‖P.gradient‖ ^ (4 : ℕ) = (‖P.gradient‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    _ = (dotProduct g g) ^ (2 : ℕ) := by rw [hnorm_sq]
    _ ≤
        dotProduct g (P.hessianApprox.mulVec g) *
          dotProduct g ((P.hessianApprox⁻¹).mulVec g) := hcoord
    _ =
        P.gradientCurvature *
          dotProduct P.gradient.ofLp ((P.hessianApprox⁻¹).mulVec P.gradient.ofLp) := by
      simp [TrustRegionSubproblem.gradientCurvature, g]

/-- Helper for Chapter06 Exercise 6.7: on the positive-definite dogleg segment from the Cauchy
point to the Newton step, the initial direction points outward from the Cauchy point. -/
theorem inner_cauchyPoint_newtonStep_sub_nonneg
    (P : TrustRegionSubproblem n) (h_hessianApprox_posDef : P.hessianApprox.PosDef) :
    0 ≤ dotProduct P.cauchyPoint.ofLp
      ((P.newtonStep h_hessianApprox_posDef.isUnit - P.cauchyPoint).ofLp) := by
  by_cases h_grad : P.gradient = 0
  · have hcauchy : P.cauchyPoint = 0 := by
      -- In the degenerate zero-gradient case, the Cauchy point vanishes.
      rw [P.cauchyPoint_eq, P.gradientBoundaryStep_eq_zero_of_eq_zero h_grad, smul_zero]
    have hnewton : P.newtonStep h_hessianApprox_posDef.isUnit = 0 := by
      -- The Newton step also vanishes because it is linear in the gradient.
      rw [newtonStep, h_grad]
      simp
    simp [hcauchy, hnewton]
  · let α : ℝ := P.cauchyPointScale * P.radius / ‖P.gradient‖
    let invQuad : ℝ :=
      dotProduct P.gradient.ofLp ((P.hessianApprox⁻¹).mulVec P.gradient.ofLp)
    let gDot : ℝ := dotProduct P.gradient.ofLp P.gradient.ofLp
    have hnorm_pos : 0 < ‖P.gradient‖ := norm_pos_iff.mpr h_grad
    have h_grad_ofLp : P.gradient.ofLp ≠ 0 := by
      simpa using h_grad
    have hcurv_pos : 0 < P.gradientCurvature := by
      -- Positive definiteness makes the curvature strictly positive away from `g = 0`.
      simpa [TrustRegionSubproblem.gradientCurvature] using
        h_hessianApprox_posDef.dotProduct_mulVec_pos h_grad_ofLp
    have hcauchy :
        P.cauchyPoint = -(α : ℝ) • P.gradient := by
      -- Use the upstream closed form of the Cauchy point on the gradient ray.
      simpa [α] using P.cauchyPoint_eq_of_ne_zero h_grad
    have hscale_eq :
        P.cauchyPointScale =
          min ((‖P.gradient‖ ^ (3 : ℕ)) / (P.radius * P.gradientCurvature)) 1 := by
      exact P.cauchyPointScale_eq_min_of_pos_curvature hcurv_pos
    have hscale_nonneg : 0 ≤ P.cauchyPointScale := by
      -- The source Cauchy-point scale is a minimum of two nonnegative quantities.
      rw [hscale_eq]
      refine le_min ?_ zero_le_one
      exact div_nonneg (by positivity) (mul_nonneg P.radius_pos.le hcurv_pos.le)
    have hα_nonneg : 0 ≤ α := by
      -- The scalar `α` rescales the negative gradient direction.
      exact div_nonneg (mul_nonneg hscale_nonneg P.radius_pos.le) hnorm_pos.le
    have hgDot_eq : gDot = ‖P.gradient‖ ^ (2 : ℕ) := by
      -- The gradient self-dot-product is the Euclidean norm square.
      simpa [gDot, dotProduct, pow_two] using (EuclideanSpace.real_norm_sq_eq P.gradient).symm
    have hgDot_nonneg : 0 ≤ gDot := by
      rw [hgDot_eq]
      positivity
    have hscale_upper :
        P.cauchyPointScale ≤
          (‖P.gradient‖ ^ (3 : ℕ)) / (P.radius * P.gradientCurvature) := by
      rw [hscale_eq]
      exact min_le_left _ _
    have hα_le :
        α ≤ gDot / P.gradientCurvature := by
      -- The Cauchy-point truncation gives the sharp bound `α ≤ ‖g‖² / (gᵀBg)`.
      have hscale_mul :
          P.cauchyPointScale * (P.radius * P.gradientCurvature) ≤ ‖P.gradient‖ ^ (3 : ℕ) := by
        have hmul :=
          mul_le_mul_of_nonneg_right hscale_upper (mul_nonneg P.radius_pos.le hcurv_pos.le)
        have hmul' := hmul
        have hden_pos : 0 < P.radius * P.gradientCurvature := mul_pos P.radius_pos hcurv_pos
        field_simp [hden_pos.ne'] at hmul'
        have hr_cancel : P.radius * ‖P.gradient‖ ^ (3 : ℕ) / P.radius = ‖P.gradient‖ ^ (3 : ℕ) := by
          field_simp [P.radius_pos.ne']
        simpa [mul_assoc, hr_cancel] using hmul'
      have hα_mul : α * P.gradientCurvature ≤ ‖P.gradient‖ ^ (2 : ℕ) := by
        have hdiv :
            (P.cauchyPointScale * P.radius * P.gradientCurvature) / ‖P.gradient‖ ≤
              ‖P.gradient‖ ^ (2 : ℕ) := by
          exact (div_le_iff₀ hnorm_pos).2 (by simpa [pow_two, pow_succ, mul_assoc, mul_comm,
            mul_left_comm] using hscale_mul)
        simpa [α, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
      have hα_le_norm : α ≤ ‖P.gradient‖ ^ (2 : ℕ) / P.gradientCurvature := by
        exact (le_div_iff₀ hcurv_pos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hα_mul)
      simpa [hgDot_eq] using hα_le_norm
    have hquartic_div :
        gDot ^ (2 : ℕ) / P.gradientCurvature ≤ invQuad := by
      -- The inverse-Hessian estimate converts the quartic norm bound into a lower bound on
      -- `gᵀ B⁻¹ g`.
      have hquartic := P.gradientNormFourth_le_gradientCurvature_mul_inverseQuadratic
        h_hessianApprox_posDef
      have hdiv : ‖P.gradient‖ ^ (4 : ℕ) / P.gradientCurvature ≤ invQuad := by
        exact (div_le_iff₀ hcurv_pos).2
          (by simpa [invQuad, mul_comm, mul_left_comm, mul_assoc] using hquartic)
      have hgDot_sq : gDot ^ (2 : ℕ) = ‖P.gradient‖ ^ (4 : ℕ) := by
        rw [hgDot_eq]
        ring
      simpa [hgDot_sq] using hdiv
    have hα_self_le_inv : α * gDot ≤ invQuad := by
      -- Combine the Cauchy-point truncation bound with the quartic inverse-Hessian bound.
      have hmul := mul_le_mul_of_nonneg_left hα_le hgDot_nonneg
      have hupper : gDot * (gDot / P.gradientCurvature) ≤ invQuad := by
        simpa [pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hquartic_div
      exact le_trans (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul)
        hupper
    have hdiff_nonneg : 0 ≤ invQuad - α * gDot := by
      linarith
    have hfactor_nonneg : 0 ≤ α * (invQuad - α * gDot) := by
      positivity
    -- Route correction: after the scalar bounds are in place, finish directly in coordinates.
    have hcoords :
        dotProduct P.cauchyPoint.ofLp
          ((P.newtonStep h_hessianApprox_posDef.isUnit - P.cauchyPoint).ofLp) =
          α * (invQuad - α * gDot) := by
      -- Expand the Cauchy and Newton formulas in coordinates and collect the scalar factors.
      rw [show P.cauchyPoint.ofLp = -(α : ℝ) • P.gradient.ofLp by simp [hcauchy]]
      rw [show (P.newtonStep h_hessianApprox_posDef.isUnit - P.cauchyPoint).ofLp =
          -((P.hessianApprox⁻¹).mulVec P.gradient.ofLp) - (-(α : ℝ) • P.gradient.ofLp) by
            simp [P.ofLp_newtonStep_eq_neg_mulVec_inv h_hessianApprox_posDef.isUnit, hcauchy]]
      simp [invQuad, gDot, dotProduct_add, dotProduct_smul, dotProduct_comm, mul_comm,
        mul_left_comm, sub_eq_add_neg]
      ring
    nlinarith [hfactor_nonneg, hcoords]

/-- Chapter06 Exercise 6.7: for the dogleg path `s(τ)` constructed from the trust-region Cauchy
point and the Newton step of a positive-definite quadratic model, the norm `‖s(τ)‖` increases
monotonically along the path on the standard parameter interval `τ ∈ [0, 2]`. -/
theorem norm_doglegPath_monotoneOn
    (P : TrustRegionSubproblem n) (h_hessianApprox_posDef : P.hessianApprox.PosDef) :
    MonotoneOn (fun τ : ℝ ↦ ‖P.doglegPath h_hessianApprox_posDef.isUnit τ‖)
      (Set.Icc (0 : ℝ) 2) := by
  intro a ha b hb hab
  by_cases hb_one : b ≤ 1
  · have ha_one : a ≤ 1 := le_trans hab hb_one
    -- On the first leg the dogleg path is just a ray through the Cauchy point.
    have hray : ‖a • P.cauchyPoint‖ ≤ ‖b • P.cauchyPoint‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha.1, Real.norm_of_nonneg hb.1]
      exact mul_le_mul_of_nonneg_right hab (norm_nonneg P.cauchyPoint)
    simpa [P.doglegPath_eq_smul_cauchyPoint_of_le_one h_hessianApprox_posDef.isUnit a ha_one,
      P.doglegPath_eq_smul_cauchyPoint_of_le_one h_hessianApprox_posDef.isUnit b hb_one] using hray
  · have hb_one_lt : 1 < b := lt_of_not_ge hb_one
    by_cases ha_one : a ≤ 1
    · have ha_to_cauchy : ‖P.doglegPath h_hessianApprox_posDef.isUnit a‖ ≤ ‖P.cauchyPoint‖ := by
      -- The first leg reaches the Cauchy point monotonically at `τ = 1`.
        have hray : ‖a • P.cauchyPoint‖ ≤ ‖P.cauchyPoint‖ := by
          rw [norm_smul, Real.norm_of_nonneg ha.1]
          simpa using mul_le_mul_of_nonneg_right ha_one (norm_nonneg P.cauchyPoint)
        simpa [P.doglegPath_eq_smul_cauchyPoint_of_le_one h_hessianApprox_posDef.isUnit a ha_one]
          using hray
      have hsecond :
          ‖P.cauchyPoint‖ ≤ ‖P.doglegPath h_hessianApprox_posDef.isUnit b‖ := by
        have hmono :=
          norm_add_smul_sub_monotoneOn_of_inner_nonneg
            (x := P.cauchyPoint)
            (y := P.newtonStep h_hessianApprox_posDef.isUnit)
            (P.inner_cauchyPoint_newtonStep_sub_nonneg h_hessianApprox_posDef)
        have hzero : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := by
          simp
        have hb_shift : b - 1 ∈ Set.Ici (0 : ℝ) := by
          simpa [Set.mem_Ici] using sub_nonneg.mpr hb_one_lt.le
        have hb_shift_nonneg : (0 : ℝ) ≤ b - 1 := by
          linarith
        have hseg := hmono hzero hb_shift hb_shift_nonneg
        simpa [P.doglegPath_eq_cauchyPoint_add_smul_of_one_lt h_hessianApprox_posDef.isUnit b
          hb_one_lt] using hseg
      exact le_trans ha_to_cauchy hsecond
    · have ha_one_lt : 1 < a := lt_of_not_ge ha_one
      have hmono :=
        norm_add_smul_sub_monotoneOn_of_inner_nonneg
          (x := P.cauchyPoint)
          (y := P.newtonStep h_hessianApprox_posDef.isUnit)
          (P.inner_cauchyPoint_newtonStep_sub_nonneg h_hessianApprox_posDef)
      have ha_shift : a - 1 ∈ Set.Ici (0 : ℝ) := by
        simpa [Set.mem_Ici] using sub_nonneg.mpr ha_one_lt.le
      have hb_shift : b - 1 ∈ Set.Ici (0 : ℝ) := by
        simpa [Set.mem_Ici] using sub_nonneg.mpr hb_one_lt.le
      have hab_shift : a - 1 ≤ b - 1 := by
        linarith
      have hseg := hmono ha_shift hb_shift hab_shift
      -- On the second leg we reuse the generic monotonicity of segment norms.
      simpa [P.doglegPath_eq_cauchyPoint_add_smul_of_one_lt h_hessianApprox_posDef.isUnit a
        ha_one_lt,
        P.doglegPath_eq_cauchyPoint_add_smul_of_one_lt h_hessianApprox_posDef.isUnit b hb_one_lt]
        using hseg

end TrustRegionSubproblem

end
