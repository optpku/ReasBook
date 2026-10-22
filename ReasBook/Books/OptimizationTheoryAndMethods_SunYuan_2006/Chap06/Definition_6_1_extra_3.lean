/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Definition_6_1_extra_1

noncomputable section

open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Chapter 6 already owns the trust-region quadratic model, feasible set, and predicted reduction
-- through `Definition_6_1_extra_1`.
-- Relevant minimizer style in this domain:
-- * `Mathlib.Order.Filter.Extr.IsMinOn` / `isMinOn_iff` is the canonical minimizer API.
-- * `TrustRegionSubproblem.isSolution_iff_mem_feasibleSet_and_isMinOn`
--   already uses that API for trust-region solutions.
-- This file therefore keeps the source-facing linearized and Cauchy-point predicates, but
-- organizes their minimization clauses around `IsMinOn` instead of a parallel `∀`-based owner.

/-- The curvature term `g_kᵀ B_k g_k` along the steepest-descent ray. -/
def TrustRegionSubproblem.gradientCurvature (P : TrustRegionSubproblem n) : ℝ :=
  dotProduct P.gradient (P.hessianApprox.mulVec P.gradient)

/-- A step solves the linearized trust-region subproblem when it is feasible and minimizes the
linear model `f(x_k) + g_kᵀ s`, equivalently `s ↦ g_kᵀ s`, on the trust region. -/
def TrustRegionSubproblem.IsLinearizedSolution
    (P : TrustRegionSubproblem n) (sG : Point) : Prop :=
  sG ∈ P.feasibleSet ∧
    IsMinOn (fun s : Point ↦ dotProduct P.gradient s) P.feasibleSet sG

/-- `TrustRegionSubproblem.IsLinearizedSolution` keeps the source-facing feasibility clause and
packages the linearized-subproblem minimization clause through the canonical `IsMinOn` owner. -/
theorem TrustRegionSubproblem.isLinearizedSolution_iff_mem_feasibleSet_and_isMinOn
    (P : TrustRegionSubproblem n) (sG : Point) :
    P.IsLinearizedSolution sG ↔
      sG ∈ P.feasibleSet ∧
        IsMinOn (fun s : Point ↦ dotProduct P.gradient s) P.feasibleSet sG :=
  Iff.rfl

/-- Expanding `IsLinearizedSolution` gives feasibility together with
minimality of the linearized model on the trust region. -/
theorem TrustRegionSubproblem.isLinearizedSolution_iff
    (P : TrustRegionSubproblem n) (sG : Point) :
    P.IsLinearizedSolution sG ↔
      sG ∈ P.feasibleSet ∧
        ∀ s : Point, s ∈ P.feasibleSet →
          dotProduct P.gradient sG ≤ dotProduct P.gradient s := by
  rw [TrustRegionSubproblem.isLinearizedSolution_iff_mem_feasibleSet_and_isMinOn, isMinOn_iff]

/-- The boundary steepest-descent step `s_k^G` used in the Cauchy-point construction. When
`g_k = 0`, this declaration uses the canonical feasible minimizer `0`. -/
def TrustRegionSubproblem.gradientBoundaryStep (P : TrustRegionSubproblem n) : Point :=
  if P.gradient = 0 then 0 else -((P.radius / ‖P.gradient‖) : ℝ) • P.gradient

/-- If `g_k ≠ 0`, the boundary steepest-descent step is `-(Δ_k / ‖g_k‖) • g_k`. -/
theorem TrustRegionSubproblem.gradientBoundaryStep_eq_of_ne_zero
    (P : TrustRegionSubproblem n) (h_grad : P.gradient ≠ 0) :
    P.gradientBoundaryStep = -((P.radius / ‖P.gradient‖) : ℝ) • P.gradient := by
  -- In the nondegenerate branch, `gradientBoundaryStep` unfolds to the explicit normalized
  -- negative-gradient step.
  simp [TrustRegionSubproblem.gradientBoundaryStep, h_grad]

/-- If `g_k = 0`, the boundary steepest-descent step is the zero step. -/
theorem TrustRegionSubproblem.gradientBoundaryStep_eq_zero_of_eq_zero
    (P : TrustRegionSubproblem n) (h_grad : P.gradient = 0) :
    P.gradientBoundaryStep = 0 := by
  -- In the degenerate branch, the owner definition already chooses the zero feasible step.
  simp [TrustRegionSubproblem.gradientBoundaryStep, h_grad]

/-- Helper for Chapter06 Definition 6.1-extra-3: when `g_k ≠ 0`, the boundary steepest-descent
step lies on the trust-region boundary `‖s_k^G‖ = Δ_k`. -/
lemma TrustRegionSubproblem.gradientBoundaryStep_norm_eq_radius_of_ne_zero
    (P : TrustRegionSubproblem n) (h_grad : P.gradient ≠ 0) :
    ‖P.gradientBoundaryStep‖ = P.radius := by
  -- Rewrite to the explicit normalized negative-gradient step and evaluate its norm.
  rw [P.gradientBoundaryStep_eq_of_ne_zero h_grad]
  have h_gradient_norm_pos : 0 < ‖P.gradient‖ := norm_pos_iff.mpr h_grad
  calc
    ‖-((P.radius / ‖P.gradient‖) : ℝ) • P.gradient‖
        = ‖-((P.radius / ‖P.gradient‖) : ℝ)‖ * ‖P.gradient‖ := by
            simpa using (norm_smul (-((P.radius / ‖P.gradient‖) : ℝ)) P.gradient)
    _ = ‖(P.radius / ‖P.gradient‖ : ℝ)‖ * ‖P.gradient‖ := by
          simp
    _ = (P.radius / ‖P.gradient‖) * ‖P.gradient‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg P.radius_pos.le (norm_nonneg _))]
    _ = P.radius := by
          field_simp [h_gradient_norm_pos.ne']

/-- The boundary steepest-descent step solves the linearized trust-region subproblem. -/
theorem TrustRegionSubproblem.gradientBoundaryStep_isLinearizedSolution
    (P : TrustRegionSubproblem n) :
    P.IsLinearizedSolution P.gradientBoundaryStep := by
  rw [TrustRegionSubproblem.isLinearizedSolution_iff]
  constructor
  · -- First verify that the explicit steepest-descent step is feasible.
    by_cases h_grad : P.gradient = 0
    · rw [P.gradientBoundaryStep_eq_zero_of_eq_zero h_grad,
        TrustRegionSubproblem.mem_feasibleSet_iff]
      simpa using P.radius_pos.le
    · rw [TrustRegionSubproblem.mem_feasibleSet_iff,
        P.gradientBoundaryStep_norm_eq_radius_of_ne_zero h_grad]
  · intro s hs
    by_cases h_grad : P.gradient = 0
    · -- If the gradient vanishes, the linearized objective is constant on the feasible set.
      simp [P.gradientBoundaryStep_eq_zero_of_eq_zero h_grad, h_grad]
    · have hnorm_sq : dotProduct P.gradient P.gradient = ‖P.gradient‖ ^ (2 : ℕ) := by
        calc
          dotProduct P.gradient P.gradient = ∑ i, P.gradient i * P.gradient i := by
            simp [dotProduct]
          _ = ∑ i, P.gradient i ^ (2 : ℕ) := by
            simp [pow_two]
          _ = ‖P.gradient‖ ^ (2 : ℕ) := by
            exact (EuclideanSpace.real_norm_sq_eq P.gradient).symm
      have hnorm_pos : 0 < ‖P.gradient‖ := norm_pos_iff.mpr h_grad
      have hstep :
          dotProduct P.gradient P.gradientBoundaryStep = -P.radius * ‖P.gradient‖ := by
        -- Evaluate the linearized model at the explicit negative-gradient boundary step.
        have hinner_step :
            dotProduct P.gradient P.gradientBoundaryStep =
              inner ℝ P.gradient P.gradientBoundaryStep := by
          calc
            dotProduct P.gradient P.gradientBoundaryStep
                = dotProduct P.gradientBoundaryStep P.gradient := by
                    rw [dotProduct_comm]
            _ = inner ℝ P.gradient P.gradientBoundaryStep := by
                  simpa using
                    (EuclideanSpace.inner_eq_star_dotProduct P.gradient P.gradientBoundaryStep).symm
        rw [hinner_step, P.gradientBoundaryStep_eq_of_ne_zero h_grad, real_inner_smul_right,
          real_inner_self_eq_norm_sq]
        field_simp [pow_two, hnorm_pos.ne']
      have habs : |dotProduct P.gradient s| ≤ ‖P.gradient‖ * ‖s‖ := by
        have hinner : dotProduct P.gradient s = inner ℝ P.gradient s := by
          calc
            dotProduct P.gradient s = dotProduct s P.gradient := by rw [dotProduct_comm]
            _ = inner ℝ P.gradient s := by
                  simpa using (EuclideanSpace.inner_eq_star_dotProduct P.gradient s).symm
        rw [hinner]
        simpa using abs_real_inner_le_norm P.gradient s
      have hs_norm : ‖s‖ ≤ P.radius := (TrustRegionSubproblem.mem_feasibleSet_iff P s).mp hs
      have hs_lower : -(‖P.gradient‖ * ‖s‖) ≤ dotProduct P.gradient s := (abs_le.mp habs).1
      have hboundary_lower : -P.radius * ‖P.gradient‖ ≤ dotProduct P.gradient s := by
        nlinarith [hs_lower, hs_norm, norm_nonneg P.gradient]
      simpa [hstep] using hboundary_lower

/-- The nonnegative steepest-descent ray through the boundary linearized minimizer `s_k^G`. -/
def TrustRegionSubproblem.gradientRaySet (P : TrustRegionSubproblem n) : Set Point :=
  { s | ∃ τ : ℝ, 0 ≤ τ ∧ s = τ • P.gradientBoundaryStep }

/-- Feasible points on the nonnegative steepest-descent ray through `s_k^G`. -/
def TrustRegionSubproblem.gradientRayFeasibleSet (P : TrustRegionSubproblem n) : Set Point :=
  P.feasibleSet ∩ P.gradientRaySet

/-- The scalar `τ_k` that rescales the boundary steepest-descent step to the Cauchy point. -/
def TrustRegionSubproblem.cauchyPointScale (P : TrustRegionSubproblem n) : ℝ :=
  if P.gradientCurvature ≤ 0 then 1
  else
    min ((‖P.gradient‖ ^ (3 : ℕ)) / (P.radius * P.gradientCurvature)) 1

/-- If `g_kᵀ B_k g_k ≤ 0`, then `τ_k = 1`. -/
theorem TrustRegionSubproblem.cauchyPointScale_eq_one_of_nonpos_curvature
    (P : TrustRegionSubproblem n)
    (h_curv : P.gradientCurvature ≤ 0) :
    P.cauchyPointScale = 1 := by
  -- The piecewise definition selects the boundary value in the nonpositive-curvature branch.
  simp [TrustRegionSubproblem.cauchyPointScale, h_curv]

/-- If `g_kᵀ B_k g_k > 0`, then
`τ_k = min (‖g_k‖^3 / (Δ_k * g_kᵀ B_k g_k)) 1`. -/
theorem TrustRegionSubproblem.cauchyPointScale_eq_min_of_pos_curvature
    (P : TrustRegionSubproblem n)
    (h_curv : 0 < P.gradientCurvature) :
    P.cauchyPointScale =
      min ((‖P.gradient‖ ^ (3 : ℕ)) / (P.radius * P.gradientCurvature)) 1 := by
  -- The positive-curvature branch keeps exactly the source minimizer formula.
  rw [TrustRegionSubproblem.cauchyPointScale, if_neg (not_le_of_gt h_curv)]

/-- Helper for Chapter06 Definition 6.1-extra-3: the stored Cauchy scale is nonnegative. -/
lemma TrustRegionSubproblem.cauchyPointScale_nonneg
    (P : TrustRegionSubproblem n) :
    0 ≤ P.cauchyPointScale := by
  by_cases h_curv : P.gradientCurvature ≤ 0
  · -- The nonpositive-curvature branch fixes the scale at `1`.
    rw [P.cauchyPointScale_eq_one_of_nonpos_curvature h_curv]
    norm_num
  · have h_curv_pos : 0 < P.gradientCurvature := lt_of_not_ge h_curv
    have hratio_nonneg :
        0 ≤ (‖P.gradient‖ ^ (3 : ℕ)) / (P.radius * P.gradientCurvature) := by
      exact div_nonneg (pow_nonneg (norm_nonneg _) _) (mul_nonneg P.radius_pos.le h_curv_pos.le)
    -- In the positive-curvature branch, both entries of the `min` are nonnegative.
    rw [P.cauchyPointScale_eq_min_of_pos_curvature h_curv_pos]
    exact le_min hratio_nonneg zero_le_one

/-- Helper for Chapter06 Definition 6.1-extra-3: the stored Cauchy scale never exceeds the
boundary value `1`. -/
lemma TrustRegionSubproblem.cauchyPointScale_le_one
    (P : TrustRegionSubproblem n) :
    P.cauchyPointScale ≤ 1 := by
  by_cases h_curv : P.gradientCurvature ≤ 0
  · -- The nonpositive-curvature branch gives equality with `1`.
    rw [P.cauchyPointScale_eq_one_of_nonpos_curvature h_curv]
  · have h_curv_pos : 0 < P.gradientCurvature := lt_of_not_ge h_curv
    -- The positive-curvature branch is the minimum of the source ratio and `1`.
    rw [P.cauchyPointScale_eq_min_of_pos_curvature h_curv_pos]
    exact min_le_right _ _

/-- The stored Cauchy point of the trust-region subproblem is `τ_k s_k^G`, where `s_k^G`
is the boundary steepest-descent step and `τ_k` is the source piecewise scalar determined by
`g_kᵀ B_k g_k`. -/
def TrustRegionSubproblem.cauchyPoint (P : TrustRegionSubproblem n) : Point :=
  P.cauchyPointScale • P.gradientBoundaryStep

/-- A step is a Cauchy point for the trust-region subproblem when it is feasible, lies on the
ray through `s_k^G`, and minimizes `q^(k)` among all feasible steps on that ray. Its
minimization clause is packaged through the canonical `IsMinOn` owner on the feasible ray. -/
def TrustRegionSubproblem.IsCauchyPointOnGradientRay
    (P : TrustRegionSubproblem n) (sC : Point) : Prop :=
  sC ∈ P.gradientRayFeasibleSet ∧
    IsMinOn P P.gradientRayFeasibleSet sC

/-- `TrustRegionSubproblem.IsCauchyPointOnGradientRay` is the source-facing feasible
ray-membership clause together with quadratic-model minimality on the canonical feasible-ray
owner. -/
theorem TrustRegionSubproblem.isCauchyPointOnGradientRay_iff_mem_gradientRayFeasibleSet_and_isMinOn
    (P : TrustRegionSubproblem n) (sC : Point) :
    P.IsCauchyPointOnGradientRay sC ↔
      sC ∈ P.gradientRayFeasibleSet ∧ IsMinOn P P.gradientRayFeasibleSet sC :=
  Iff.rfl

/-- Expanding `IsCauchyPointOnGradientRay` gives the feasibility, ray-membership, and
quadratic-model minimality conditions from the source definition. -/
theorem TrustRegionSubproblem.isCauchyPointOnGradientRay_iff
    (P : TrustRegionSubproblem n) (sC : Point) :
    P.IsCauchyPointOnGradientRay sC ↔
      sC ∈ P.feasibleSet ∧
        ∃ τC : ℝ, 0 ≤ τC ∧ sC = τC • P.gradientBoundaryStep ∧
          ∀ s : Point, (∃ τ : ℝ, 0 ≤ τ ∧ s = τ • P.gradientBoundaryStep) →
              s ∈ P.feasibleSet →
            P sC ≤ P s := by
  rw [TrustRegionSubproblem.isCauchyPointOnGradientRay_iff_mem_gradientRayFeasibleSet_and_isMinOn,
    isMinOn_iff]
  constructor
  · rintro ⟨hsC, hmin⟩
    rcases hsC with ⟨hsC_feasible, τC, hτC, hsC_ray⟩
    refine ⟨hsC_feasible, τC, hτC, hsC_ray, ?_⟩
    intro s hs_ray hs_feasible
    exact hmin s ⟨hs_feasible, hs_ray⟩
  · rintro ⟨hsC_feasible, τC, hτC, hsC_ray, hmin⟩
    refine ⟨⟨hsC_feasible, ⟨τC, hτC, hsC_ray⟩⟩, ?_⟩
    intro s hs
    exact hmin s hs.2 hs.1

/-- Helper for Chapter06 Definition 6.1-extra-3: on the nonnegative steepest-descent ray,
feasibility is equivalent to the scalar bound `τ ≤ 1`. -/
lemma TrustRegionSubproblem.nonneg_smul_gradientBoundaryStep_mem_feasibleSet_iff
    (P : TrustRegionSubproblem n) (h_grad : P.gradient ≠ 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    τ • P.gradientBoundaryStep ∈ P.feasibleSet ↔ τ ≤ 1 := by
  -- Normalize the feasible-ray condition using the boundary norm of `gradientBoundaryStep`.
  rw [TrustRegionSubproblem.mem_feasibleSet_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ,
    P.gradientBoundaryStep_norm_eq_radius_of_ne_zero h_grad]
  constructor
  · intro h
    nlinarith [h, P.radius_pos]
  · intro h
    nlinarith [h, P.radius_pos]

/-- Helper for Chapter06 Definition 6.1-extra-3: along the boundary steepest-descent ray,
the predicted reduction is the scalar quadratic from the source proof. -/
lemma TrustRegionSubproblem.predictedReduction_smul_gradientBoundaryStep_eq_of_ne_zero
    (P : TrustRegionSubproblem n) (h_grad : P.gradient ≠ 0) (τ : ℝ) :
    P.predictedReduction (τ • P.gradientBoundaryStep) =
      τ * P.radius * ‖P.gradient‖ -
        (1 / 2 : ℝ) * τ ^ (2 : ℕ) * P.radius ^ (2 : ℕ) * P.gradientCurvature /
          (‖P.gradient‖ ^ (2 : ℕ)) := by
  have hnorm_pos : 0 < ‖P.gradient‖ := norm_pos_iff.mpr h_grad
  have hnorm_sq : dotProduct P.gradient P.gradient = ‖P.gradient‖ ^ (2 : ℕ) := by
    calc
      dotProduct P.gradient P.gradient = ∑ i, P.gradient i * P.gradient i := by
        simp [dotProduct]
      _ = ∑ i, P.gradient i ^ (2 : ℕ) := by
        simp [pow_two]
      _ = ‖P.gradient‖ ^ (2 : ℕ) := by
        exact (EuclideanSpace.real_norm_sq_eq P.gradient).symm
  have hpred_neg (α : ℝ) :
      P.predictedReduction (-(α : ℝ) • P.gradient) =
        α * ‖P.gradient‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * α ^ (2 : ℕ) * P.gradientCurvature := by
    -- Expand the quadratic model once along the negative-gradient ray and collect scalars.
    calc
      P.predictedReduction (-(α : ℝ) • P.gradient)
          =
            -(dotProduct P.gradient (-(α : ℝ) • P.gradient)) -
              (1 / 2 : ℝ) *
                dotProduct (-(α : ℝ) • P.gradient)
                  (P.hessianApprox.mulVec (-(α : ℝ) • P.gradient)) := by
            simp [TrustRegionSubproblem.predictedReduction_eq,
              TrustRegionSubproblem.quadraticModel_eq]
            ring
      _ =
          α * dotProduct P.gradient P.gradient -
            (1 / 2 : ℝ) * α ^ (2 : ℕ) * P.gradientCurvature := by
          rw [dotProduct_smul, Matrix.mulVec_smul, dotProduct_smul]
          simp [TrustRegionSubproblem.gradientCurvature, pow_two, mul_assoc, mul_left_comm,
            mul_comm, smul_dotProduct]
      _ = α * ‖P.gradient‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * α ^ (2 : ℕ) * P.gradientCurvature := by
          rw [hnorm_sq]
  -- Rewrite the boundary step to the explicit negative-gradient ray, then specialize the scalar
  -- predicted-reduction formula.
  rw [P.gradientBoundaryStep_eq_of_ne_zero h_grad]
  calc
    P.predictedReduction (τ • (-((P.radius / ‖P.gradient‖) : ℝ) • P.gradient))
      = P.predictedReduction (-((τ * (P.radius / ‖P.gradient‖)) : ℝ) • P.gradient) := by
          congr 1
          rw [smul_smul]
          congr 1
          ring
    _ =
        (τ * (P.radius / ‖P.gradient‖)) * ‖P.gradient‖ ^ (2 : ℕ) -
          (1 / 2 : ℝ) * (τ * (P.radius / ‖P.gradient‖)) ^ (2 : ℕ) * P.gradientCurvature :=
        hpred_neg (τ * (P.radius / ‖P.gradient‖))
    _ =
        τ * P.radius * ‖P.gradient‖ -
          (1 / 2 : ℝ) * τ ^ (2 : ℕ) * P.radius ^ (2 : ℕ) * P.gradientCurvature /
            (‖P.gradient‖ ^ (2 : ℕ)) := by
          field_simp [pow_two, hnorm_pos.ne']

/-- Helper for Chapter06 Definition 6.1-extra-3: among feasible nonnegative multiples of the
boundary steepest-descent step, the stored Cauchy scale gives the smallest quadratic-model
value. -/
lemma TrustRegionSubproblem.cauchyPoint_onGradientRay_le_of_feasible
    (P : TrustRegionSubproblem n) (h_grad : P.gradient ≠ 0)
    {τ : ℝ} (hτ : 0 ≤ τ) (hfeas : τ • P.gradientBoundaryStep ∈ P.feasibleSet) :
    P (P.cauchyPointScale • P.gradientBoundaryStep) ≤ P (τ • P.gradientBoundaryStep) := by
  have hnorm_pos : 0 < ‖P.gradient‖ := norm_pos_iff.mpr h_grad
  have hτ_le_one : τ ≤ 1 :=
    (P.nonneg_smul_gradientBoundaryStep_mem_feasibleSet_iff h_grad hτ).1 hfeas
  have hpred :
      P.predictedReduction (τ • P.gradientBoundaryStep) ≤
        P.predictedReduction (P.cauchyPointScale • P.gradientBoundaryStep) := by
    by_cases h_curv : P.gradientCurvature ≤ 0
    · have hτk_eq : P.cauchyPointScale = 1 :=
        P.cauchyPointScale_eq_one_of_nonpos_curvature h_curv
      have hboundary_formula (u : ℝ) :
          P.predictedReduction ((1 : ℝ) • P.gradientBoundaryStep) -
              P.predictedReduction (u • P.gradientBoundaryStep) =
            P.radius * (1 - u) *
                (2 * ‖P.gradient‖ ^ (3 : ℕ) - P.radius * P.gradientCurvature * (1 + u)) /
              (2 * ‖P.gradient‖ ^ (2 : ℕ)) := by
        rw [P.predictedReduction_smul_gradientBoundaryStep_eq_of_ne_zero h_grad (1 : ℝ),
          P.predictedReduction_smul_gradientBoundaryStep_eq_of_ne_zero h_grad u]
        field_simp [pow_two, hnorm_pos.ne']
        ring
      have hfactor_nonneg :
          0 ≤ 2 * ‖P.gradient‖ ^ (3 : ℕ) - P.radius * P.gradientCurvature * (1 + τ) := by
        have hcurv_term_nonpos :
            P.radius * P.gradientCurvature * (1 + τ) ≤ 0 := by
          have hradius_curv_nonpos : P.radius * P.gradientCurvature ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos P.radius_pos.le h_curv
          exact mul_nonpos_of_nonpos_of_nonneg hradius_curv_nonpos (by nlinarith [hτ])
        have hnorm_cube_pos : 0 < ‖P.gradient‖ ^ (3 : ℕ) := pow_pos hnorm_pos _
        nlinarith
      have hden_nonneg : 0 ≤ 2 * ‖P.gradient‖ ^ (2 : ℕ) := by
        have hnorm_sq_pos : 0 < ‖P.gradient‖ ^ (2 : ℕ) := pow_pos hnorm_pos _
        nlinarith
      have hdiff_nonneg :
          0 ≤ P.predictedReduction ((1 : ℝ) • P.gradientBoundaryStep) -
            P.predictedReduction (τ • P.gradientBoundaryStep) := by
        rw [hboundary_formula τ]
        exact div_nonneg
          (mul_nonneg (mul_nonneg P.radius_pos.le (sub_nonneg.mpr hτ_le_one)) hfactor_nonneg)
          hden_nonneg
      rw [hτk_eq]
      linarith
    · have h_curv_pos : 0 < P.gradientCurvature := lt_of_not_ge h_curv
      let ρ : ℝ := (‖P.gradient‖ ^ (3 : ℕ)) / (P.radius * P.gradientCurvature)
      have hρ_pos : 0 < ρ := by
        unfold ρ
        exact div_pos (pow_pos hnorm_pos _) (mul_pos P.radius_pos h_curv_pos)
      by_cases hρ_le_one : ρ ≤ 1
      · have hτk_eq : P.cauchyPointScale = ρ := by
          rw [P.cauchyPointScale_eq_min_of_pos_curvature h_curv_pos, min_eq_left hρ_le_one]
        have hcoeff_pos : 0 < (P.radius * ‖P.gradient‖) / (2 * ρ) := by
          have hnum_pos : 0 < P.radius * ‖P.gradient‖ := mul_pos P.radius_pos hnorm_pos
          have hden_pos : 0 < 2 * ρ := by nlinarith
          exact div_pos hnum_pos hden_pos
        have hsquare_formula (u : ℝ) :
            P.predictedReduction (ρ • P.gradientBoundaryStep) -
                P.predictedReduction (u • P.gradientBoundaryStep) =
              ((P.radius * ‖P.gradient‖) / (2 * ρ)) * (u - ρ) ^ (2 : ℕ) := by
          rw [P.predictedReduction_smul_gradientBoundaryStep_eq_of_ne_zero h_grad ρ,
            P.predictedReduction_smul_gradientBoundaryStep_eq_of_ne_zero h_grad u]
          unfold ρ
          field_simp [ρ, pow_two, hnorm_pos.ne', (ne_of_gt P.radius_pos), h_curv_pos.ne']
          ring_nf
        have hdiff_nonneg :
            0 ≤ P.predictedReduction (ρ • P.gradientBoundaryStep) -
              P.predictedReduction (τ • P.gradientBoundaryStep) := by
          rw [hsquare_formula τ]
          exact mul_nonneg hcoeff_pos.le (sq_nonneg _)
        rw [hτk_eq]
        linarith
      · have hρ_gt_one : 1 < ρ := lt_of_not_ge hρ_le_one
        have hτk_eq : P.cauchyPointScale = 1 := by
          rw [P.cauchyPointScale_eq_min_of_pos_curvature h_curv_pos,
            min_eq_right (le_of_lt hρ_gt_one)]
        have hboundary_formula (u : ℝ) :
            P.predictedReduction ((1 : ℝ) • P.gradientBoundaryStep) -
                P.predictedReduction (u • P.gradientBoundaryStep) =
              P.radius * (1 - u) *
                  (2 * ‖P.gradient‖ ^ (3 : ℕ) - P.radius * P.gradientCurvature * (1 + u)) /
                (2 * ‖P.gradient‖ ^ (2 : ℕ)) := by
          rw [P.predictedReduction_smul_gradientBoundaryStep_eq_of_ne_zero h_grad (1 : ℝ),
            P.predictedReduction_smul_gradientBoundaryStep_eq_of_ne_zero h_grad u]
          field_simp [pow_two, hnorm_pos.ne']
          ring
        have hρ_bound : P.radius * P.gradientCurvature < ‖P.gradient‖ ^ (3 : ℕ) := by
          have hden_pos : 0 < P.radius * P.gradientCurvature := mul_pos P.radius_pos h_curv_pos
          unfold ρ at hρ_gt_one
          rcases (one_lt_div_iff).mp hρ_gt_one with hpos | hneg
          · exact hpos.2
          · linarith
        have hfactor_nonneg :
            0 ≤ 2 * ‖P.gradient‖ ^ (3 : ℕ) - P.radius * P.gradientCurvature * (1 + τ) := by
          have hone_add_le : 1 + τ ≤ 2 := by nlinarith
          have hcurv_coeff_nonneg : 0 ≤ P.radius * P.gradientCurvature := by
            exact mul_nonneg P.radius_pos.le h_curv_pos.le
          have hcurv_scaled_le :
              P.radius * P.gradientCurvature * (1 + τ) ≤
                P.radius * P.gradientCurvature * 2 := by
            exact mul_le_mul_of_nonneg_left hone_add_le hcurv_coeff_nonneg
          have hscaled_lt :
              P.radius * P.gradientCurvature * (1 + τ) < 2 * ‖P.gradient‖ ^ (3 : ℕ) := by
            have hscaled_lt' : P.radius * P.gradientCurvature * 2 < 2 * ‖P.gradient‖ ^ (3 : ℕ) := by
              nlinarith [hρ_bound]
            exact lt_of_le_of_lt hcurv_scaled_le hscaled_lt'
          have hfactor_pos :
              0 < 2 * ‖P.gradient‖ ^ (3 : ℕ) - P.radius * P.gradientCurvature * (1 + τ) := by
            nlinarith [hscaled_lt]
          exact hfactor_pos.le
        have hden_nonneg : 0 ≤ 2 * ‖P.gradient‖ ^ (2 : ℕ) := by
          have hnorm_sq_pos : 0 < ‖P.gradient‖ ^ (2 : ℕ) := pow_pos hnorm_pos _
          nlinarith
        have hdiff_nonneg :
            0 ≤ P.predictedReduction ((1 : ℝ) • P.gradientBoundaryStep) -
              P.predictedReduction (τ • P.gradientBoundaryStep) := by
          rw [hboundary_formula τ]
          exact div_nonneg
            (mul_nonneg (mul_nonneg P.radius_pos.le (sub_nonneg.mpr hτ_le_one)) hfactor_nonneg)
            hden_nonneg
        rw [hτk_eq]
        linarith
  -- Convert the predicted-reduction comparison back to the quadratic-model comparison.
  rw [TrustRegionSubproblem.predictedReduction_eq,
    TrustRegionSubproblem.predictedReduction_eq] at hpred
  linarith

/-- Chapter06 Definition 6.1-extra-3: the chosen Cauchy point has the source-facing
minimization property `q^(k) (s_k^c) = min { q^(k) (s) | s = τ s_k^G, ‖s‖ ≤ Δ_k }`. -/
theorem TrustRegionSubproblem.cauchyPoint_isCauchyPointOnGradientRay
    (P : TrustRegionSubproblem n) :
    P.IsCauchyPointOnGradientRay P.cauchyPoint := by
  rw [TrustRegionSubproblem.isCauchyPointOnGradientRay_iff]
  by_cases h_grad : P.gradient = 0
  · have hstep : P.gradientBoundaryStep = 0 := P.gradientBoundaryStep_eq_zero_of_eq_zero h_grad
    have hcauchy : P.cauchyPoint = 0 := by
      -- When the gradient vanishes, both the boundary step and the Cauchy point collapse to `0`.
      simp [TrustRegionSubproblem.cauchyPoint, hstep]
    refine ⟨?_, 0, le_rfl, ?_, ?_⟩
    · rw [hcauchy, TrustRegionSubproblem.mem_feasibleSet_iff]
      simpa using P.radius_pos.le
    · simp [hcauchy, hstep]
    · intro s hs_ray hs_feasible
      rcases hs_ray with ⟨τ, hτ, rfl⟩
      -- The whole feasible gradient ray is just `{0}` in the degenerate branch.
      simp [hcauchy, hstep]
  · have hτk_nonneg : 0 ≤ P.cauchyPointScale := P.cauchyPointScale_nonneg
    have hτk_le_one : P.cauchyPointScale ≤ 1 := P.cauchyPointScale_le_one
    refine ⟨?_, P.cauchyPointScale, hτk_nonneg, rfl, ?_⟩
    · -- The stored Cauchy scale stays in `[0, 1]`, so the scaled boundary step is feasible.
      simpa [TrustRegionSubproblem.cauchyPoint] using
        (P.nonneg_smul_gradientBoundaryStep_mem_feasibleSet_iff h_grad hτk_nonneg).2 hτk_le_one
    · intro s hs_ray hs_feasible
      rcases hs_ray with ⟨τ, hτ, rfl⟩
      -- Reduce the ray minimization to the scalar comparison already proved above.
      simpa [TrustRegionSubproblem.cauchyPoint] using
        P.cauchyPoint_onGradientRay_le_of_feasible h_grad hτ hs_feasible

/-- Expanding the Cauchy point gives `τ_k • s_k^G`. -/
theorem TrustRegionSubproblem.cauchyPoint_eq
    (P : TrustRegionSubproblem n) :
    P.cauchyPoint = P.cauchyPointScale • P.gradientBoundaryStep := by
  -- This is exactly the defining equation of `cauchyPoint`.
  rfl

/-- If `g_k ≠ 0`, the Cauchy point is
`-(τ_k * Δ_k / ‖g_k‖) • g_k`. -/
theorem TrustRegionSubproblem.cauchyPoint_eq_of_ne_zero
    (P : TrustRegionSubproblem n) (h_grad : P.gradient ≠ 0) :
    P.cauchyPoint =
      -((P.cauchyPointScale * P.radius / ‖P.gradient‖) : ℝ) • P.gradient := by
  -- Rewrite the boundary step explicitly and then combine the scalar factors.
  rw [P.cauchyPoint_eq, P.gradientBoundaryStep_eq_of_ne_zero h_grad, smul_smul]
  congr 1
  ring
