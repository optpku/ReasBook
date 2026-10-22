/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Exercise_6_10
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Definition_6_1_extra_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Lemma_6_1_4
import Mathlib.Order.Filter.Extr
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

-- Domain sampling:
-- * primary domain: weighted trust-region subproblems and Cauchy-point constructions;
-- * inspected declarations:
--   `Mathlib.Order.Filter.Extr.IsMinOn`,
--   `TrustRegionSubproblem.gradientBoundaryStep`,
--   `TrustRegionSubproblem.IsLinearizedSolution`,
--   `TrustRegionSubproblem.gradientRayFeasibleSet`,
--   `TrustRegionSubproblem.IsCauchyPointOnGradientRay`;
-- * source/core/bridge triage:
--   the Exercise 6.10 owner `GeneralizedTrustRegionSubproblem` is the core/canonical primitive
--   data layer for weighted trust-region models in this chapter,
--   this Exercise 6.9 file is source-facing and adds the generalized steepest-descent and
--   generalized Cauchy-point formulas,
--   and the weighted-gradient ray and scale feasible sets below are bridge/view data derived
--   from that owner rather than new primitive fields.
-- Primitive-vs-derived check:
-- * `fAtCenter`, `gradient`, `hessianApprox`, `scalingMatrix`, `scalingMatrixInv`, and `radius`
--   already live in the upstream owner;
-- * `quadraticModel`, `weightedNorm`, `feasibleSet`, and the owner-level weighted metric
--   `Dᵀ D` already live there conceptually;
-- * this file therefore keeps only the Exercise 6.9-specific linearized/ray-minimization API,
--   phrased through the canonical minimizer owner `IsMinOn` and the weighted geometry
--   `(Dᵀ D)⁻¹` and `D⁻ᵀ g`.

section

namespace GeneralizedTrustRegionSubproblem

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- The linearized model minimized in part (1) is `f(x_k) + g_kᵀ s`. -/
def linearizedModel (P : GeneralizedTrustRegionSubproblem n) (s : Point) : ℝ :=
  P.fAtCenter + dotProduct P.gradient s

/-- The inverse weighted metric `(Dᵀ D)⁻¹ = D⁻¹ D⁻ᵀ` attached to the trust-region norm
`‖D s‖₂`. -/
def inverseWeightMatrix (P : GeneralizedTrustRegionSubproblem n) : MatrixN :=
  P.scalingMatrixInv * P.scalingMatrixInv.transpose

/-- The dual weighted gradient `D⁻ᵀ g_k` arising from the change of variables `y = D s`. -/
def inverseTransposeScaledGradient (P : GeneralizedTrustRegionSubproblem n) : Point :=
  Matrix.toEuclideanLin P.scalingMatrixInv.transpose P.gradient

/-- The weighted steepest-descent direction `(Dᵀ D)⁻¹ g_k = D⁻¹ D⁻ᵀ g_k`. -/
def generalizedGradientDirection (P : GeneralizedTrustRegionSubproblem n) : Point :=
  Matrix.toEuclideanLin P.inverseWeightMatrix P.gradient

/-- The curvature scalar `g_kᵀ (Dᵀ D)⁻¹ B_k (Dᵀ D)⁻¹ g_k` along the weighted steepest-descent
ray. -/
def generalizedGradientCurvature (P : GeneralizedTrustRegionSubproblem n) : ℝ :=
  dotProduct P.gradient
    (Matrix.toEuclideanLin
      (P.inverseWeightMatrix * P.hessianApprox * P.inverseWeightMatrix) P.gradient)

/-- Helper for Chapter06 Exercise 6.9: if the scaling matrix `D` is symmetric, then its stored
inverse is symmetric as well. -/
theorem scalingMatrixInv_transpose_eq_of_isSymm
    (P : GeneralizedTrustRegionSubproblem n) (h_scalingMatrix_symm : P.scalingMatrix.IsSymm) :
    P.scalingMatrixInv.transpose = P.scalingMatrixInv := by
  -- Use the explicit inverse identities to show that `D⁻ᵀ` is also a left inverse of `D`,
  -- then cancel the common factor.
  calc
    P.scalingMatrixInv.transpose
      = P.scalingMatrixInv.transpose * 1 := by simp
    _ = P.scalingMatrixInv.transpose * (P.scalingMatrix * P.scalingMatrixInv) := by
          rw [P.scalingMatrix_mul_inv]
    _ = (P.scalingMatrixInv.transpose * P.scalingMatrix) * P.scalingMatrixInv := by
          rw [Matrix.mul_assoc]
    _ = 1 * P.scalingMatrixInv := by
          have h_left_inverse :
              P.scalingMatrixInv.transpose * P.scalingMatrix = 1 := by
            calc
              P.scalingMatrixInv.transpose * P.scalingMatrix
                = P.scalingMatrixInv.transpose * P.scalingMatrix.transpose := by
                    rw [h_scalingMatrix_symm.eq]
              _ = (P.scalingMatrix * P.scalingMatrixInv).transpose := by
                    simp [Matrix.transpose_mul]
              _ = 1 := by simp [P.scalingMatrix_mul_inv]
          rw [h_left_inverse]
    _ = P.scalingMatrixInv := by simp

/-- If `D` is symmetric, then the dual weighted gradient `D⁻ᵀ g_k` reduces to the source vector
`D⁻¹ g_k`. -/
theorem inverseTransposeScaledGradient_eq_inverseScaledGradient_of_isSymm
    (P : GeneralizedTrustRegionSubproblem n) (h_scalingMatrix_symm : P.scalingMatrix.IsSymm) :
    P.inverseTransposeScaledGradient = Matrix.toEuclideanLin P.scalingMatrixInv P.gradient := by
  -- Route correction: first normalize the stored inverse to a symmetric matrix, then rewrite the
  -- transported gradient with that stable normal form.
  have h_inv_transpose : P.scalingMatrixInv.transpose = P.scalingMatrixInv :=
    P.scalingMatrixInv_transpose_eq_of_isSymm h_scalingMatrix_symm
  -- The weighted dual gradient now uses the ordinary inverse matrix.
  rw [inverseTransposeScaledGradient, h_inv_transpose]

/-- If `D` is symmetric, then `(Dᵀ D)⁻¹` reduces to the source matrix `D⁻²`. -/
theorem inverseWeightMatrix_eq_inverseSquareMatrix_of_isSymm
    (P : GeneralizedTrustRegionSubproblem n) (h_scalingMatrix_symm : P.scalingMatrix.IsSymm) :
    P.inverseWeightMatrix = P.scalingMatrixInv * P.scalingMatrixInv := by
  -- Rewrite the transpose factor using the symmetry of the explicit inverse.
  rw [inverseWeightMatrix, P.scalingMatrixInv_transpose_eq_of_isSymm h_scalingMatrix_symm]

/-- A step solves the linearized weighted trust-region subproblem when it is feasible and
minimizes `f(x_k) + g_kᵀ s` on `‖D s‖ ≤ Δ_k`. -/
def IsLinearizedSolution (P : GeneralizedTrustRegionSubproblem n) (sG : Point) : Prop :=
  sG ∈ P.feasibleSet ∧
    IsMinOn P.linearizedModel P.feasibleSet sG

/-- `IsLinearizedSolution` keeps the source-facing feasibility clause and packages the linearized
minimization statement through the canonical `IsMinOn` owner. -/
theorem isLinearizedSolution_iff_mem_feasibleSet_and_isMinOn
    (P : GeneralizedTrustRegionSubproblem n) (sG : Point) :
    P.IsLinearizedSolution sG ↔
      sG ∈ P.feasibleSet ∧ IsMinOn P.linearizedModel P.feasibleSet sG :=
  Iff.rfl

/-- Expanding `IsLinearizedSolution` gives feasibility together with minimality of
`f(x_k) + g_kᵀ s` on the weighted trust region. -/
theorem isLinearizedSolution_iff
    (P : GeneralizedTrustRegionSubproblem n) (sG : Point) :
    P.IsLinearizedSolution sG ↔
      sG ∈ P.feasibleSet ∧
        ∀ s : Point, s ∈ P.feasibleSet →
          P.linearizedModel sG ≤ P.linearizedModel s := by
  rw [isLinearizedSolution_iff_mem_feasibleSet_and_isMinOn, isMinOn_iff]

/-- The weighted steepest-descent boundary step
`-(Δ_k / ‖D⁻ᵀ g_k‖₂) (Dᵀ D)⁻¹ g_k`. When `g_k = 0`, this declaration uses the canonical
feasible minimizer `0`. Under symmetry of `D`, the nonzero-gradient branch is the source formula
`-(Δ_k / ‖D⁻¹ g_k‖₂) D⁻² g_k`. -/
def generalizedGradientBoundaryStep (P : GeneralizedTrustRegionSubproblem n) : Point :=
  if P.gradient = 0 then 0
  else -((P.radius / ‖P.inverseTransposeScaledGradient‖) : ℝ) • P.generalizedGradientDirection

/-- If `g_k ≠ 0`, the weighted boundary steepest-descent step is the source quotient formula. -/
theorem generalizedGradientBoundaryStep_eq_of_ne_zero
    (P : GeneralizedTrustRegionSubproblem n) (h_gradient : P.gradient ≠ 0) :
    P.generalizedGradientBoundaryStep =
      -((P.radius / ‖P.inverseTransposeScaledGradient‖) : ℝ) • P.generalizedGradientDirection :=
  by
  simp [generalizedGradientBoundaryStep, h_gradient]

/-- If `g_k = 0`, the weighted boundary steepest-descent step is the zero step. -/
theorem generalizedGradientBoundaryStep_eq_zero_of_eq_zero
    (P : GeneralizedTrustRegionSubproblem n) (h_gradient : P.gradient = 0) :
    P.generalizedGradientBoundaryStep = 0 := by
  simp [generalizedGradientBoundaryStep, h_gradient]

/-- The positive weighted-gradient ray through the boundary linearized minimizer `s_k^G`. -/
def generalizedGradientRaySet (P : GeneralizedTrustRegionSubproblem n) : Set Point :=
  { s | ∃ τ : ℝ, 0 < τ ∧ s = τ • P.generalizedGradientBoundaryStep }

/-- Feasible points on the positive weighted-gradient ray through `s_k^G`. -/
def generalizedGradientRayFeasibleSet (P : GeneralizedTrustRegionSubproblem n) : Set Point :=
  P.feasibleSet ∩ P.generalizedGradientRaySet

/-- Positive ray parameters whose weighted-gradient ray points remain feasible. When `g_k = 0`,
the source ray degenerates to the zero step, so every positive scale yields the same ray point
`0`. -/
def generalizedGradientScaleFeasibleSet (P : GeneralizedTrustRegionSubproblem n) : Set ℝ :=
  { τ | 0 < τ ∧ τ • P.generalizedGradientBoundaryStep ∈ P.feasibleSet }

/-- If `g_k = 0`, the feasible generalized Cauchy scales are exactly the positive parameters,
since the weighted-gradient ray collapses to the single feasible point `0`. -/
theorem generalizedGradientScaleFeasibleSet_eq_of_eq_zero
    (P : GeneralizedTrustRegionSubproblem n) (h_gradient : P.gradient = 0) :
    P.generalizedGradientScaleFeasibleSet = { τ | 0 < τ } := by
  have h_zero_feasible : (0 : Point) ∈ P.feasibleSet := by
    rw [P.mem_feasibleSet_iff]
    simp [GeneralizedTrustRegionSubproblem.weightedNorm, P.radius_pos.le]
  ext τ
  simp [generalizedGradientScaleFeasibleSet,
    P.generalizedGradientBoundaryStep_eq_zero_of_eq_zero h_gradient, h_zero_feasible]

/-- The source scalar `τ_k` is a generalized Cauchy scale when the ray point `τ_k s_k^G` is
feasible and minimizes `q^(k)` among all feasible points on the positive ray through `s_k^G`. -/
def IsGeneralizedCauchyScale (P : GeneralizedTrustRegionSubproblem n) (τk : ℝ) : Prop :=
  τk ∈ P.generalizedGradientScaleFeasibleSet ∧
    IsMinOn
      (fun τ : ℝ ↦ P.quadraticModel (τ • P.generalizedGradientBoundaryStep))
      P.generalizedGradientScaleFeasibleSet τk

/-- `IsGeneralizedCauchyScale` keeps the source-facing positivity/feasibility clause and
packages ray minimization through `IsMinOn` on the feasible scale set. -/
theorem isGeneralizedCauchyScale_iff_mem_generalizedGradientScaleFeasibleSet_and_isMinOn
    (P : GeneralizedTrustRegionSubproblem n) (τk : ℝ) :
    P.IsGeneralizedCauchyScale τk ↔
      τk ∈ P.generalizedGradientScaleFeasibleSet ∧
        IsMinOn
          (fun τ : ℝ ↦ P.quadraticModel (τ • P.generalizedGradientBoundaryStep))
          P.generalizedGradientScaleFeasibleSet τk :=
  Iff.rfl

/-- If `g_k = 0`, the generalized Cauchy scales are exactly the positive parameters: every such
scale produces the same source point `τ_k s_k^G = 0`. -/
theorem isGeneralizedCauchyScale_iff_of_eq_zero
    (P : GeneralizedTrustRegionSubproblem n) (τk : ℝ) (h_gradient : P.gradient = 0) :
    P.IsGeneralizedCauchyScale τk ↔ 0 < τk := by
  rw [isGeneralizedCauchyScale_iff_mem_generalizedGradientScaleFeasibleSet_and_isMinOn,
    P.generalizedGradientScaleFeasibleSet_eq_of_eq_zero h_gradient, isMinOn_iff]
  constructor
  · rintro ⟨hτk, _⟩
    exact hτk
  · intro hτk
    refine ⟨hτk, ?_⟩
    intro τ hτ
    -- When the boundary step vanishes, the ray model is constant at the feasible zero step.
    simp [P.generalizedGradientBoundaryStep_eq_zero_of_eq_zero h_gradient]

/-- Helper for Chapter06 Exercise 6.9: the standardized gradient is exactly the weighted dual
gradient `D⁻ᵀ g_k`. -/
theorem toTrustRegionSubproblem_gradient_eq_inverseTransposeScaledGradient
    (P : GeneralizedTrustRegionSubproblem n) :
    P.toTrustRegionSubproblem.gradient = P.inverseTransposeScaledGradient := by
  -- Both sides are the same Euclidean-space image of `D⁻ᵀ g_k`.
  rfl

/-- Helper for Chapter06 Exercise 6.9: the linearized weighted model becomes the ordinary
linearized model after standardization, up to the shared constant `f(x_k)`. -/
theorem linearizedModel_eq_standardized_linearizedModel
    (P : GeneralizedTrustRegionSubproblem n) (s : Point) :
    P.linearizedModel s =
      P.fAtCenter + dotProduct P.toTrustRegionSubproblem.gradient (P.standardizeStep s) := by
  -- Reuse the same linear-term transport as in Exercise 6.10 and keep the constant untouched.
  rw [linearizedModel]
  have hLinear :
      dotProduct P.toTrustRegionSubproblem.gradient (P.standardizeStep s) =
        dotProduct P.gradient s := by
    calc
      dotProduct P.toTrustRegionSubproblem.gradient (P.standardizeStep s)
        = dotProduct (P.scalingMatrix.mulVec s.ofLp)
            (P.scalingMatrixInv.transpose.mulVec P.gradient.ofLp) := by
            simp [GeneralizedTrustRegionSubproblem.toTrustRegionSubproblem,
              GeneralizedTrustRegionSubproblem.standardizeStep, dotProduct_comm]
      _ = dotProduct P.gradient.ofLp
            (P.scalingMatrixInv.mulVec (P.scalingMatrix.mulVec s.ofLp)) := by
            simpa using
              (Matrix.dotProduct_transpose_mulVec (A := P.scalingMatrixInv)
                (x := P.scalingMatrix.mulVec s.ofLp) (y := P.gradient.ofLp))
      _ = dotProduct P.gradient.ofLp s.ofLp := by
            simp [Matrix.mulVec_mulVec, P.scalingMatrixInv_mul]
      _ = dotProduct P.gradient s := by
            rfl
  rw [hLinear]

/-- Helper for Chapter06 Exercise 6.9: solving the weighted linearized subproblem at `sG` is
equivalent to solving the ordinary standardized linearized subproblem at `D sG`. -/
theorem isLinearizedSolution_iff_standardized_isLinearizedSolution
    (P : GeneralizedTrustRegionSubproblem n) (sG : Point) :
    P.IsLinearizedSolution sG ↔
      P.toTrustRegionSubproblem.IsLinearizedSolution (P.standardizeStep sG) := by
  -- Rewrite both minimizer owners through pointwise inequalities and transport comparison points
  -- through the standardization equivalence.
  rw [P.isLinearizedSolution_iff, TrustRegionSubproblem.isLinearizedSolution_iff,
    P.mem_feasibleSet_iff_standardized_mem_feasibleSet]
  constructor
  · rintro ⟨hsG, hmin⟩
    refine ⟨hsG, ?_⟩
    intro y hy
    have hy' :=
      hmin (P.destandardizeStep y) ((P.destandardizeStep_mem_feasibleSet_iff y).2 hy)
    simpa [P.linearizedModel_eq_standardized_linearizedModel,
      P.standardizeStep_destandardizeStep y] using hy'
  · rintro ⟨hsG, hmin⟩
    refine ⟨hsG, ?_⟩
    intro s hs
    have hs' :=
      hmin (P.standardizeStep s) ((P.mem_feasibleSet_iff_standardized_mem_feasibleSet s).1 hs)
    simpa [P.linearizedModel_eq_standardized_linearizedModel] using hs'

/-- Helper for Chapter06 Exercise 6.9: a nonzero weighted gradient produces a nonzero
standardized gradient. -/
theorem inverseTransposeScaledGradient_ne_zero_of_ne_zero
    (P : GeneralizedTrustRegionSubproblem n) (h_gradient : P.gradient ≠ 0) :
    P.inverseTransposeScaledGradient ≠ 0 := by
  intro h_zero
  have h_transpose_mul :
      P.scalingMatrix.transpose * P.scalingMatrixInv.transpose = 1 := by
    simpa using congrArg Matrix.transpose P.scalingMatrixInv_mul
  have h_zero_ofLp :
      P.scalingMatrixInv.transpose.mulVec P.gradient.ofLp = 0 := by
    simpa [GeneralizedTrustRegionSubproblem.inverseTransposeScaledGradient,
      Matrix.toEuclideanLin] using congrArg WithLp.ofLp h_zero
  have h_gradient_zero :
      P.gradient.ofLp = 0 := by
    calc
      P.gradient.ofLp = (1 : MatrixN).mulVec P.gradient.ofLp := by simp
      _ = (P.scalingMatrix.transpose * P.scalingMatrixInv.transpose).mulVec P.gradient.ofLp := by
            rw [h_transpose_mul]
      _ = P.scalingMatrix.transpose.mulVec
            (P.scalingMatrixInv.transpose.mulVec P.gradient.ofLp) := by
            simp [Matrix.mulVec_mulVec]
      _ = 0 := by rw [h_zero_ofLp, Matrix.mulVec_zero]
  exact h_gradient (by simpa using h_gradient_zero)

/-- Helper for Chapter06 Exercise 6.9: standardizing the weighted steepest-descent direction
recovers the ordinary steepest-descent direction in the `y = D s` variables. -/
theorem standardizeStep_generalizedGradientDirection
    (P : GeneralizedTrustRegionSubproblem n) :
    P.standardizeStep P.generalizedGradientDirection = P.toTrustRegionSubproblem.gradient := by
  -- Push the matrix product `D (D⁻¹ D⁻ᵀ g)` to raw coordinates and cancel `D D⁻¹ = I`.
  have hmat :
      P.scalingMatrix * P.inverseWeightMatrix = P.scalingMatrixInv.transpose := by
    calc
      P.scalingMatrix * P.inverseWeightMatrix
        = P.scalingMatrix * (P.scalingMatrixInv * P.scalingMatrixInv.transpose) := by
            rfl
      _ = (P.scalingMatrix * P.scalingMatrixInv) * P.scalingMatrixInv.transpose := by
            rw [Matrix.mul_assoc]
      _ = P.scalingMatrixInv.transpose := by
            simp [P.scalingMatrix_mul_inv]
  apply WithLp.ofLp_injective
  calc
    (P.standardizeStep P.generalizedGradientDirection).ofLp
      = (P.scalingMatrix * P.inverseWeightMatrix).mulVec P.gradient.ofLp := by
          simp [GeneralizedTrustRegionSubproblem.standardizeStep,
            GeneralizedTrustRegionSubproblem.generalizedGradientDirection, Matrix.mulVec_mulVec]
    _ = P.scalingMatrixInv.transpose.mulVec P.gradient.ofLp := by rw [hmat]
    _ = P.toTrustRegionSubproblem.gradient.ofLp := by
          simp [GeneralizedTrustRegionSubproblem.toTrustRegionSubproblem]

/-- Helper for Chapter06 Exercise 6.9: standardizing the weighted boundary step gives the
ordinary boundary steepest-descent step of the standardized problem. -/
theorem standardizeStep_generalizedGradientBoundaryStep
    (P : GeneralizedTrustRegionSubproblem n) :
    P.standardizeStep P.generalizedGradientBoundaryStep =
      P.toTrustRegionSubproblem.gradientBoundaryStep := by
  by_cases h_gradient : P.gradient = 0
  · -- In the zero-gradient branch, both closed-form boundary steps collapse to `0`.
    have h_standardized_gradient : P.toTrustRegionSubproblem.gradient = 0 := by
      simp [P.toTrustRegionSubproblem_gradient_eq_inverseTransposeScaledGradient,
        GeneralizedTrustRegionSubproblem.inverseTransposeScaledGradient, h_gradient]
    rw [P.generalizedGradientBoundaryStep_eq_zero_of_eq_zero h_gradient,
      TrustRegionSubproblem.gradientBoundaryStep_eq_zero_of_eq_zero
        P.toTrustRegionSubproblem h_standardized_gradient]
    simp [GeneralizedTrustRegionSubproblem.standardizeStep]
  · -- In the nonzero branch, rewrite both steps to their explicit formulas and standardize the
    -- weighted gradient direction directly.
    have h_standardized_gradient :
        P.toTrustRegionSubproblem.gradient ≠ 0 := by
      simpa [P.toTrustRegionSubproblem_gradient_eq_inverseTransposeScaledGradient] using
        P.inverseTransposeScaledGradient_ne_zero_of_ne_zero h_gradient
    have h_standardized_gradient_norm :
        ‖P.toTrustRegionSubproblem.gradient‖ = ‖P.inverseTransposeScaledGradient‖ := by
      simp [P.toTrustRegionSubproblem_gradient_eq_inverseTransposeScaledGradient]
    rw [P.generalizedGradientBoundaryStep_eq_of_ne_zero h_gradient,
      TrustRegionSubproblem.gradientBoundaryStep_eq_of_ne_zero
        P.toTrustRegionSubproblem h_standardized_gradient]
    rw [h_standardized_gradient_norm]
    -- Push the common scalar through `standardizeStep`, then rewrite the transported direction.
    simpa [GeneralizedTrustRegionSubproblem.standardizeStep,
      GeneralizedTrustRegionSubproblem.toTrustRegionSubproblem,
      P.toTrustRegionSubproblem_gradient_eq_inverseTransposeScaledGradient] using
      congrArg
        (fun z ↦ -((P.radius / ‖P.inverseTransposeScaledGradient‖) : ℝ) • z)
        P.standardizeStep_generalizedGradientDirection

namespace TrustRegionSubproblem

/-- Helper for Chapter06 Exercise 6.9: on the ordinary Euclidean ball, a nonzero-gradient
linearized minimizer is the boundary steepest-descent step. -/
theorem gradientBoundaryStep_eq_of_isLinearizedSolution
    (Q : TrustRegionSubproblem n) {y : Point} (h_gradient : Q.gradient ≠ 0)
    (h_y : Q.IsLinearizedSolution y) :
    y = Q.gradientBoundaryStep := by
  rw [Q.isLinearizedSolution_iff] at h_y
  rcases h_y with ⟨hy_feasible, hmin⟩
  have hy_norm_le : ‖y‖ ≤ Q.radius :=
    (Q.mem_feasibleSet_iff y).1 hy_feasible
  have hlin :
      ∀ s : Point, s ∈ Q.feasibleSet → 0 ≤ dotProduct (s - y) Q.gradient := by
    intro s hs
    have hcompare : dotProduct Q.gradient y ≤ dotProduct Q.gradient s :=
      hmin s hs
    have hsub : 0 ≤ dotProduct Q.gradient s - dotProduct Q.gradient y :=
      sub_nonneg.mpr hcompare
    simpa [dotProduct_sub, dotProduct_comm, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc] using hsub
  -- The closed-ball normal-cone lemma packages the equality case of the linear minimization.
  rcases Q.exists_multiplier_of_ballLinearMin hy_norm_le hlin with
    ⟨lambdaStar, hlambda_nonneg, hresidual, hcomplementarity⟩
  have hlambda_ne : lambdaStar ≠ 0 := by
    intro hlambda_zero
    apply h_gradient
    simp [hresidual, hlambda_zero]
  have hlambda_pos : 0 < lambdaStar :=
    lt_of_le_of_ne hlambda_nonneg (Ne.symm hlambda_ne)
  have hy_boundary : ‖y‖ = Q.radius := by
    have hgap_zero : Q.radius - ‖y‖ = 0 := by
      exact (eq_zero_or_eq_zero_of_mul_eq_zero hcomplementarity).resolve_left hlambda_ne
    linarith
  have hgrad_norm :
      ‖Q.gradient‖ = lambdaStar * Q.radius := by
    calc
      ‖Q.gradient‖ = ‖-lambdaStar • y‖ := by rw [hresidual]
      _ = |(-lambdaStar : ℝ)| * ‖y‖ := norm_smul _ _
      _ = lambdaStar * Q.radius := by
            rw [abs_of_nonpos (neg_nonpos.mpr hlambda_nonneg), neg_neg, hy_boundary]
  have hscale :
      (Q.radius / ‖Q.gradient‖) * lambdaStar = 1 := by
    have hgrad_norm_ne : ‖Q.gradient‖ ≠ 0 :=
      norm_ne_zero_iff.mpr h_gradient
    calc
      (Q.radius / ‖Q.gradient‖) * lambdaStar = (Q.radius * lambdaStar) / ‖Q.gradient‖ := by ring
      _ = ‖Q.gradient‖ / ‖Q.gradient‖ := by rw [hgrad_norm, mul_comm]
      _ = 1 := by exact div_self hgrad_norm_ne
  have hy_formula :
      y = -((Q.radius / ‖Q.gradient‖) : ℝ) • Q.gradient := by
    -- Rescale the normal-cone identity to recover the explicit boundary-step formula.
    calc
      y = ((Q.radius / ‖Q.gradient‖) * lambdaStar) • y := by rw [hscale, one_smul]
      _ = -((Q.radius / ‖Q.gradient‖) : ℝ) • Q.gradient := by
            rw [hresidual]
            simp [smul_smul]
  -- Rescale the normal-cone identity to recover the explicit boundary step formula.
  calc
    y = -((Q.radius / ‖Q.gradient‖) : ℝ) • Q.gradient := hy_formula
    _ = Q.gradientBoundaryStep := by
      symm
      exact Q.gradientBoundaryStep_eq_of_ne_zero h_gradient

end TrustRegionSubproblem

/-- Expanding `IsGeneralizedCauchyScale` gives the source positive-ray minimization statement. -/
theorem isGeneralizedCauchyScale_iff
    (P : GeneralizedTrustRegionSubproblem n) (τk : ℝ) :
    P.IsGeneralizedCauchyScale τk ↔
      0 < τk ∧
        τk • P.generalizedGradientBoundaryStep ∈ P.feasibleSet ∧
          ∀ τ : ℝ, 0 < τ → τ • P.generalizedGradientBoundaryStep ∈ P.feasibleSet →
            P.quadraticModel (τk • P.generalizedGradientBoundaryStep) ≤
              P.quadraticModel (τ • P.generalizedGradientBoundaryStep) := by
  rw [isGeneralizedCauchyScale_iff_mem_generalizedGradientScaleFeasibleSet_and_isMinOn,
    generalizedGradientScaleFeasibleSet,
    isMinOn_iff]
  constructor
  · rintro ⟨⟨hτk, hτk_feasible⟩, hmin⟩
    refine ⟨hτk, hτk_feasible, ?_⟩
    intro τ hτ hτ_feasible
    exact hmin τ ⟨hτ, hτ_feasible⟩
  · rintro ⟨hτk, hτk_feasible, hmin⟩
    refine ⟨⟨hτk, hτk_feasible⟩, ?_⟩
    intro τ hτ
    exact hmin τ hτ.1 hτ.2

/-- A step is a generalized Cauchy point when it is feasible, lies on the positive ray through
`s_k^G`, and minimizes `q^(k)` among feasible ray points `s = τ s_k^G`. -/
def IsGeneralizedCauchyPointOnGradientRay
    (P : GeneralizedTrustRegionSubproblem n) (sC : Point) : Prop :=
  sC ∈ P.generalizedGradientRayFeasibleSet ∧
    IsMinOn P.quadraticModel P.generalizedGradientRayFeasibleSet sC

/-- `IsGeneralizedCauchyPointOnGradientRay` keeps the source-facing feasible-ray clause and
packages weighted ray minimization through the canonical `IsMinOn` owner. -/
theorem
    isGeneralizedCauchyPointOnGradientRay_iff_mem_generalizedGradientRayFeasibleSet_and_isMinOn
    (P : GeneralizedTrustRegionSubproblem n) (sC : Point) :
    P.IsGeneralizedCauchyPointOnGradientRay sC ↔
      sC ∈ P.generalizedGradientRayFeasibleSet ∧
        IsMinOn P.quadraticModel P.generalizedGradientRayFeasibleSet sC :=
  Iff.rfl

/-- Expanding `IsGeneralizedCauchyPointOnGradientRay` gives the source positive-ray
characterization. -/
theorem isGeneralizedCauchyPointOnGradientRay_iff
    (P : GeneralizedTrustRegionSubproblem n) (sC : Point) :
    P.IsGeneralizedCauchyPointOnGradientRay sC ↔
      sC ∈ P.feasibleSet ∧
        ∃ τC : ℝ, 0 < τC ∧ sC = τC • P.generalizedGradientBoundaryStep ∧
          ∀ s : Point, (∃ τ : ℝ, 0 < τ ∧ s = τ • P.generalizedGradientBoundaryStep) →
            s ∈ P.feasibleSet → P.quadraticModel sC ≤ P.quadraticModel s := by
  rw [isGeneralizedCauchyPointOnGradientRay_iff_mem_generalizedGradientRayFeasibleSet_and_isMinOn,
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

/-- The generalized Cauchy scale `τ_k` given by the weighted closed formula:
`τ_k = 1` if `g_kᵀ (Dᵀ D)⁻¹ B_k (Dᵀ D)⁻¹ g_k ≤ 0`, and otherwise
`τ_k = min (‖D⁻ᵀ g_k‖₂^3 / (Δ_k (g_kᵀ (Dᵀ D)⁻¹ B_k (Dᵀ D)⁻¹ g_k))) 1`.
Under symmetry of `D`, this reduces to the source formula (6.3.68). -/
def generalizedCauchyScale (P : GeneralizedTrustRegionSubproblem n) : ℝ :=
  if P.generalizedGradientCurvature ≤ 0 then 1
  else
    min
      ((‖P.inverseTransposeScaledGradient‖ ^ (3 : ℕ)) /
        (P.radius * P.generalizedGradientCurvature))
      1

/-- The generalized Cauchy point `s_k^c = τ_k s_k^G` built from the weighted closed formula
for `τ_k`. Its source ray-minimization property is recorded separately. -/
def generalizedCauchyPoint (P : GeneralizedTrustRegionSubproblem n) : Point :=
  P.generalizedCauchyScale • P.generalizedGradientBoundaryStep

section

variable (P : GeneralizedTrustRegionSubproblem n)

/-- Part (1) of Chapter06 Exercise 6.9: if `g_k ≠ 0` and `s_k^G` solves the linearized weighted
trust-region subproblem
`min f(x_k) + g_kᵀ s` subject to `‖D s‖ ≤ Δ_k`, then
`s_k^G = -(Δ_k / ‖D⁻ᵀ g_k‖₂) (Dᵀ D)⁻¹ g_k`. Under symmetry of `D`, this is the source
formula `-(Δ_k / ‖D⁻¹ g_k‖₂) D⁻² g_k`. -/
theorem generalizedGradientBoundaryStep_eq_of_isLinearizedSolution
    {sG : Point} (h_gradient : P.gradient ≠ 0) (h_sG : P.IsLinearizedSolution sG) :
    sG = P.generalizedGradientBoundaryStep := by
  let Q := P.toTrustRegionSubproblem
  have h_standardized_solution :
      Q.IsLinearizedSolution (P.standardizeStep sG) := by
    exact (P.isLinearizedSolution_iff_standardized_isLinearizedSolution sG).1 h_sG
  have h_standardized_gradient : Q.gradient ≠ 0 := by
    simpa [Q, P.toTrustRegionSubproblem_gradient_eq_inverseTransposeScaledGradient] using
      P.inverseTransposeScaledGradient_ne_zero_of_ne_zero h_gradient
  have h_standardized_eq :
      P.standardizeStep sG = Q.gradientBoundaryStep := by
    exact
      TrustRegionSubproblem.gradientBoundaryStep_eq_of_isLinearizedSolution Q
        h_standardized_gradient h_standardized_solution
  have h_destandardized_boundary :
      P.destandardizeStep Q.gradientBoundaryStep = P.generalizedGradientBoundaryStep := by
    -- Route correction: use the explicit standardization bridge and then invert the change of
    -- variables once, instead of transporting minimizer predicates again.
    simpa [Q, P.destandardizeStep_standardizeStep] using
      (congrArg P.destandardizeStep P.standardizeStep_generalizedGradientBoundaryStep).symm
  -- Applying `D⁻¹` to the standardized equality returns the weighted-space step.
  calc
    sG = P.destandardizeStep (P.standardizeStep sG) := by
      symm
      exact P.destandardizeStep_standardizeStep sG
    _ = P.destandardizeStep Q.gradientBoundaryStep := by rw [h_standardized_eq]
    _ = P.generalizedGradientBoundaryStep := h_destandardized_boundary

/-- Helper for Chapter06 Exercise 6.9: the standardized curvature scalar is exactly the weighted
curvature `g_kᵀ (Dᵀ D)⁻¹ B_k (Dᵀ D)⁻¹ g_k`. -/
theorem toTrustRegionSubproblem_gradientCurvature_eq_generalizedGradientCurvature :
    P.toTrustRegionSubproblem.gradientCurvature = P.generalizedGradientCurvature := by
  -- Evaluate both quadratic forms in raw coordinates and collapse the two `D⁻¹` factors into
  -- the stored inverse-weight matrix.
  rw [TrustRegionSubproblem.gradientCurvature,
    GeneralizedTrustRegionSubproblem.generalizedGradientCurvature]
  calc
    dotProduct P.toTrustRegionSubproblem.gradient
        (P.toTrustRegionSubproblem.hessianApprox.mulVec P.toTrustRegionSubproblem.gradient)
      =
        dotProduct (P.scalingMatrixInv.transpose.mulVec P.gradient.ofLp)
          (P.scalingMatrixInv.transpose.mulVec
            ((P.hessianApprox * P.inverseWeightMatrix).mulVec P.gradient.ofLp)) := by
          simp [GeneralizedTrustRegionSubproblem.toTrustRegionSubproblem,
            GeneralizedTrustRegionSubproblem.inverseWeightMatrix, Matrix.mulVec_mulVec,
            Matrix.mul_assoc]
    _ =
        dotProduct P.gradient.ofLp
          (P.scalingMatrixInv.mulVec
            ((P.scalingMatrixInv.transpose.mulVec
              ((P.hessianApprox * P.inverseWeightMatrix).mulVec P.gradient.ofLp)))) := by
          rw [dotProduct_comm]
          simpa using
            (Matrix.dotProduct_transpose_mulVec (A := P.scalingMatrixInv)
              (x := P.scalingMatrixInv.transpose.mulVec
                ((P.hessianApprox * P.inverseWeightMatrix).mulVec P.gradient.ofLp))
              (y := P.gradient.ofLp))
    _ =
        dotProduct P.gradient.ofLp
          ((P.inverseWeightMatrix * P.hessianApprox * P.inverseWeightMatrix).mulVec
            P.gradient.ofLp) := by
          rw [Matrix.mul_assoc]
          simp [GeneralizedTrustRegionSubproblem.inverseWeightMatrix,
            Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = dotProduct P.gradient
          (Matrix.toEuclideanLin
            (P.inverseWeightMatrix * P.hessianApprox * P.inverseWeightMatrix) P.gradient) := by
          rw [Matrix.mul_assoc]
          rfl

/-- Helper for Chapter06 Exercise 6.9: the weighted explicit scale is exactly the ordinary
Cauchy-point scale of the standardized problem. -/
theorem generalizedCauchyScale_eq_toTrustRegionSubproblem_cauchyPointScale :
    P.generalizedCauchyScale = P.toTrustRegionSubproblem.cauchyPointScale := by
  -- Rewrite the weighted source formula through the standardized gradient and curvature bridges.
  rw [GeneralizedTrustRegionSubproblem.generalizedCauchyScale,
    TrustRegionSubproblem.cauchyPointScale,
    P.toTrustRegionSubproblem_gradientCurvature_eq_generalizedGradientCurvature]
  rw [P.toTrustRegionSubproblem_gradient_eq_inverseTransposeScaledGradient]
  simp [GeneralizedTrustRegionSubproblem.toTrustRegionSubproblem]

/-- Helper for Chapter06 Exercise 6.9: standardizing a scaled weighted boundary step gives the
same scale applied to the standardized boundary step. -/
theorem standardizeStep_smul_generalizedGradientBoundaryStep (τ : ℝ) :
    P.standardizeStep (τ • P.generalizedGradientBoundaryStep) =
      τ • P.toTrustRegionSubproblem.gradientBoundaryStep := by
  -- Standardization is linear, so the scale may be pushed directly through `D`.
  calc
    P.standardizeStep (τ • P.generalizedGradientBoundaryStep)
      = τ • P.standardizeStep P.generalizedGradientBoundaryStep := by
          simp [GeneralizedTrustRegionSubproblem.standardizeStep]
    _ = τ • P.toTrustRegionSubproblem.gradientBoundaryStep := by
          rw [P.standardizeStep_generalizedGradientBoundaryStep]

/-- Helper for Chapter06 Exercise 6.9: for a nonzero weighted gradient, the feasible scales on
the weighted boundary-step ray are exactly the interval `[-1, 1]`. -/
theorem smul_generalizedGradientBoundaryStep_mem_feasibleSet_iff
    (h_gradient : P.gradient ≠ 0) (τ : ℝ) :
    τ • P.generalizedGradientBoundaryStep ∈ P.feasibleSet ↔ |τ| ≤ 1 := by
  let Q := P.toTrustRegionSubproblem
  have h_standardized_gradient : Q.gradient ≠ 0 := by
    simpa [Q, P.toTrustRegionSubproblem_gradient_eq_inverseTransposeScaledGradient] using
      P.inverseTransposeScaledGradient_ne_zero_of_ne_zero h_gradient
  have h_boundary_norm : ‖Q.gradientBoundaryStep‖ = Q.radius := by
    -- Rewrite the standardized boundary step to its explicit formula and simplify the norm.
    rw [TrustRegionSubproblem.gradientBoundaryStep_eq_of_ne_zero Q h_standardized_gradient]
    have h_gradient_norm_pos : 0 < ‖Q.gradient‖ := norm_pos_iff.mpr h_standardized_gradient
    calc
      ‖-((Q.radius / ‖Q.gradient‖) : ℝ) • Q.gradient‖
        = ‖Q.radius / ‖Q.gradient‖‖ * ‖Q.gradient‖ := by
            simpa using (norm_smul ((Q.radius / ‖Q.gradient‖) : ℝ) Q.gradient)
      _ = (Q.radius / ‖Q.gradient‖) * ‖Q.gradient‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg Q.radius_pos.le (norm_nonneg _))]
      _ = Q.radius := by
            field_simp [h_gradient_norm_pos.ne']
  -- Transport the weighted feasibility test to the standardized ball, then normalize the radius.
  calc
    τ • P.generalizedGradientBoundaryStep ∈ P.feasibleSet
      ↔ P.standardizeStep (τ • P.generalizedGradientBoundaryStep) ∈ Q.feasibleSet := by
          exact P.mem_feasibleSet_iff_standardized_mem_feasibleSet _
    _ ↔ τ • Q.gradientBoundaryStep ∈ Q.feasibleSet := by
          rw [P.standardizeStep_smul_generalizedGradientBoundaryStep]
    _ ↔ ‖τ • Q.gradientBoundaryStep‖ ≤ Q.radius := by
          rw [TrustRegionSubproblem.mem_feasibleSet_iff]
    _ ↔ |τ| * Q.radius ≤ Q.radius := by
          rw [norm_smul, Real.norm_eq_abs, h_boundary_norm]
    _ ↔ |τ| ≤ 1 := by
          constructor
          · intro h
            nlinarith [h, Q.radius_pos]
          · intro h
            nlinarith [h, Q.radius_pos]

/-- The explicit scale `τ_k` from (6.3.68) satisfies the source ray-minimization
specification. -/
theorem generalizedCauchyScale_isGeneralizedCauchyScale :
    P.IsGeneralizedCauchyScale P.generalizedCauchyScale := by
  by_cases h_gradient : P.gradient = 0
  · -- In the degenerate branch, every positive scale is optimal because the ray collapses to `0`.
    rw [P.isGeneralizedCauchyScale_iff_of_eq_zero P.generalizedCauchyScale h_gradient]
    simp [GeneralizedTrustRegionSubproblem.generalizedCauchyScale,
      GeneralizedTrustRegionSubproblem.generalizedGradientCurvature, h_gradient]
  · let Q := P.toTrustRegionSubproblem
    have h_standardized_gradient : Q.gradient ≠ 0 := by
      simpa [Q, P.toTrustRegionSubproblem_gradient_eq_inverseTransposeScaledGradient] using
        P.inverseTransposeScaledGradient_ne_zero_of_ne_zero h_gradient
    have h_scale_eq :
        P.generalizedCauchyScale = Q.cauchyPointScale := by
      simpa [Q] using P.generalizedCauchyScale_eq_toTrustRegionSubproblem_cauchyPointScale
    have h_scale_pos : 0 < P.generalizedCauchyScale := by
      -- The explicit weighted scale is positive in both curvature branches.
      by_cases h_curv : P.generalizedGradientCurvature ≤ 0
      · rw [GeneralizedTrustRegionSubproblem.generalizedCauchyScale, if_pos h_curv]
        norm_num
      · have h_curv_pos : 0 < P.generalizedGradientCurvature := lt_of_not_ge h_curv
        have h_gradient_norm_pos :
            0 < ‖P.inverseTransposeScaledGradient‖ := by
          exact norm_pos_iff.mpr (P.inverseTransposeScaledGradient_ne_zero_of_ne_zero h_gradient)
        have h_ratio_pos :
            0 <
              (‖P.inverseTransposeScaledGradient‖ ^ (3 : ℕ)) /
                (P.radius * P.generalizedGradientCurvature) := by
          exact div_pos (pow_pos h_gradient_norm_pos _) (mul_pos P.radius_pos h_curv_pos)
        rw [GeneralizedTrustRegionSubproblem.generalizedCauchyScale, if_neg h_curv]
        exact lt_min h_ratio_pos zero_lt_one
    rw [P.isGeneralizedCauchyScale_iff]
    refine ⟨h_scale_pos, ?_, ?_⟩
    · -- Transport the ordinary Cauchy point's feasibility back through the change of variables.
      have hQcauchy := Q.cauchyPoint_isCauchyPointOnGradientRay
      rw [TrustRegionSubproblem.isCauchyPointOnGradientRay_iff] at hQcauchy
      rcases hQcauchy with ⟨hQcauchy_feasible, _, _, _, _⟩
      have hQscale_feasible :
          Q.cauchyPointScale • Q.gradientBoundaryStep ∈ Q.feasibleSet := by
        simpa [TrustRegionSubproblem.cauchyPoint_eq] using hQcauchy_feasible
      have h_standardized_feasible :
          P.standardizeStep (P.generalizedCauchyScale • P.generalizedGradientBoundaryStep) ∈
            Q.feasibleSet := by
        simpa [Q, h_scale_eq, P.standardizeStep_smul_generalizedGradientBoundaryStep] using
          hQscale_feasible
      exact (P.mem_feasibleSet_iff_standardized_mem_feasibleSet _).2 h_standardized_feasible
    · intro τ hτ_pos hτ_feasible
      have hQcauchy := Q.cauchyPoint_isCauchyPointOnGradientRay
      rw [TrustRegionSubproblem.isCauchyPointOnGradientRay_iff] at hQcauchy
      rcases hQcauchy with ⟨_, _, _, _, hQmin⟩
      have h_standardized_feasible :
          τ • Q.gradientBoundaryStep ∈ Q.feasibleSet := by
        have hPfeasible :
            P.standardizeStep (τ • P.generalizedGradientBoundaryStep) ∈ Q.feasibleSet :=
          (P.mem_feasibleSet_iff_standardized_mem_feasibleSet _).1 hτ_feasible
        simpa [Q, P.standardizeStep_smul_generalizedGradientBoundaryStep] using hPfeasible
      have hQineq :
          Q.quadraticModel (Q.cauchyPointScale • Q.gradientBoundaryStep) ≤
            Q.quadraticModel (τ • Q.gradientBoundaryStep) := by
        simpa [TrustRegionSubproblem.cauchyPoint_eq] using
          hQmin (τ • Q.gradientBoundaryStep) ⟨τ, le_of_lt hτ_pos, rfl⟩ h_standardized_feasible
      -- Route correction: compare scalar values in the standardized problem first, then transport
      -- the inequality back to the weighted model.
      simpa [Q, h_scale_eq, P.standardizeStep_smul_generalizedGradientBoundaryStep,
        P.quadraticModel_eq_standardized_quadraticModel] using hQineq

/-- Part (2) of Chapter06 Exercise 6.9: the generalized Cauchy point `s_k^c` is characterized by the
source minimization property
`q^(k) (s_k^c) = min { q^(k) (s) | s = τ s_k^G, ‖D s‖ ≤ Δ_k }`
along the positive ray through `s_k^G`. -/
theorem generalizedCauchyPoint_isGeneralizedCauchyPointOnGradientRay :
    P.IsGeneralizedCauchyPointOnGradientRay P.generalizedCauchyPoint := by
  -- Repackage the scale-level minimizer directly as a point-level minimizer on the same ray.
  have h_scale_min : P.IsGeneralizedCauchyScale P.generalizedCauchyScale :=
    P.generalizedCauchyScale_isGeneralizedCauchyScale
  rw [P.isGeneralizedCauchyPointOnGradientRay_iff]
  rw [P.isGeneralizedCauchyScale_iff] at h_scale_min
  rcases h_scale_min with ⟨hτ_pos, hτ_feasible, hτ_min⟩
  refine ⟨?_, P.generalizedCauchyScale, hτ_pos, rfl, ?_⟩
  · simpa [GeneralizedTrustRegionSubproblem.generalizedCauchyPoint] using hτ_feasible
  · intro s hs_ray hs_feasible
    rcases hs_ray with ⟨τ, hτ, rfl⟩
    simpa [GeneralizedTrustRegionSubproblem.generalizedCauchyPoint] using
      hτ_min τ hτ hs_feasible

/-- Part (3) of Chapter06 Exercise 6.9: if `g_k ≠ 0`, every generalized Cauchy point on the
weighted-gradient ray has the explicit form
`s_k^c = τ_k s_k^G = -(τ_k Δ_k / ‖D⁻ᵀ g_k‖₂) (Dᵀ D)⁻¹ g_k` for some generalized Cauchy
scale `τ_k`. Under symmetry of `D`, this is the source formula (6.3.67). -/
theorem generalizedCauchyPoint_eq
    {sC : Point} (h_gradient : P.gradient ≠ 0)
    (h_sC : P.IsGeneralizedCauchyPointOnGradientRay sC) :
    ∃ τk : ℝ, P.IsGeneralizedCauchyScale τk ∧
      sC =
        -((τk * P.radius / ‖P.inverseTransposeScaledGradient‖) : ℝ) •
          P.generalizedGradientDirection := by
  rw [P.isGeneralizedCauchyPointOnGradientRay_iff] at h_sC
  rcases h_sC with ⟨hsC_feasible, τk, hτk_pos, hsC_ray, hmin⟩
  refine ⟨τk, ?_, ?_⟩
  · -- Reuse the point-minimality clause on the specific ray point `τ • s_k^G`.
    rw [P.isGeneralizedCauchyScale_iff]
    refine ⟨hτk_pos, ?_, ?_⟩
    · simpa [hsC_ray] using hsC_feasible
    · intro τ hτ hτ_feasible
      simpa [hsC_ray] using
        hmin (τ • P.generalizedGradientBoundaryStep) ⟨τ, hτ, rfl⟩ hτ_feasible
  · -- Rewrite the ray point using the explicit boundary-step formula from part (1).
    calc
      sC = τk • P.generalizedGradientBoundaryStep := hsC_ray
      _ =
          τk •
            (-((P.radius / ‖P.inverseTransposeScaledGradient‖) : ℝ) •
              P.generalizedGradientDirection) := by
              rw [P.generalizedGradientBoundaryStep_eq_of_ne_zero h_gradient]
      _ =
          -((τk * P.radius / ‖P.inverseTransposeScaledGradient‖) : ℝ) •
            P.generalizedGradientDirection := by
              rw [smul_smul]
              ring_nf

/-- Helper for Chapter06 Exercise 6.9: when the weighted gradient is nonzero, any generalized
Cauchy scale must agree with the stored explicit scale. -/
theorem eq_generalizedCauchyScale_of_isGeneralizedCauchyScale
    {τk : ℝ} (h_gradient : P.gradient ≠ 0) (h_tau : P.IsGeneralizedCauchyScale τk) :
    τk = P.generalizedCauchyScale := by
  let Q := P.toTrustRegionSubproblem
  have h_standardized_gradient : Q.gradient ≠ 0 := by
    simpa [Q, P.toTrustRegionSubproblem_gradient_eq_inverseTransposeScaledGradient] using
      P.inverseTransposeScaledGradient_ne_zero_of_ne_zero h_gradient
  have h_gradient_norm_pos : 0 < ‖Q.gradient‖ := norm_pos_iff.mpr h_standardized_gradient
  have h_tau_scale_eq :
      P.generalizedCauchyScale = Q.cauchyPointScale := by
    simpa [Q] using P.generalizedCauchyScale_eq_toTrustRegionSubproblem_cauchyPointScale
  rw [P.isGeneralizedCauchyScale_iff] at h_tau
  rcases h_tau with ⟨hτ_pos, hτ_feasible, hτ_min⟩
  have hτ_le_one : τk ≤ 1 := by
    have hτ_abs :
        |τk| ≤ 1 := (P.smul_generalizedGradientBoundaryStep_mem_feasibleSet_iff h_gradient τk).1
          hτ_feasible
    simpa [abs_of_pos hτ_pos] using hτ_abs
  have h_predictedReduction_on_ray (τ : ℝ) :
      Q.predictedReduction (τ • Q.gradientBoundaryStep) =
        τ * Q.radius * ‖Q.gradient‖ -
          (1 / 2 : ℝ) * τ ^ (2 : ℕ) * Q.radius ^ (2 : ℕ) * Q.gradientCurvature /
            (‖Q.gradient‖ ^ (2 : ℕ)) := by
    -- Rewrite the standardized boundary step to the explicit negative-gradient step once, then
    -- specialize the ordinary scalar predicted-reduction formula.
    rw [TrustRegionSubproblem.gradientBoundaryStep_eq_of_ne_zero Q h_standardized_gradient]
    calc
      Q.predictedReduction (τ • (-((Q.radius / ‖Q.gradient‖) : ℝ) • Q.gradient))
        =
          (τ * (Q.radius / ‖Q.gradient‖)) * ‖Q.gradient‖ ^ (2 : ℕ) -
            (1 / 2 : ℝ) * (τ * (Q.radius / ‖Q.gradient‖)) ^ (2 : ℕ) * Q.gradientCurvature := by
              simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
                (TrustRegionSubproblem.predictedReduction_eq_negGradientStep Q
                  (τ * (Q.radius / ‖Q.gradient‖)))
      _ =
          τ * Q.radius * ‖Q.gradient‖ -
            (1 / 2 : ℝ) * τ ^ (2 : ℕ) * Q.radius ^ (2 : ℕ) * Q.gradientCurvature /
              (‖Q.gradient‖ ^ (2 : ℕ)) := by
            field_simp [pow_two, h_gradient_norm_pos.ne']
  have h_predictedReduction_rho_form :
      ∀ τ : ℝ,
        Q.predictedReduction (τ • Q.gradientBoundaryStep) =
          Q.radius * ‖Q.gradient‖ * τ -
            ((Q.radius * ‖Q.gradient‖) / (2 * ((‖Q.gradient‖ ^ (3 : ℕ)) /
              (Q.radius * Q.gradientCurvature)))) * τ ^ (2 : ℕ) := by
    intro τ
    rw [h_predictedReduction_on_ray τ]
    by_cases h_curv : Q.gradientCurvature = 0
    · simp [h_curv, mul_comm, mul_left_comm, mul_assoc]
    · field_simp [pow_two, h_gradient_norm_pos.ne', (ne_of_gt Q.radius_pos), h_curv]
  have h_predictedReduction_max :
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
        Q.predictedReduction (τ • Q.gradientBoundaryStep) ≤
          Q.predictedReduction (τk • Q.gradientBoundaryStep) := by
    intro τ hτ_pos hτ_le_one
    have hτ_feasible_weighted : τ • P.generalizedGradientBoundaryStep ∈ P.feasibleSet := by
      have hτ_abs : |τ| ≤ 1 := by simpa [abs_of_pos hτ_pos] using hτ_le_one
      exact (P.smul_generalizedGradientBoundaryStep_mem_feasibleSet_iff h_gradient τ).2 hτ_abs
    have hQineq :
        Q.quadraticModel (τk • Q.gradientBoundaryStep) ≤
          Q.quadraticModel (τ • Q.gradientBoundaryStep) := by
      have hPineq :
          P.quadraticModel (τk • P.generalizedGradientBoundaryStep) ≤
            P.quadraticModel (τ • P.generalizedGradientBoundaryStep) :=
        hτ_min τ hτ_pos hτ_feasible_weighted
      simpa [Q, P.standardizeStep_smul_generalizedGradientBoundaryStep,
        P.quadraticModel_eq_standardized_quadraticModel] using hPineq
    have hPred :
        Q.predictedReduction (τ • Q.gradientBoundaryStep) ≤
          Q.predictedReduction (τk • Q.gradientBoundaryStep) := by
      rw [TrustRegionSubproblem.predictedReduction_eq, TrustRegionSubproblem.predictedReduction_eq]
      linarith
    exact hPred
  by_cases h_curv : Q.gradientCurvature ≤ 0
  · -- In the nonpositive-curvature branch, the scalar predicted reduction keeps increasing up to
    -- the boundary, so every minimizing scale must equal `1`.
    have hcompare :
        Q.predictedReduction ((1 : ℝ) • Q.gradientBoundaryStep) ≤
          Q.predictedReduction (τk • Q.gradientBoundaryStep) :=
      h_predictedReduction_max (1 : ℝ) zero_lt_one le_rfl
    have hboundary_formula (τ : ℝ) :
        Q.predictedReduction ((1 : ℝ) • Q.gradientBoundaryStep) -
            Q.predictedReduction (τ • Q.gradientBoundaryStep) =
          Q.radius * (1 - τ) *
              (2 * ‖Q.gradient‖ ^ (3 : ℕ) - Q.radius * Q.gradientCurvature * (1 + τ)) /
            (2 * ‖Q.gradient‖ ^ (2 : ℕ)) := by
      rw [h_predictedReduction_on_ray (1 : ℝ), h_predictedReduction_on_ray τ]
      field_simp [pow_two, h_gradient_norm_pos.ne']
      ring
    have hτ_eq_one : τk = 1 := by
      by_contra hτ_ne_one
      have hτ_lt_one : τk < 1 := lt_of_le_of_ne hτ_le_one hτ_ne_one
      have hfactor_pos :
          0 < 2 * ‖Q.gradient‖ ^ (3 : ℕ) - Q.radius * Q.gradientCurvature * (1 + τk) := by
        have hnorm_cube_pos : 0 < ‖Q.gradient‖ ^ (3 : ℕ) := by
          exact pow_pos h_gradient_norm_pos _
        have h_one_add_pos : 0 < 1 + τk := by nlinarith
        have hcurv_term_nonpos :
            Q.radius * Q.gradientCurvature * (1 + τk) ≤ 0 := by
          have hradius_curv_nonpos : Q.radius * Q.gradientCurvature ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos Q.radius_pos.le h_curv
          exact mul_nonpos_of_nonpos_of_nonneg hradius_curv_nonpos h_one_add_pos.le
        nlinarith [hnorm_cube_pos, hcurv_term_nonpos]
      have hdiff_nonpos :
          Q.predictedReduction ((1 : ℝ) • Q.gradientBoundaryStep) -
              Q.predictedReduction (τk • Q.gradientBoundaryStep) ≤ 0 := by
        linarith
      rw [hboundary_formula τk] at hdiff_nonpos
      have hden_pos : 0 < 2 * ‖Q.gradient‖ ^ (2 : ℕ) := by
        have hnorm_sq_pos : 0 < ‖Q.gradient‖ ^ (2 : ℕ) := by
          exact pow_pos h_gradient_norm_pos _
        nlinarith
      have hdiff_pos :
          0 <
            Q.radius * (1 - τk) *
                (2 * ‖Q.gradient‖ ^ (3 : ℕ) - Q.radius * Q.gradientCurvature * (1 + τk)) /
              (2 * ‖Q.gradient‖ ^ (2 : ℕ)) := by
        exact div_pos (mul_pos (mul_pos Q.radius_pos (sub_pos.mpr hτ_lt_one)) hfactor_pos) hden_pos
      linarith
    rw [hτ_eq_one, h_tau_scale_eq,
      TrustRegionSubproblem.cauchyPointScale_eq_one_of_nonpos_curvature Q h_curv]
  · have h_curv_pos : 0 < Q.gradientCurvature := lt_of_not_ge h_curv
    let ρ : ℝ := (‖Q.gradient‖ ^ (3 : ℕ)) / (Q.radius * Q.gradientCurvature)
    have hρ_pos : 0 < ρ := by
      unfold ρ
      exact div_pos (pow_pos h_gradient_norm_pos _) (mul_pos Q.radius_pos h_curv_pos)
    by_cases hρ_le_one : ρ ≤ 1
    · -- In the interior branch, the scalar model is maximized uniquely at the critical ratio `ρ`.
      have hcompare :
          Q.predictedReduction (ρ • Q.gradientBoundaryStep) ≤
            Q.predictedReduction (τk • Q.gradientBoundaryStep) :=
        h_predictedReduction_max ρ hρ_pos hρ_le_one
      have hcoeff_pos :
          0 < (Q.radius * ‖Q.gradient‖) / (2 * ρ) := by
        have hnum_pos : 0 < Q.radius * ‖Q.gradient‖ := mul_pos Q.radius_pos h_gradient_norm_pos
        have hden_pos : 0 < 2 * ρ := by nlinarith
        exact div_pos hnum_pos hden_pos
      have hsquare_formula (τ : ℝ) :
          Q.predictedReduction (ρ • Q.gradientBoundaryStep) -
              Q.predictedReduction (τ • Q.gradientBoundaryStep) =
            ((Q.radius * ‖Q.gradient‖) / (2 * ρ)) * (τ - ρ) ^ (2 : ℕ) := by
        rw [h_predictedReduction_rho_form ρ, h_predictedReduction_rho_form τ]
        unfold ρ
        field_simp [ρ, pow_two, h_gradient_norm_pos.ne', (ne_of_gt Q.radius_pos), h_curv_pos.ne']
        ring_nf
      have hbest :
          Q.predictedReduction (τk • Q.gradientBoundaryStep) ≤
            Q.predictedReduction (ρ • Q.gradientBoundaryStep) := by
        have hdiff_nonneg :
            0 ≤ Q.predictedReduction (ρ • Q.gradientBoundaryStep) -
              Q.predictedReduction (τk • Q.gradientBoundaryStep) := by
          rw [hsquare_formula τk]
          exact mul_nonneg hcoeff_pos.le (sq_nonneg _)
        linarith
      have h_eq :
          Q.predictedReduction (τk • Q.gradientBoundaryStep) =
            Q.predictedReduction (ρ • Q.gradientBoundaryStep) :=
        le_antisymm hbest hcompare
      have hsquare_zero :
          ((τk - ρ) : ℝ) ^ (2 : ℕ) = 0 := by
        have hdiff_zero :
            Q.predictedReduction (ρ • Q.gradientBoundaryStep) -
              Q.predictedReduction (τk • Q.gradientBoundaryStep) = 0 := by
          linarith
        rw [hsquare_formula τk] at hdiff_zero
        nlinarith [hcoeff_pos, sq_nonneg (τk - ρ)]
      have hτ_eq_ρ : τk = ρ := by
        nlinarith [hsquare_zero]
      rw [hτ_eq_ρ, h_tau_scale_eq,
        TrustRegionSubproblem.cauchyPointScale_eq_min_of_pos_curvature Q h_curv_pos,
        min_eq_left hρ_le_one]
    · -- If the critical ratio exceeds `1`, the scalar model keeps improving up to the boundary.
      have hρ_gt_one : 1 < ρ := lt_of_not_ge hρ_le_one
      have hcompare :
          Q.predictedReduction ((1 : ℝ) • Q.gradientBoundaryStep) ≤
            Q.predictedReduction (τk • Q.gradientBoundaryStep) :=
        h_predictedReduction_max (1 : ℝ) zero_lt_one le_rfl
      have hboundary_formula (τ : ℝ) :
          Q.predictedReduction ((1 : ℝ) • Q.gradientBoundaryStep) -
              Q.predictedReduction (τ • Q.gradientBoundaryStep) =
            Q.radius * ‖Q.gradient‖ * (1 - τ) * (1 - (1 + τ) / (2 * ρ)) := by
        rw [h_predictedReduction_rho_form (1 : ℝ), h_predictedReduction_rho_form τ]
        unfold ρ
        field_simp [ρ, pow_two, h_gradient_norm_pos.ne', (ne_of_gt Q.radius_pos), h_curv_pos.ne']
        ring_nf
      have hbest :
          Q.predictedReduction (τk • Q.gradientBoundaryStep) ≤
            Q.predictedReduction ((1 : ℝ) • Q.gradientBoundaryStep) := by
        have h_two_rho_pos : 0 < 2 * ρ := by nlinarith
        have h_one_add_le : 1 + τk ≤ 2 * ρ := by nlinarith [hτ_le_one, hρ_gt_one]
        have htail_nonneg : 0 ≤ 1 - (1 + τk) / (2 * ρ) := by
          have hden_ne : (2 * ρ : ℝ) ≠ 0 := ne_of_gt h_two_rho_pos
          field_simp [hden_ne]
          nlinarith
        have hdiff_nonneg :
            0 ≤ Q.predictedReduction ((1 : ℝ) • Q.gradientBoundaryStep) -
              Q.predictedReduction (τk • Q.gradientBoundaryStep) := by
          rw [hboundary_formula τk]
          exact mul_nonneg (mul_nonneg (mul_nonneg Q.radius_pos.le h_gradient_norm_pos.le)
            (sub_nonneg.mpr hτ_le_one)) htail_nonneg
        linarith
      have h_eq :
          Q.predictedReduction (τk • Q.gradientBoundaryStep) =
            Q.predictedReduction ((1 : ℝ) • Q.gradientBoundaryStep) :=
        le_antisymm hbest hcompare
      have hτ_eq_one : τk = 1 := by
        have hdiff_zero :
            Q.predictedReduction ((1 : ℝ) • Q.gradientBoundaryStep) -
              Q.predictedReduction (τk • Q.gradientBoundaryStep) = 0 := by
          linarith
        rw [hboundary_formula τk] at hdiff_zero
        have h_two_rho_pos : 0 < 2 * ρ := by nlinarith
        have h_one_add_lt : 1 + τk < 2 * ρ := by nlinarith [hτ_le_one, hρ_gt_one]
        have htail_pos : 0 < 1 - (1 + τk) / (2 * ρ) := by
          have hden_ne : (2 * ρ : ℝ) ≠ 0 := ne_of_gt h_two_rho_pos
          field_simp [hden_ne]
          nlinarith
        have hnum_pos : 0 < Q.radius * ‖Q.gradient‖ := mul_pos Q.radius_pos h_gradient_norm_pos
        by_contra hτ_ne_one
        have hτ_lt_one : τk < 1 := lt_of_le_of_ne hτ_le_one hτ_ne_one
        have hprod_pos :
            0 < Q.radius * ‖Q.gradient‖ * (1 - τk) * (1 - (1 + τk) / (2 * ρ)) := by
          exact mul_pos (mul_pos hnum_pos (sub_pos.mpr hτ_lt_one)) htail_pos
        linarith
      rw [hτ_eq_one, h_tau_scale_eq,
        TrustRegionSubproblem.cauchyPointScale_eq_min_of_pos_curvature Q h_curv_pos,
        min_eq_right (le_of_lt hρ_gt_one)]

/-- Chapter06 Exercise 6.9 (4): when `g_k ≠ 0`, the generalized Cauchy-point parameter `τ_k` is
given by the
piecewise formula
`τ_k = 1` if `g_kᵀ (Dᵀ D)⁻¹ B_k (Dᵀ D)⁻¹ g_k ≤ 0`, and otherwise
`τ_k = min (‖D⁻ᵀ g_k‖₂^3 / (Δ_k (g_kᵀ (Dᵀ D)⁻¹ B_k (Dᵀ D)⁻¹ g_k))) 1`.
Under symmetry of `D`, this is the source formula (6.3.68). -/
theorem generalizedCauchyScale_eq_piecewise
    {τk : ℝ} (h_gradient : P.gradient ≠ 0) (h_tau : P.IsGeneralizedCauchyScale τk) :
    τk =
      if P.generalizedGradientCurvature ≤ 0 then 1
      else
        min
          ((‖P.inverseTransposeScaledGradient‖ ^ (3 : ℕ)) /
            (P.radius * P.generalizedGradientCurvature))
          1 := by
  -- Route correction: once the scalar uniqueness lemma is isolated, the final statement is just
  -- the definitional expansion of the stored explicit weighted scale.
  simpa [GeneralizedTrustRegionSubproblem.generalizedCauchyScale] using
    P.eq_generalizedCauchyScale_of_isGeneralizedCauchyScale h_gradient h_tau

end

end GeneralizedTrustRegionSubproblem

end
