/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Theorem_6_1_2

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced `Matrix.PosSemidef` as the canonical mathlib API
-- for the shifted Hessian condition, and the local Chapter 6 precedent keeps the trust-region
-- owner explicit on `EuclideanSpace ℝ (Fin n)` rather than importing sibling generated files.

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- A generalized trust-region subproblem on `ℝ^n` consists of the model value `f`, the
gradient `g`, a symmetric Hessian approximation `B`, an explicit invertible scaling matrix `D`,
and a positive trust-region radius `Δ`. -/
structure GeneralizedTrustRegionSubproblem (n : ℕ) where
  fAtCenter : ℝ
  gradient : EuclideanSpace ℝ (Fin n)
  hessianApprox : Matrix (Fin n) (Fin n) ℝ
  hessianApprox_symm : hessianApprox.IsSymm
  scalingMatrix : Matrix (Fin n) (Fin n) ℝ
  scalingMatrixInv : Matrix (Fin n) (Fin n) ℝ
  scalingMatrix_mul_inv : scalingMatrix * scalingMatrixInv = 1
  scalingMatrixInv_mul : scalingMatrixInv * scalingMatrix = 1
  radius : ℝ
  radius_pos : 0 < radius

/-- The quadratic model attached to the generalized trust-region subproblem is
`f + gᵀ s + (1 / 2) sᵀ B s`. -/
def GeneralizedTrustRegionSubproblem.quadraticModel
    (P : GeneralizedTrustRegionSubproblem n) (s : Point) : ℝ :=
  P.fAtCenter + dotProduct P.gradient s +
    (1 / 2 : ℝ) * dotProduct s (P.hessianApprox.mulVec s)

/-- A generalized trust-region subproblem coerces to its quadratic model. -/
instance : CoeFun (GeneralizedTrustRegionSubproblem n) (fun _ ↦ Point → ℝ) where
  coe P := P.quadraticModel

/-- Evaluating a generalized trust-region subproblem as a function agrees with its quadratic
model. -/
theorem GeneralizedTrustRegionSubproblem.coeFn_apply
    (P : GeneralizedTrustRegionSubproblem n) (s : Point) :
    P s = P.quadraticModel s :=
  rfl

/-- Expanding the quadratic model gives the source formula
`f + gᵀ s + (1 / 2) sᵀ B s`. -/
theorem GeneralizedTrustRegionSubproblem.quadraticModel_eq
    (P : GeneralizedTrustRegionSubproblem n) (s : Point) :
    P.quadraticModel s =
      P.fAtCenter + dotProduct P.gradient s +
        (1 / 2 : ℝ) * dotProduct s (P.hessianApprox.mulVec s) :=
  rfl

/-- The weighted norm in the constraint is `‖D s‖₂`. -/
def GeneralizedTrustRegionSubproblem.weightedNorm
    (P : GeneralizedTrustRegionSubproblem n) (s : Point) : ℝ :=
  ‖Matrix.toEuclideanLin P.scalingMatrix s‖

/-- Expanding `weightedNorm` gives the source quantity `‖D s‖₂`. -/
theorem GeneralizedTrustRegionSubproblem.weightedNorm_eq
    (P : GeneralizedTrustRegionSubproblem n) (s : Point) :
    P.weightedNorm s = ‖Matrix.toEuclideanLin P.scalingMatrix s‖ :=
  rfl

/-- The feasible set of the generalized trust-region subproblem is the ellipsoid
`‖D s‖₂ ≤ Δ`. -/
def GeneralizedTrustRegionSubproblem.feasibleSet
    (P : GeneralizedTrustRegionSubproblem n) : Set Point :=
  { s | P.weightedNorm s ≤ P.radius }

/-- Membership in the feasible set is exactly the weighted trust-region constraint. -/
theorem GeneralizedTrustRegionSubproblem.mem_feasibleSet_iff
    (P : GeneralizedTrustRegionSubproblem n) (s : Point) :
    s ∈ P.feasibleSet ↔ P.weightedNorm s ≤ P.radius :=
  Iff.rfl

/-- A step solves the generalized trust-region subproblem when it is feasible and minimizes the
quadratic model on the feasible set. -/
def GeneralizedTrustRegionSubproblem.IsSolution
    (P : GeneralizedTrustRegionSubproblem n) (sStar : Point) : Prop :=
  sStar ∈ P.feasibleSet ∧ IsMinOn P P.feasibleSet sStar

/-- Unfolding `P.IsSolution sStar` gives feasibility together with the canonical minimizer
predicate `IsMinOn` on the weighted trust region. -/
theorem GeneralizedTrustRegionSubproblem.isSolution_iff_mem_feasibleSet_and_isMinOn
    (P : GeneralizedTrustRegionSubproblem n) (sStar : Point) :
    P.IsSolution sStar ↔ sStar ∈ P.feasibleSet ∧ IsMinOn P P.feasibleSet sStar :=
  Iff.rfl

/-- Expanding `IsSolution` gives feasibility together with global minimality of the quadratic
model on the weighted trust region. -/
theorem GeneralizedTrustRegionSubproblem.isSolution_iff
    (P : GeneralizedTrustRegionSubproblem n) (sStar : Point) :
    P.IsSolution sStar ↔
      sStar ∈ P.feasibleSet ∧
        ∀ s : Point, s ∈ P.feasibleSet → P.quadraticModel sStar ≤ P.quadraticModel s := by
  rw [isSolution_iff_mem_feasibleSet_and_isMinOn, isMinOn_iff]

/-- The shifted Hessian in the generalized KKT condition is `B + λ Dᵀ D`. -/
def GeneralizedTrustRegionSubproblem.shiftedHessian
    (P : GeneralizedTrustRegionSubproblem n) (lambdaStar : ℝ) : MatrixN :=
  P.hessianApprox + lambdaStar • (P.scalingMatrix.transpose * P.scalingMatrix)

/-- An optimality multiplier for `sStar` satisfies the weighted trust-region KKT conditions for
the generalized trust-region subproblem `P`. -/
structure GeneralizedTrustRegionSubproblem.IsOptimalityMultiplier
    (P : GeneralizedTrustRegionSubproblem n) (sStar : Point) (lambdaStar : ℝ) : Prop where
  nonneg : 0 ≤ lambdaStar
  stationarity : (P.shiftedHessian lambdaStar).mulVec sStar = -P.gradient
  feasible : P.weightedNorm sStar ≤ P.radius
  complementarity : lambdaStar * (P.radius - P.weightedNorm sStar) = 0
  posSemidef : (P.shiftedHessian lambdaStar).PosSemidef

/-- Expanding `P.IsOptimalityMultiplier sStar λ` gives the weighted trust-region KKT clauses. -/
theorem GeneralizedTrustRegionSubproblem.isOptimalityMultiplier_iff
    (P : GeneralizedTrustRegionSubproblem n) (sStar : Point) (lambdaStar : ℝ) :
    P.IsOptimalityMultiplier sStar lambdaStar ↔
      0 ≤ lambdaStar ∧
      (P.shiftedHessian lambdaStar).mulVec sStar = -P.gradient ∧
      P.weightedNorm sStar ≤ P.radius ∧
      lambdaStar * (P.radius - P.weightedNorm sStar) = 0 ∧
      (P.shiftedHessian lambdaStar).PosSemidef := by
  constructor
  · intro hMultiplier
    exact ⟨hMultiplier.nonneg, hMultiplier.stationarity, hMultiplier.feasible,
      hMultiplier.complementarity, hMultiplier.posSemidef⟩
  · rintro ⟨hNonneg, hStationarity, hFeasible, hComplementarity, hPosSemidef⟩
    exact
      { nonneg := hNonneg
        stationarity := hStationarity
        feasible := hFeasible
        complementarity := hComplementarity
        posSemidef := hPosSemidef }

/-- Helper for Chapter06 Exercise 6.10: the scaling matrix `D` is invertible in the matrix ring
because the problem data stores an explicit two-sided inverse. -/
theorem GeneralizedTrustRegionSubproblem.scalingMatrix_isUnit
    (P : GeneralizedTrustRegionSubproblem n) : IsUnit P.scalingMatrix := by
  -- Repackage the stored inverse data as the ring-theoretic `IsUnit` certificate.
  rw [isUnit_iff_exists_inv]
  exact ⟨P.scalingMatrixInv, P.scalingMatrix_mul_inv⟩

/-- Helper for Chapter06 Exercise 6.10: the stored inverse matrix `D⁻¹` is itself invertible. -/
theorem GeneralizedTrustRegionSubproblem.scalingMatrixInv_isUnit
    (P : GeneralizedTrustRegionSubproblem n) : IsUnit P.scalingMatrixInv := by
  -- Swap the two-sided inverse identities to certify that `D⁻¹` is also a unit.
  rw [isUnit_iff_exists_inv]
  exact ⟨P.scalingMatrix, P.scalingMatrixInv_mul⟩

/-- Helper for Chapter06 Exercise 6.10: applying `D` after `D⁻¹` recovers the original
standardized vector. -/
theorem GeneralizedTrustRegionSubproblem.scalingMatrix_mulVec_scalingMatrixInv_mulVec
    (P : GeneralizedTrustRegionSubproblem n) (y : Point) :
    P.scalingMatrix.mulVec (P.scalingMatrixInv.mulVec y) = y := by
  -- Push the two matrix actions together and use the stored inverse identity.
  simpa [Matrix.mulVec_mulVec, P.scalingMatrix_mul_inv, Matrix.one_mulVec] using
    (Matrix.mulVec_mulVec y P.scalingMatrix P.scalingMatrixInv)

/-- Helper for Chapter06 Exercise 6.10: applying `D⁻¹` after `D` recovers the original
weighted-space step. -/
theorem GeneralizedTrustRegionSubproblem.scalingMatrixInv_mulVec_scalingMatrix_mulVec
    (P : GeneralizedTrustRegionSubproblem n) (s : Point) :
    P.scalingMatrixInv.mulVec (P.scalingMatrix.mulVec s) = s := by
  -- Push the two matrix actions together and use the inverse-on-the-left identity.
  simpa [Matrix.mulVec_mulVec, P.scalingMatrixInv_mul, Matrix.one_mulVec] using
    (Matrix.mulVec_mulVec s P.scalingMatrixInv P.scalingMatrix)

/-- Helper for Chapter06 Exercise 6.10: `standardizeStep s` is the Euclidean-space image of the
raw variable change `y = D s`. -/
def GeneralizedTrustRegionSubproblem.standardizeStep
    (P : GeneralizedTrustRegionSubproblem n) (s : Point) : Point :=
  Matrix.toEuclideanLin P.scalingMatrix s

/-- Helper for Chapter06 Exercise 6.10: `destandardizeStep y` is the Euclidean-space image of the
inverse change of variables `s = D⁻¹ y`. -/
def GeneralizedTrustRegionSubproblem.destandardizeStep
    (P : GeneralizedTrustRegionSubproblem n) (y : Point) : Point :=
  Matrix.toEuclideanLin P.scalingMatrixInv y

/-- Helper for Chapter06 Exercise 6.10: standardization really applies `D` to the raw
coordinates. -/
theorem GeneralizedTrustRegionSubproblem.standardizeStep_ofLp
    (P : GeneralizedTrustRegionSubproblem n) (s : Point) :
    (P.standardizeStep s).ofLp = P.scalingMatrix.mulVec s.ofLp :=
  Matrix.ofLp_toEuclideanLin_apply P.scalingMatrix s

/-- Helper for Chapter06 Exercise 6.10: destandardization really applies `D⁻¹` to the raw
coordinates. -/
theorem GeneralizedTrustRegionSubproblem.destandardizeStep_ofLp
    (P : GeneralizedTrustRegionSubproblem n) (y : Point) :
    (P.destandardizeStep y).ofLp = P.scalingMatrixInv.mulVec y.ofLp :=
  Matrix.ofLp_toEuclideanLin_apply P.scalingMatrixInv y

/-- Helper for Chapter06 Exercise 6.10: the Euclidean norm of the standardized point is exactly
the weighted norm of the original step. -/
theorem GeneralizedTrustRegionSubproblem.norm_standardizeStep_eq_weightedNorm
    (P : GeneralizedTrustRegionSubproblem n) (s : Point) :
    ‖P.standardizeStep s‖ = P.weightedNorm s := by
  -- The standardized point is exactly the Euclidean image `D s`, so both norms are identical.
  rfl

/-- Helper for Chapter06 Exercise 6.10: destandardizing a point preserves the standardized
Euclidean norm when measured back in the weighted metric. -/
theorem GeneralizedTrustRegionSubproblem.weightedNorm_destandardizeStep_eq
    (P : GeneralizedTrustRegionSubproblem n) (y : Point) :
    P.weightedNorm (P.destandardizeStep y) = ‖y‖ := by
  -- Evaluate `D (D⁻¹ y)` once on raw coordinates and collapse it to the identity.
  simpa [GeneralizedTrustRegionSubproblem.weightedNorm,
    GeneralizedTrustRegionSubproblem.destandardizeStep, Matrix.toEuclideanLin_apply,
    Matrix.mulVec_mulVec, P.scalingMatrix_mul_inv]

/-- Helper for Chapter06 Exercise 6.10: standardizing after destandardizing returns the original
standardized point. -/
theorem GeneralizedTrustRegionSubproblem.standardizeStep_destandardizeStep
    (P : GeneralizedTrustRegionSubproblem n) (y : Point) :
    P.standardizeStep (P.destandardizeStep y) = y := by
  -- Compare raw coordinates and collapse the identity `D D⁻¹ = I`.
  apply WithLp.ofLp_injective
  simp [GeneralizedTrustRegionSubproblem.standardizeStep,
    GeneralizedTrustRegionSubproblem.destandardizeStep,
    Matrix.mulVec_mulVec, P.scalingMatrix_mul_inv]

/-- Helper for Chapter06 Exercise 6.10: destandardizing after standardizing returns the original
weighted-space step. -/
theorem GeneralizedTrustRegionSubproblem.destandardizeStep_standardizeStep
    (P : GeneralizedTrustRegionSubproblem n) (s : Point) :
    P.destandardizeStep (P.standardizeStep s) = s := by
  -- Compare raw coordinates and collapse the identity `D⁻¹ D = I`.
  apply WithLp.ofLp_injective
  simp [GeneralizedTrustRegionSubproblem.standardizeStep,
    GeneralizedTrustRegionSubproblem.destandardizeStep,
    Matrix.mulVec_mulVec, P.scalingMatrixInv_mul]

/-- Helper for Chapter06 Exercise 6.10: conjugating the symmetric Hessian approximation by the
inverse scaling matrix preserves symmetry. -/
theorem GeneralizedTrustRegionSubproblem.standardized_hessian_isSymm
    (P : GeneralizedTrustRegionSubproblem n) :
    (P.scalingMatrixInv.transpose * P.hessianApprox * P.scalingMatrixInv).IsSymm := by
  -- The transpose reverses the conjugation, and `B` is already symmetric.
  simpa [Matrix.IsSymm, Matrix.transpose_mul, Matrix.mul_assoc, P.hessianApprox_symm.eq]

/-- Helper for Chapter06 Exercise 6.10: the weighted trust-region problem becomes an ordinary
ball-constrained trust-region problem after the change of variables `y = D s`. -/
def GeneralizedTrustRegionSubproblem.toTrustRegionSubproblem
    (P : GeneralizedTrustRegionSubproblem n) : TrustRegionSubproblem n :=
  { fAtCenter := P.fAtCenter
    gradient := WithLp.toLp 2 (P.scalingMatrixInv.transpose.mulVec P.gradient.ofLp)
    hessianApprox := P.scalingMatrixInv.transpose * P.hessianApprox * P.scalingMatrixInv
    hessianApprox_symm := P.standardized_hessian_isSymm
    radius := P.radius
    radius_pos := P.radius_pos }

/-- Helper for Chapter06 Exercise 6.10: the quadratic model is unchanged by the bijective
substitution `y = D s`. -/
theorem GeneralizedTrustRegionSubproblem.quadraticModel_eq_standardized_quadraticModel
    (P : GeneralizedTrustRegionSubproblem n) (s : Point) :
    P.quadraticModel s =
      P.toTrustRegionSubproblem.quadraticModel (P.standardizeStep s) := by
  -- Rewrite the standardized model in raw coordinates and simplify the two conjugated terms.
  rw [GeneralizedTrustRegionSubproblem.quadraticModel_eq, TrustRegionSubproblem.quadraticModel_eq]
  have hLinear :
      dotProduct P.toTrustRegionSubproblem.gradient (P.standardizeStep s) =
        dotProduct P.gradient s := by
    -- Route correction: compare the two linear terms after swapping the dot-product order once,
    -- then collapse `D⁻¹ (D s) = s`.
    calc
      dotProduct P.toTrustRegionSubproblem.gradient (P.standardizeStep s)
        = dotProduct (P.scalingMatrix.mulVec s.ofLp)
            (P.scalingMatrixInv.transpose.mulVec P.gradient.ofLp) := by
            simp [GeneralizedTrustRegionSubproblem.toTrustRegionSubproblem,
              GeneralizedTrustRegionSubproblem.standardizeStep, Matrix.toEuclideanLin_apply,
              dotProduct_comm]
      _ = dotProduct P.gradient.ofLp
            (P.scalingMatrixInv.mulVec (P.scalingMatrix.mulVec s.ofLp)) := by
            simpa using
              (Matrix.dotProduct_transpose_mulVec (A := P.scalingMatrixInv)
                (x := P.scalingMatrix.mulVec s.ofLp) (y := P.gradient.ofLp))
      _ = dotProduct P.gradient.ofLp s.ofLp := by
            simp [Matrix.mulVec_mulVec, P.scalingMatrixInv_mul]
      _ = dotProduct P.gradient s := by
            rfl
  have hQuadratic :
      dotProduct (P.standardizeStep s)
          (P.toTrustRegionSubproblem.hessianApprox.mulVec (P.standardizeStep s)) =
        dotProduct s (P.hessianApprox.mulVec s) := by
    -- Evaluate the conjugated Hessian once and again use `D⁻¹ (D s) = s`.
    calc
      dotProduct (P.standardizeStep s)
          (P.toTrustRegionSubproblem.hessianApprox.mulVec (P.standardizeStep s))
        = dotProduct (P.scalingMatrix.mulVec s.ofLp)
            ((P.scalingMatrixInv.transpose * P.hessianApprox * P.scalingMatrixInv).mulVec
              (P.scalingMatrix.mulVec s.ofLp)) := by
            simp [GeneralizedTrustRegionSubproblem.toTrustRegionSubproblem,
              GeneralizedTrustRegionSubproblem.standardizeStep, Matrix.toEuclideanLin_apply]
      _ = dotProduct (P.scalingMatrix.mulVec s.ofLp)
            (P.scalingMatrixInv.transpose.mulVec (P.hessianApprox.mulVec s.ofLp)) := by
            simp [Matrix.mulVec_mulVec, Matrix.mul_assoc, P.scalingMatrixInv_mul]
      _ = dotProduct (P.hessianApprox.mulVec s.ofLp)
            (P.scalingMatrixInv.mulVec (P.scalingMatrix.mulVec s.ofLp)) := by
            simpa using
              (Matrix.dotProduct_transpose_mulVec (A := P.scalingMatrixInv)
                (x := P.scalingMatrix.mulVec s.ofLp)
                (y := P.hessianApprox.mulVec s.ofLp))
      _ = dotProduct (P.hessianApprox.mulVec s.ofLp) s.ofLp := by
            simp [Matrix.mulVec_mulVec, P.scalingMatrixInv_mul]
      _ = dotProduct s (P.hessianApprox.mulVec s) := by
            rw [dotProduct_comm]
  -- The remaining constants match after rewriting the transported linear and quadratic terms.
  rw [hLinear, hQuadratic]
  simp [GeneralizedTrustRegionSubproblem.toTrustRegionSubproblem]

/-- Helper for Chapter06 Exercise 6.10: the weighted feasible set becomes the ordinary
trust-region ball after applying `D`. -/
theorem GeneralizedTrustRegionSubproblem.mem_feasibleSet_iff_standardized_mem_feasibleSet
    (P : GeneralizedTrustRegionSubproblem n) (s : Point) :
    s ∈ P.feasibleSet ↔ P.standardizeStep s ∈ P.toTrustRegionSubproblem.feasibleSet := by
  -- After standardization, the ball constraint is exactly the same scalar inequality.
  simp [GeneralizedTrustRegionSubproblem.mem_feasibleSet_iff,
    TrustRegionSubproblem.mem_feasibleSet_iff,
    GeneralizedTrustRegionSubproblem.norm_standardizeStep_eq_weightedNorm,
    GeneralizedTrustRegionSubproblem.toTrustRegionSubproblem]

/-- Helper for Chapter06 Exercise 6.10: pulling a standardized feasible point back by `D⁻¹`
recovers a feasible point of the weighted problem. -/
theorem GeneralizedTrustRegionSubproblem.destandardizeStep_mem_feasibleSet_iff
    (P : GeneralizedTrustRegionSubproblem n) (y : Point) :
    P.destandardizeStep y ∈ P.feasibleSet ↔ y ∈ P.toTrustRegionSubproblem.feasibleSet := by
  -- Pulling back a standardized point replaces `‖D (D⁻¹ y)‖` by `‖y‖`.
  simp [GeneralizedTrustRegionSubproblem.mem_feasibleSet_iff,
    TrustRegionSubproblem.mem_feasibleSet_iff,
    GeneralizedTrustRegionSubproblem.weightedNorm_destandardizeStep_eq,
    GeneralizedTrustRegionSubproblem.toTrustRegionSubproblem]

/-- Helper for Chapter06 Exercise 6.10: solving the weighted problem at `sStar` is equivalent to
solving the standardized ordinary trust-region problem at `yStar = D sStar`. -/
theorem GeneralizedTrustRegionSubproblem.isSolution_iff_standardized_isSolution
    (P : GeneralizedTrustRegionSubproblem n) (sStar : Point) :
    P.IsSolution sStar ↔
      P.toTrustRegionSubproblem.IsSolution (P.standardizeStep sStar) := by
  -- Rewrite both owners through `IsMinOn`, then transport comparison points by `D` and `D⁻¹`.
  rw [GeneralizedTrustRegionSubproblem.isSolution_iff_mem_feasibleSet_and_isMinOn,
    TrustRegionSubproblem.isSolution_iff_mem_feasibleSet_and_isMinOn,
    GeneralizedTrustRegionSubproblem.mem_feasibleSet_iff_standardized_mem_feasibleSet,
    isMinOn_iff, isMinOn_iff]
  constructor
  · rintro ⟨hsStar, hmin⟩
    refine ⟨hsStar, ?_⟩
    intro y hy
    -- Pull the standardized comparison point back to the weighted problem.
    simpa [GeneralizedTrustRegionSubproblem.quadraticModel_eq_standardized_quadraticModel,
      P.standardizeStep_destandardizeStep y] using
      hmin (P.destandardizeStep y) ((P.destandardizeStep_mem_feasibleSet_iff y).2 hy)
  · rintro ⟨hsStar, hmin⟩
    refine ⟨hsStar, ?_⟩
    intro s hs
    -- Push the weighted comparison point forward to the standardized problem.
    simpa [GeneralizedTrustRegionSubproblem.quadraticModel_eq_standardized_quadraticModel] using
      hmin (P.standardizeStep s) ((P.mem_feasibleSet_iff_standardized_mem_feasibleSet s).1 hs)

/-- Helper for Chapter06 Exercise 6.10: the standardized shifted Hessian is the conjugate of the
weighted shifted Hessian by `D⁻¹`. -/
theorem GeneralizedTrustRegionSubproblem.standardized_shiftedHessian_eq_conjugate
    (P : GeneralizedTrustRegionSubproblem n) (lambdaStar : ℝ) :
    P.toTrustRegionSubproblem.shiftedHessian lambdaStar =
      P.scalingMatrixInv.transpose * (P.shiftedHessian lambdaStar) * P.scalingMatrixInv := by
  -- Expand both shifted Hessians and simplify the conjugated metric term to the identity.
  have hInvTransposeMul :
      P.scalingMatrixInv.transpose * P.scalingMatrix.transpose = 1 := by
    simpa using congrArg Matrix.transpose P.scalingMatrix_mul_inv
  have hTransposeInvMul :
      P.scalingMatrix.transpose * P.scalingMatrixInv.transpose = 1 := by
    simpa using congrArg Matrix.transpose P.scalingMatrixInv_mul
  have hMetric :
      P.scalingMatrixInv.transpose *
          (P.scalingMatrix.transpose * P.scalingMatrix) *
          P.scalingMatrixInv =
        1 := by
    -- The weighted metric term collapses to the identity after conjugation by `D⁻¹`.
    calc
      P.scalingMatrixInv.transpose *
          (P.scalingMatrix.transpose * P.scalingMatrix) *
          P.scalingMatrixInv
        = (P.scalingMatrixInv.transpose * P.scalingMatrix.transpose) *
            (P.scalingMatrix * P.scalingMatrixInv) := by
            simp [Matrix.mul_assoc]
      _ = (1 : MatrixN) * 1 := by
            rw [hInvTransposeMul, P.scalingMatrix_mul_inv]
      _ = 1 := by
            simp
  ext i j
  simp [TrustRegionSubproblem.shiftedHessian, GeneralizedTrustRegionSubproblem.shiftedHessian,
    GeneralizedTrustRegionSubproblem.toTrustRegionSubproblem, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc, hMetric]

/-- Helper for Chapter06 Exercise 6.10: applying the standardized shifted Hessian to `D s`
matches applying `D⁻ᵀ` to the weighted shifted Hessian action on `s`. -/
theorem GeneralizedTrustRegionSubproblem.standardized_shiftedHessian_mul_standardizeStep
    (P : GeneralizedTrustRegionSubproblem n) (lambdaStar : ℝ) (s : Point) :
    (P.toTrustRegionSubproblem.shiftedHessian lambdaStar).mulVec (P.standardizeStep s).ofLp =
      P.scalingMatrixInv.transpose.mulVec ((P.shiftedHessian lambdaStar).mulVec s.ofLp) := by
  -- Evaluate the conjugated shifted Hessian on `D s` and simplify `D⁻¹ (D s) = s`.
  rw [P.standardized_shiftedHessian_eq_conjugate]
  simp [GeneralizedTrustRegionSubproblem.standardizeStep_ofLp,
    Matrix.mulVec_mulVec, Matrix.mul_assoc, P.scalingMatrixInv_mul]

/-- Helper for Chapter06 Exercise 6.10: positive semidefiniteness of the shifted Hessian is
invariant under the invertible conjugation that standardizes the trust region. -/
theorem GeneralizedTrustRegionSubproblem.standardized_shiftedHessian_posSemidef_iff
    (P : GeneralizedTrustRegionSubproblem n) (lambdaStar : ℝ) :
    (P.toTrustRegionSubproblem.shiftedHessian lambdaStar).PosSemidef ↔
      (P.shiftedHessian lambdaStar).PosSemidef := by
  -- Positive semidefiniteness is invariant under invertible real transpose-conjugation.
  rw [P.standardized_shiftedHessian_eq_conjugate]
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.IsUnit.posSemidef_star_left_conjugate_iff
      (x := P.shiftedHessian lambdaStar) (U := P.scalingMatrixInv)
      (P.scalingMatrixInv_isUnit))

/-- Chapter06 Exercise 6.10: a step `sStar` solves the generalized trust-region subproblem
`min f + gᵀ s + (1 / 2) sᵀ B s` subject to `‖D s‖₂ ≤ Δ` if and only if there is an
multiplier `λStar` satisfying the weighted trust-region KKT conditions. -/
theorem GeneralizedTrustRegionSubproblem.isSolution_iff_exists_multiplier
    (P : GeneralizedTrustRegionSubproblem n) (sStar : Point) :
    P.IsSolution sStar ↔
      ∃ lambdaStar : ℝ,
        0 ≤ lambdaStar ∧
        (P.shiftedHessian lambdaStar).mulVec sStar = -P.gradient ∧
        P.weightedNorm sStar ≤ P.radius ∧
        lambdaStar * (P.radius - P.weightedNorm sStar) = 0 ∧
        (P.shiftedHessian lambdaStar).PosSemidef := by
  -- Transport the problem to the standardized trust region, apply Theorem 6.1.2 there, and
  -- then rewrite each KKT clause back through the change of variables `y = D s`.
  rw [P.isSolution_iff_standardized_isSolution,
    TrustRegionSubproblem.isSolution_iff_exists_multiplier]
  constructor
  · rintro ⟨lambdaStar, hNonneg, hStationarity, hFeasible, hComplementarity, hPosSemidef⟩
    have hTransposeInvMul :
        P.scalingMatrix.transpose * P.scalingMatrixInv.transpose = 1 := by
      simpa using congrArg Matrix.transpose P.scalingMatrixInv_mul
    have hScaledStationarity :
        P.scalingMatrixInv.transpose.mulVec ((P.shiftedHessian lambdaStar).mulVec sStar.ofLp) =
          -P.scalingMatrixInv.transpose.mulVec P.gradient.ofLp := by
      calc
        P.scalingMatrixInv.transpose.mulVec ((P.shiftedHessian lambdaStar).mulVec sStar.ofLp)
          = (P.toTrustRegionSubproblem.shiftedHessian lambdaStar).mulVec
              (P.standardizeStep sStar).ofLp := by
              symm
              exact P.standardized_shiftedHessian_mul_standardizeStep lambdaStar sStar
        _ = (-P.toTrustRegionSubproblem.gradient).ofLp := by
              simpa using hStationarity
        _ = -P.scalingMatrixInv.transpose.mulVec P.gradient.ofLp := by
              simp [GeneralizedTrustRegionSubproblem.toTrustRegionSubproblem]
    have hRawStationarity :
        (P.shiftedHessian lambdaStar).mulVec sStar.ofLp = -P.gradient.ofLp := by
      have hApplyTranspose :=
        congrArg (fun v : Fin n → ℝ ↦ P.scalingMatrix.transpose.mulVec v) hScaledStationarity
      have hConjugated :
          P.scalingMatrix.transpose *
              (P.scalingMatrixInv.transpose * P.shiftedHessian lambdaStar) =
            P.shiftedHessian lambdaStar := by
        calc
          P.scalingMatrix.transpose *
              (P.scalingMatrixInv.transpose * P.shiftedHessian lambdaStar)
            = (P.scalingMatrix.transpose * P.scalingMatrixInv.transpose) *
                P.shiftedHessian lambdaStar := by
                simp [Matrix.mul_assoc]
          _ = (1 : MatrixN) * P.shiftedHessian lambdaStar := by
                rw [hTransposeInvMul]
          _ = P.shiftedHessian lambdaStar := by
                simp
      simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc, hConjugated, hTransposeInvMul,
        Matrix.mulVec_neg] using hApplyTranspose
    refine ⟨lambdaStar, hNonneg, ?_, ?_, ?_,
      (P.standardized_shiftedHessian_posSemidef_iff lambdaStar).mp hPosSemidef⟩
    · simpa using hRawStationarity
    · simpa [P.norm_standardizeStep_eq_weightedNorm,
        GeneralizedTrustRegionSubproblem.toTrustRegionSubproblem] using hFeasible
    · simpa [P.norm_standardizeStep_eq_weightedNorm,
        GeneralizedTrustRegionSubproblem.toTrustRegionSubproblem] using hComplementarity
  · rintro ⟨lambdaStar, hNonneg, hStationarity, hFeasible, hComplementarity, hPosSemidef⟩
    refine ⟨lambdaStar, hNonneg, ?_, ?_, ?_,
      (P.standardized_shiftedHessian_posSemidef_iff lambdaStar).2 hPosSemidef⟩
    · calc
        (P.toTrustRegionSubproblem.shiftedHessian lambdaStar).mulVec (P.standardizeStep sStar).ofLp
          = P.scalingMatrixInv.transpose.mulVec ((P.shiftedHessian lambdaStar).mulVec sStar.ofLp) :=
              P.standardized_shiftedHessian_mul_standardizeStep lambdaStar sStar
        _ = P.scalingMatrixInv.transpose.mulVec (-P.gradient.ofLp) := by
              simpa using congrArg (fun v : Fin n → ℝ ↦ P.scalingMatrixInv.transpose.mulVec v)
                hStationarity
        _ = (-P.toTrustRegionSubproblem.gradient).ofLp := by
              simp [GeneralizedTrustRegionSubproblem.toTrustRegionSubproblem, Matrix.mulVec_neg]
    · simpa [P.norm_standardizeStep_eq_weightedNorm,
        GeneralizedTrustRegionSubproblem.toTrustRegionSubproblem] using hFeasible
    · simpa [P.norm_standardizeStep_eq_weightedNorm,
        GeneralizedTrustRegionSubproblem.toTrustRegionSubproblem] using hComplementarity

/-- The source KKT theorem can be repackaged through the bundled multiplier predicate
`P.IsOptimalityMultiplier sStar λ`. -/
theorem GeneralizedTrustRegionSubproblem.isSolution_iff_exists_optimalityMultiplier
    (P : GeneralizedTrustRegionSubproblem n) (sStar : Point) :
    P.IsSolution sStar ↔
      ∃ lambdaStar : ℝ, P.IsOptimalityMultiplier sStar lambdaStar := by
  rw [isSolution_iff_exists_multiplier]
  constructor
  · rintro ⟨lambdaStar, hNonneg, hStationarity, hFeasible, hComplementarity, hPosSemidef⟩
    exact
      ⟨lambdaStar,
        ⟨hNonneg, hStationarity, hFeasible, hComplementarity, hPosSemidef⟩⟩
  · rintro ⟨lambdaStar, hMultiplier⟩
    exact
      ⟨lambdaStar, hMultiplier.nonneg, hMultiplier.stationarity, hMultiplier.feasible,
        hMultiplier.complementarity, hMultiplier.posSemidef⟩

end
