/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_3_4

noncomputable section

open scoped Gradient

section Chapter08Exercise86

variable {n : ℕ}

local notation "Point" => Fin n → ℝ
local notation "ConstraintIndex" => Fin 1
local notation "Multiplier" => ConstraintIndex → ℝ
local notation "EPoint" => EuclideanSpace ℝ (Fin n)

-- Domain sampling:
-- * primary domain: second-order sufficiency for a concrete Chapter 8 constrained problem
-- * inspected owner declarations in this domain:
--   `ConstrainedOptimizationProblem.IsKKTPoint` from `Theorem_8_2_7`
--   `ConstrainedOptimizationProblem.linearizedNullConstraintDirections` from `Definition_8_3_2`
--   `ConstrainedOptimizationProblem.lagrangianHessianQuadratic` from `Theorem_8_3_3`
--   `ConstrainedOptimizationProblem
--      .isStrictLocalMinOn_of_positive_lagrangianHessian_on_linearizedNullConstraintDirections`
--   from `Theorem_8_3_4`
-- * semantic recall via `lean_leansearch`: no more specific mathlib/project owner surfaced than
--   the chapter KKT/SOSC API already used here
-- * owner abstraction chosen here: the chapter owner `ConstrainedOptimizationProblem`
-- * primitive data kept here: the exercise objective, the single inequality-constraint family,
--   the resulting constrained problem, and its explicit source-facing candidate data
-- * derived API deleted from the local file: the bespoke feasible-set and SOSC wrapper
--   definitions, now replaced by the canonical KKT/null-direction/Hessian owners
-- * transport note: the source uses the Euclidean norm on `ℝ^n`; on the chapter owner
--   `Point = Fin n → ℝ`, that norm is expressed via `WithLp.toLp 2`

/-- The linear objective `x ↦ dotProduct c x` from Exercise 8.6. -/
def exercise86Objective (c : Point) : Point → ℝ :=
  fun x ↦ dotProduct c x

/-- The unique inequality-constraint family for the Euclidean unit ball from Exercise 8.6,
expressed on the chapter owner `Point = Fin n → ℝ` via `WithLp.toLp 2`. -/
def exercise86Constraint (_ : ConstraintIndex) : Point → ℝ :=
  fun x ↦ 1 - ‖WithLp.toLp 2 x‖ ^ 2

/-- The ball-constrained optimization problem from Exercise 8.6. -/
def exercise86Problem (c : Point) :
    ConstrainedOptimizationProblem n 1
      (∅ : Set ConstraintIndex) (Set.univ : Set ConstraintIndex) where
  objective := exercise86Objective c
  constraint := exercise86Constraint
  eqIndices_union_ineqIndices := by
    ext i
    simp
  eqIndices_disjoint_ineqIndices := by
    simp

/-- The minimization-consistent boundary point `-c / ‖c‖₂` for Exercise 8.6,
expressed on `Point = Fin n → ℝ` via `WithLp.toLp 2`. -/
def exercise86Candidate (c : Point) : Point :=
  (-(‖WithLp.toLp 2 c‖)⁻¹) • c

/-- Helper for Chapter08 Exercise 8.6: the Euclidean transport of the linear objective is the
inner product with `WithLp.toLp 2 c`. -/
lemma exercise86_euclideanObjective_eq (c : Point) :
    (exercise86Problem c).euclideanObjective = fun y : EPoint ↦ inner ℝ (WithLp.toLp 2 c) y := by
  -- Expand the transported objective and rewrite the dot product as the Euclidean inner product.
  ext y
  simp [exercise86Problem, exercise86Objective, dotProduct, PiLp.inner_apply, mul_comm]

/-- Helper for Chapter08 Exercise 8.6: the Euclidean transport of the constraint is
`y ↦ 1 - ‖y‖^2`. -/
lemma exercise86_euclideanConstraint_eq (c : Point) :
    (exercise86Problem c).euclideanConstraint 0 = fun y : EPoint ↦ 1 - ‖y‖ ^ (2 : ℕ) := by
  -- Converting from `Point` to Euclidean coordinates and back leaves the norm unchanged.
  ext y
  change 1 - ‖WithLp.toLp 2 y.ofLp‖ ^ (2 : ℕ) = 1 - ‖y‖ ^ (2 : ℕ)
  rw [WithLp.toLp_ofLp 2 y]

/-- Helper for Chapter08 Exercise 8.6: the explicit candidate lies on the unit sphere. -/
lemma exercise86Candidate_norm_eq_one (c : Point) (hc : c ≠ 0) :
    ‖WithLp.toLp 2 (exercise86Candidate c)‖ = 1 := by
  -- Rewrite the candidate norm as the product of the inverse scale and `‖c‖₂`.
  have hcEuclidean : WithLp.toLp 2 c ≠ 0 := by
    simpa using hc
  have hnorm_ne : ‖WithLp.toLp 2 c‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr hcEuclidean
  calc
    ‖WithLp.toLp 2 (exercise86Candidate c)‖
      = ‖(-(‖WithLp.toLp 2 c‖)⁻¹ : ℝ) • WithLp.toLp 2 c‖ := by
          simp [exercise86Candidate]
    _ = |(-(‖WithLp.toLp 2 c‖)⁻¹ : ℝ)| * ‖WithLp.toLp 2 c‖ := norm_smul _ _
    _ = ‖WithLp.toLp 2 c‖⁻¹ * ‖WithLp.toLp 2 c‖ := by simp
    _ = 1 := inv_mul_cancel₀ hnorm_ne

/-- Helper for Chapter08 Exercise 8.6: the linear objective is differentiable at every point. -/
lemma exercise86_objective_differentiableAt (c x : Point) :
    DifferentiableAt ℝ (exercise86Problem c).objective x := by
  -- The Euclidean transport is a continuous linear functional, so the original objective is
  -- differentiable after transporting back.
  have hEuclidean :
      DifferentiableAt ℝ (exercise86Problem c).euclideanObjective (WithLp.toLp 2 x) := by
    rw [exercise86_euclideanObjective_eq]
    exact (((innerSL ℝ (WithLp.toLp 2 c)) : EPoint →L[ℝ] ℝ).differentiableAt)
  exact ((exercise86Problem c).differentiableAt_euclideanObjective_iff x).1 hEuclidean

/-- Helper for Chapter08 Exercise 8.6: the unique constraint is differentiable at every point. -/
lemma exercise86_constraint_differentiableAt (c x : Point) :
    (exercise86Problem c).HasConstraintGradientsAt x := by
  intro i
  fin_cases i
  -- After transporting to Euclidean coordinates, the constraint is `1 - ‖y‖^2`.
  have hEuclidean :
      DifferentiableAt ℝ ((exercise86Problem c).euclideanConstraint 0) (WithLp.toLp 2 x) := by
    rw [exercise86_euclideanConstraint_eq]
    exact
      ((show HasFDerivAt (fun y : EPoint ↦ y) (ContinuousLinearMap.id ℝ EPoint)
          (WithLp.toLp 2 x) from hasFDerivAt_id (WithLp.toLp 2 x)).norm_sq).differentiableAt.const_sub
        (1 : ℝ)
  exact ((exercise86Problem c).differentiableAt_euclideanConstraint_iff 0 x).1 hEuclidean

/-- Helper for Chapter08 Exercise 8.6: the Euclidean gradient of the linear objective is the
constant vector `WithLp.toLp 2 c`. -/
lemma exercise86_objective_gradient (c : Point) (p : EPoint) :
    gradient ((exercise86Problem c).euclideanObjective) p = WithLp.toLp 2 c := by
  -- Compare both sides by pairing with arbitrary test vectors in the Euclidean inner product.
  apply ext_inner_right ℝ
  intro z
  calc
    inner ℝ (gradient ((exercise86Problem c).euclideanObjective) p) z
      = fderiv ℝ ((exercise86Problem c).euclideanObjective) p z := by
          simpa using
            (inner_gradient_left (𝕜 := ℝ) (f := (exercise86Problem c).euclideanObjective)
              (x := p) (y := z))
    _ = fderiv ℝ (fun y : EPoint ↦ inner ℝ (WithLp.toLp 2 c) y) p z := by
          rw [exercise86_euclideanObjective_eq]
    _ = inner ℝ (WithLp.toLp 2 c) z := by
          simpa [innerSL_apply_apply] using
            congrArg (fun f : EPoint →L[ℝ] ℝ ↦ f z)
              ((((innerSL ℝ (WithLp.toLp 2 c)) : EPoint →L[ℝ] ℝ).hasFDerivAt.fderiv) :
                fderiv ℝ (fun y : EPoint ↦ inner ℝ (WithLp.toLp 2 c) y) p =
                  innerSL ℝ (WithLp.toLp 2 c))

/-- Helper for Chapter08 Exercise 8.6: the Euclidean gradient of the ball constraint is
`-2 • p`. -/
lemma exercise86_constraint_gradient (c : Point) (p : EPoint) :
    gradient ((exercise86Problem c).euclideanConstraint 0) p = (-2 : ℝ) • p := by
  -- Differentiate the explicit Euclidean constraint `1 - ‖p‖^2` and compare by inner products.
  apply ext_inner_right ℝ
  intro z
  calc
    inner ℝ (gradient ((exercise86Problem c).euclideanConstraint 0) p) z
      = fderiv ℝ ((exercise86Problem c).euclideanConstraint 0) p z := by
          simpa using
            (inner_gradient_left (𝕜 := ℝ) (f := (exercise86Problem c).euclideanConstraint 0)
              (x := p) (y := z))
    _ = fderiv ℝ (fun y : EPoint ↦ 1 - ‖y‖ ^ (2 : ℕ)) p z := by
          rw [exercise86_euclideanConstraint_eq]
    _ = inner ℝ ((-2 : ℝ) • p) z := by
          rw [fderiv_const_sub]
          have hNormSq :
              fderiv ℝ (fun y : EPoint ↦ ‖y‖ ^ (2 : ℕ)) p z = 2 * inner ℝ p z := by
            simpa [smul_apply, innerSL_apply_apply, two_smul, two_mul] using
              congrArg (fun f : EPoint →L[ℝ] ℝ ↦ f z) (fderiv_norm_sq_apply p)
          rw [show (-fderiv ℝ (fun y : EPoint ↦ ‖y‖ ^ (2 : ℕ)) p) z = -(2 * inner ℝ p z) by
            rw [neg_apply, hNormSq]]
          simp [inner_smul_left, two_mul]

/-- Helper for Chapter08 Exercise 8.6: the Euclidean gradient of the exercise Lagrangian is the
explicit affine field `c + 2 λ x`. -/
lemma exercise86_lagrangianGradient (c x : Point) (lam : ℝ) :
    gradient ((exercise86Problem c).euclideanLagrangian (fun _ ↦ lam)) (WithLp.toLp 2 x) =
      WithLp.toLp 2 c + (2 * lam) • WithLp.toLp 2 x := by
  -- Rewrite the generic Chapter 8 gradient formula using the explicit objective and constraint
  -- gradients for this one-constraint problem.
  have hObjective : DifferentiableAt ℝ (exercise86Problem c).objective x :=
    exercise86_objective_differentiableAt c x
  have hConstraints : (exercise86Problem c).HasConstraintGradientsAt x :=
    exercise86_constraint_differentiableAt c x
  rw [(exercise86Problem c).gradient_euclideanLagrangian_eq_objective_sub_sum x (fun _ ↦ lam)
    hObjective hConstraints]
  rw [exercise86_objective_gradient, Fin.sum_univ_one, exercise86_constraint_gradient]
  simp [sub_eq_add_neg, smul_smul, mul_comm]

/-- Helper for Chapter08 Exercise 8.6: the explicit multiplier `‖c‖₂ / 2` satisfies the KKT
conditions at `exercise86Candidate c`. -/
lemma exercise86Candidate_isKKTPoint (c : Point) (hc : c ≠ 0) :
    (exercise86Problem c).IsKKTPoint (exercise86Candidate c)
      (fun _ ↦ ‖WithLp.toLp 2 c‖ / 2) := by
  let lam0 : ℝ := ‖WithLp.toLp 2 c‖ / 2
  have hcEuclidean : WithLp.toLp 2 c ≠ 0 := by
    simpa using hc
  have hnorm_ne : ‖WithLp.toLp 2 c‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr hcEuclidean
  refine
    { feasible := ?_
      dualFeasible := ?_
      stationarity := ?_
      complementarySlackness := ?_ }
  · -- Feasibility reduces to checking the unique inequality constraint on the unit sphere.
    rw [(exercise86Problem c).mem_iff]
    constructor
    · intro i hi
      simp at hi
    · intro i hi
      fin_cases i
      simp [exercise86Problem, exercise86Constraint, exercise86Candidate_norm_eq_one, hc]
  · -- The unique multiplier is nonnegative because it is half a norm.
    intro i hi
    fin_cases i
    nlinarith [norm_nonneg (WithLp.toLp 2 c)]
  · -- The explicit affine gradient vanishes because `xStar = -(1 / ‖c‖₂) • c`.
    rw [exercise86_lagrangianGradient]
    change WithLp.toLp 2 c + (2 * lam0) • WithLp.toLp 2 (exercise86Candidate c) = 0
    have hScale : 2 * lam0 = ‖WithLp.toLp 2 c‖ := by
      dsimp [lam0]
      ring
    rw [hScale]
    have hCandidate :
        ‖WithLp.toLp 2 c‖ • WithLp.toLp 2 (exercise86Candidate c) =
          (-1 : ℝ) • WithLp.toLp 2 c := by
      simp [exercise86Candidate, smul_smul, hnorm_ne]
    rw [hCandidate]
    simp
  · -- Complementary slackness follows because the unique inequality constraint is active.
    intro i hi
    fin_cases i
    simp [exercise86Problem, exercise86Constraint, exercise86Candidate_norm_eq_one, hc]

/-- Helper for Chapter08 Exercise 8.6: the Lagrangian Hessian quadratic form is the positive
multiple `(2 * lam) * ‖d‖₂^2`. -/
lemma exercise86_lagrangianHessianQuadratic_eq (c x d : Point) (lam : ℝ) :
    (exercise86Problem c).lagrangianHessianQuadratic x (fun _ ↦ lam) d =
      (2 * lam) * ‖WithLp.toLp 2 d‖ ^ (2 : ℕ) := by
  -- Normalize the gradient field to an affine map, then differentiate that affine map directly.
  have hGradientField :
      gradient ((exercise86Problem c).euclideanLagrangian (fun _ ↦ lam)) =
        fun y : EPoint ↦ WithLp.toLp 2 c + (2 * lam) • y := by
    funext y
    simpa using exercise86_lagrangianGradient (c := c) (x := y.ofLp) (lam := lam)
  rw [(exercise86Problem c).lagrangianHessianQuadratic_eq x d (fun _ ↦ lam)]
  have hFDeriv :
      fderiv ℝ (gradient ((exercise86Problem c).euclideanLagrangian (fun _ ↦ lam)))
        (WithLp.toLp 2 x) = (2 * lam) • ContinuousLinearMap.id ℝ EPoint := by
    rw [hGradientField]
    simpa using
      ((((2 * lam) • (ContinuousLinearMap.id ℝ EPoint)) : EPoint →L[ℝ] EPoint).hasFDerivAt.const_add
        (WithLp.toLp 2 c)).fderiv
  rw [ConstrainedOptimizationProblem.lagrangianHessianAt, hFDeriv]
  calc
    inner ℝ (WithLp.toLp 2 d)
        (((2 * lam) • ContinuousLinearMap.id ℝ EPoint) (WithLp.toLp 2 d))
        = inner ℝ (WithLp.toLp 2 d) ((2 * lam) • WithLp.toLp 2 d) := by
            simp [smul_apply]
    _ = (2 * lam) * inner ℝ (WithLp.toLp 2 d) (WithLp.toLp 2 d) := by
            rw [inner_smul_right]
    _ = (2 * lam) * ‖WithLp.toLp 2 d‖ ^ (2 : ℕ) := by
            rw [real_inner_self_eq_norm_sq]
    _ = (2 * lam) * ‖WithLp.toLp 2 d‖ ^ (2 : ℕ) := by
            rfl

/-- Chapter08 Exercise 8.6: for the problem with objective `exercise86Objective c` and Euclidean
ball constraint `exercise86Constraint`, the minimization-consistent boundary point
`exercise86Candidate c = -c / ‖c‖₂` is stated on the chapter's canonical
second-order sufficient-condition surface using an existential multiplier. -/
theorem exercise86_candidate_satisfiesSecondOrderSufficientCondition
    (c : Point) (hc : c ≠ 0) :
    let problem := exercise86Problem c
    let xStar : Point := exercise86Candidate c
    ∃ lamStar : Multiplier,
      problem.IsKKTPoint xStar lamStar ∧
        ∀ d ∈ problem.linearizedNullConstraintDirections xStar lamStar,
          0 < problem.lagrangianHessianQuadratic xStar lamStar d := by
  -- Choose the textbook multiplier `‖c‖₂ / 2`, prove KKT directly, and use the explicit Hessian
  -- quadratic formula to get strict positivity on every nonzero null direction.
  dsimp
  refine ⟨fun _ ↦ ‖WithLp.toLp 2 c‖ / 2, exercise86Candidate_isKKTPoint c hc, ?_⟩
  intro d hd
  have hcEuclidean : WithLp.toLp 2 c ≠ 0 := by
    simpa using hc
  have hnormc_pos : 0 < ‖WithLp.toLp 2 c‖ := norm_pos_iff.mpr hcEuclidean
  have hd_nonzero : d ≠ 0 := by
    exact
      ((exercise86Problem c).mem_linearizedNullConstraintDirections_iff
        (exercise86Candidate c) (fun _ ↦ ‖WithLp.toLp 2 c‖ / 2) d).1 hd |>.2.1
  have hdEuclidean : WithLp.toLp 2 d ≠ 0 := by
    simpa using hd_nonzero
  have hnormd_pos : 0 < ‖WithLp.toLp 2 d‖ := norm_pos_iff.mpr hdEuclidean
  rw [exercise86_lagrangianHessianQuadratic_eq]
  have hsq_pos : 0 < ‖WithLp.toLp 2 d‖ ^ (2 : ℕ) := by
    exact pow_pos hnormd_pos _
  nlinarith

end Chapter08Exercise86
