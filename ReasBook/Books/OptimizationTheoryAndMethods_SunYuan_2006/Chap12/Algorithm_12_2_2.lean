/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_6_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Definition_12_2_extra_1

noncomputable section

/-- The ambient primal space `ℝ^n` used in the Wilson-Han-Powell method. -/
abbrev WilsonHanPowellPoint (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The multiplier space `ℝ^m` used in the Wilson-Han-Powell method. -/
abbrev WilsonHanPowellMultiplier (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- The Hessian-approximation matrices `B_k ∈ ℝ^(n × n)` used in the Wilson-Han-Powell method. -/
abbrev WilsonHanPowellHessianApproximation (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The constraint Jacobian `A_k ∈ ℝ^(n × m)` with constraint gradients as columns. -/
abbrev WilsonHanPowellConstraintJacobian (n m : ℕ) := Matrix (Fin n) (Fin m) ℝ

-- Semantic recall: `WilsonHanPowellSubproblem` is the Chapter 12 canonical owner for the SQP
-- Step-1 subproblem. Algorithm 12.2.2 specializes it to the equality-constrained case, so this
-- file keeps the source-facing stage formulas and exposes the chapter owner through a thin bridge.

/-- The Step-2 trial point obtained from the current iterate `x`, direction `d`, and trial
step size `α` is `x + α d`. -/
def wilsonHanPowellTrialPoint {n : ℕ}
    (x d : WilsonHanPowellPoint n) (α : ℝ) : WilsonHanPowellPoint n :=
  x + α • d

/-- Unfolding `wilsonHanPowellTrialPoint x d α` gives the source trial-point formula
`x + α d`. -/
theorem wilsonHanPowellTrialPoint_eq {n : ℕ}
    (x d : WilsonHanPowellPoint n) (α : ℝ) :
    wilsonHanPowellTrialPoint x d α = x + α • d := rfl

/-- The inexact line-search condition `(12.2.14)` written as an `ε`-optimality comparison
against every step length `β ∈ [0, δ]`. -/
def IsApproximatePenaltyStep {n : ℕ}
    (penaltyFunction : WilsonHanPowellPoint n → ℝ → ℝ)
    (x d : WilsonHanPowellPoint n) (σ δ α ε : ℝ) : Prop :=
  α ∈ Set.Icc (0 : ℝ) δ ∧
    ∀ β : ℝ, β ∈ Set.Icc (0 : ℝ) δ →
      penaltyFunction (wilsonHanPowellTrialPoint x d α) σ ≤
        penaltyFunction (wilsonHanPowellTrialPoint x d β) σ + ε

/-- Unfolding `IsApproximatePenaltyStep penaltyFunction x d σ δ α ε` gives the source Step-2
condition `(12.2.14)` in comparison form on `[0, δ]`. -/
theorem isApproximatePenaltyStep_iff {n : ℕ}
    (penaltyFunction : WilsonHanPowellPoint n → ℝ → ℝ)
    (x d : WilsonHanPowellPoint n) (σ δ α ε : ℝ) :
    IsApproximatePenaltyStep penaltyFunction x d σ δ α ε ↔
      α ∈ Set.Icc (0 : ℝ) δ ∧
        ∀ β : ℝ, β ∈ Set.Icc (0 : ℝ) δ →
          penaltyFunction (wilsonHanPowellTrialPoint x d α) σ ≤
            penaltyFunction (wilsonHanPowellTrialPoint x d β) σ + ε := Iff.rfl

/-- The `i`th constraint gradient column of a Jacobian matrix `A`. -/
def wilsonHanPowellConstraintGradient {n m : ℕ}
    (A : WilsonHanPowellConstraintJacobian n m) (i : Fin m) :
    WilsonHanPowellPoint n :=
  WithLp.toLp 2 fun j : Fin n ↦ A j i

/-- Evaluating `wilsonHanPowellConstraintGradient A i` at coordinate `j` returns the matrix
entry `A j i`. -/
theorem wilsonHanPowellConstraintGradient_apply {n m : ℕ}
    (A : WilsonHanPowellConstraintJacobian n m) (i : Fin m) (j : Fin n) :
    wilsonHanPowellConstraintGradient A i j = A j i := rfl

/-- The equality-constrained Wilson-Han-Powell data viewed as the Chapter 10
`StandardPenaltyProblem` owner with `eqCount = m`. -/
def wilsonHanPowellPenaltyProblem {n m : ℕ}
    (objectiveFunction : WilsonHanPowellPoint n → ℝ)
    (constraintFunction : WilsonHanPowellPoint n → WilsonHanPowellMultiplier m) :
    StandardPenaltyProblem n m where
  eqCount := m
  eqCount_le := le_rfl
  objective := objectiveFunction
  constraint := fun i x ↦ constraintFunction x i

/-- The Chapter 10 constraint map of `wilsonHanPowellPenaltyProblem objectiveFunction
constraintFunction` is exactly the recorded constraint vector `c(x)`. -/
@[simp] theorem wilsonHanPowellPenaltyProblem_constraintMap {n m : ℕ}
    (objectiveFunction : WilsonHanPowellPoint n → ℝ)
    (constraintFunction : WilsonHanPowellPoint n → WilsonHanPowellMultiplier m)
    (x : WilsonHanPowellPoint n) :
    (wilsonHanPowellPenaltyProblem objectiveFunction constraintFunction).constraintMap x =
      constraintFunction x := by
  ext i
  simp [wilsonHanPowellPenaltyProblem, StandardPenaltyProblem.constraintMap]

/-- Because all constraints are equalities, the Chapter 10 violation vector of
`wilsonHanPowellPenaltyProblem objectiveFunction constraintFunction` is exactly `c(x)`. -/
@[simp] theorem wilsonHanPowellPenaltyProblem_constraintViolation {n m : ℕ}
    (objectiveFunction : WilsonHanPowellPoint n → ℝ)
    (constraintFunction : WilsonHanPowellPoint n → WilsonHanPowellMultiplier m)
    (x : WilsonHanPowellPoint n) :
    c⁽-⁾[wilsonHanPowellPenaltyProblem objectiveFunction constraintFunction] x =
      constraintFunction x := by
  ext i
  simp [wilsonHanPowellPenaltyProblem, StandardPenaltyProblem.constraintViolation]

/-- Evaluating the Chapter 10 exact-penalty owner on the equality-only Wilson-Han-Powell bridge
gives the source formula `f(x) + σ * ‖c(x)‖₁`. -/
@[simp] theorem wilsonHanPowellPenaltyProblem_nonsmoothExactPenalty_apply {n m : ℕ}
    (objectiveFunction : WilsonHanPowellPoint n → ℝ)
    (constraintFunction : WilsonHanPowellPoint n → WilsonHanPowellMultiplier m)
    (x : WilsonHanPowellPoint n) (σ : ℝ) :
    (wilsonHanPowellPenaltyProblem objectiveFunction constraintFunction).nonsmoothExactPenalty
        (fun c ↦ c.sunYuanL1Norm) σ x =
      objectiveFunction x + σ * ‖constraintFunction x‖₁ := by
  rw [StandardPenaltyProblem.nonsmoothExactPenalty_apply]
  change
    objectiveFunction x +
        σ *
          (c⁽-⁾[wilsonHanPowellPenaltyProblem objectiveFunction constraintFunction] x).sunYuanL1Norm =
      objectiveFunction x + σ * ‖constraintFunction x‖₁
  rw [wilsonHanPowellPenaltyProblem_constraintViolation objectiveFunction constraintFunction x]

/-- The Lagrangian `L(x, λ) = f(x) + λᵀ c(x)` determined by the objective and constraints. -/
def wilsonHanPowellLagrangian {n m : ℕ}
    (objectiveFunction : WilsonHanPowellPoint n → ℝ)
    (constraintFunction : WilsonHanPowellPoint n → WilsonHanPowellMultiplier m)
    (x : WilsonHanPowellPoint n) (lam : WilsonHanPowellMultiplier m) : ℝ :=
  objectiveFunction x + dotProduct lam (constraintFunction x)

/-- Unfolding `wilsonHanPowellLagrangian objectiveFunction constraintFunction x lam` gives the
source Lagrangian formula `f(x) + λᵀ c(x)`. -/
theorem wilsonHanPowellLagrangian_eq {n m : ℕ}
    (objectiveFunction : WilsonHanPowellPoint n → ℝ)
    (constraintFunction : WilsonHanPowellPoint n → WilsonHanPowellMultiplier m)
    (x : WilsonHanPowellPoint n) (lam : WilsonHanPowellMultiplier m) :
    wilsonHanPowellLagrangian objectiveFunction constraintFunction x lam =
      objectiveFunction x + dotProduct lam (constraintFunction x) := rfl

/-- The stage-`k` quadratic objective from `(12.2.1)` built from the current gradient `g_k`
and Hessian approximation `B_k`. -/
def wilsonHanPowellStageObjective {n : ℕ}
    (g : WilsonHanPowellPoint n)
    (B : WilsonHanPowellHessianApproximation n) :
    WilsonHanPowellPoint n → ℝ :=
  fun d ↦
    dotProduct g d +
      (1 / 2 : ℝ) * dotProduct d (WithLp.toLp 2 (B.mulVec d.ofLp))

/-- Evaluating `wilsonHanPowellStageObjective g B d` gives the source quadratic model
`gᵀ d + (1 / 2) dᵀ B d`. -/
theorem wilsonHanPowellStageObjective_apply {n : ℕ}
    (g : WilsonHanPowellPoint n)
    (B : WilsonHanPowellHessianApproximation n)
    (d : WilsonHanPowellPoint n) :
    wilsonHanPowellStageObjective g B d =
      dotProduct g d +
        (1 / 2 : ℝ) * dotProduct d (WithLp.toLp 2 (B.mulVec d.ofLp)) := rfl

/-- The stage-`k` linearized constraint system from `(12.2.2)`-`(12.2.3)` built from the
current constraint value `c(x_k)` and Jacobian `A_k`. -/
def wilsonHanPowellStageFeasible {n m : ℕ}
    (c : WilsonHanPowellMultiplier m)
    (A : WilsonHanPowellConstraintJacobian n m) :
    WilsonHanPowellPoint n → Prop :=
  fun d ↦ c + WithLp.toLp 2 (A.transpose.mulVec d.ofLp) = 0

/-- Unfolding `wilsonHanPowellStageFeasible c A d` gives the source linearized constraint
equation `c + Aᵀ d = 0`. -/
theorem wilsonHanPowellStageFeasible_iff {n m : ℕ}
    (c : WilsonHanPowellMultiplier m)
    (A : WilsonHanPowellConstraintJacobian n m)
    (d : WilsonHanPowellPoint n) :
    wilsonHanPowellStageFeasible c A d ↔
      c + WithLp.toLp 2 (A.transpose.mulVec d.ofLp) = 0 := Iff.rfl

/-- The equality-constrained Step-1 quadratic subproblem built from the current stage data,
viewed through the chapter's canonical `WilsonHanPowellSubproblem` owner. -/
def wilsonHanPowellStageSubproblem {n m : ℕ}
    (g : WilsonHanPowellPoint n)
    (B : WilsonHanPowellHessianApproximation n)
    (c : WilsonHanPowellMultiplier m)
    (A : WilsonHanPowellConstraintJacobian n m) :
    WilsonHanPowellSubproblem n m 0 where
  B := B
  g := g.ofLp
  Aeq := A.transpose
  ceq := c.ofLp
  Aineq := 0
  cineq := 0

/-- Evaluating `wilsonHanPowellStageSubproblem g B c A` on a direction recovers the source
quadratic model `gᵀ d + (1 / 2) dᵀ B d`. -/
theorem wilsonHanPowellStageSubproblem_objective_eq {n m : ℕ}
    (g : WilsonHanPowellPoint n)
    (B : WilsonHanPowellHessianApproximation n)
    (c : WilsonHanPowellMultiplier m)
    (A : WilsonHanPowellConstraintJacobian n m)
    (d : WilsonHanPowellPoint n) :
    (wilsonHanPowellStageSubproblem g B c A).objective d.ofLp =
      wilsonHanPowellStageObjective g B d := rfl

/-- Membership in `wilsonHanPowellStageSubproblem g B c A` is exactly the source linearized
equality system `c + Aᵀ d = 0`; the inequality block is empty in Algorithm 12.2.2. -/
theorem wilsonHanPowellStageSubproblem_mem_iff {n m : ℕ}
    (g : WilsonHanPowellPoint n)
    (B : WilsonHanPowellHessianApproximation n)
    (c : WilsonHanPowellMultiplier m)
    (A : WilsonHanPowellConstraintJacobian n m)
    (d : WilsonHanPowellPoint n) :
    d.ofLp ∈ wilsonHanPowellStageSubproblem g B c A ↔
      wilsonHanPowellStageFeasible c A d := by
  simp only [WilsonHanPowellSubproblem.mem_iff, wilsonHanPowellStageSubproblem,
    Matrix.empty_mulVec, IsEmpty.forall_iff, and_true]
  constructor
  · intro h
    ext i
    simpa [add_comm] using congrArg (fun x : Fin m → ℝ ↦ x i) h
  · intro h
    ext i
    simpa [add_comm] using congrArg (fun x : WilsonHanPowellMultiplier m ↦ x i) h

/-- `IsStageSearchDirection g B c A d` means that `d` solves the equality-constrained
Wilson-Han-Powell subproblem determined by `g`, `B`, `c`, and `A`. This is the
`WilsonHanPowellPoint`-valued bridge to the chapter's canonical subproblem owner. -/
def IsStageSearchDirection {n m : ℕ}
    (g : WilsonHanPowellPoint n)
    (B : WilsonHanPowellHessianApproximation n)
    (c : WilsonHanPowellMultiplier m)
    (A : WilsonHanPowellConstraintJacobian n m)
    (d : WilsonHanPowellPoint n) : Prop :=
  (wilsonHanPowellStageSubproblem g B c A).IsSearchDirection d.ofLp

/-- Unfolding `IsStageSearchDirection g B c A d` gives the canonical Chapter 12
search-direction predicate for the equality-constrained stage subproblem. -/
theorem isStageSearchDirection_iff {n m : ℕ}
    (g : WilsonHanPowellPoint n)
    (B : WilsonHanPowellHessianApproximation n)
    (c : WilsonHanPowellMultiplier m)
    (A : WilsonHanPowellConstraintJacobian n m)
    (d : WilsonHanPowellPoint n) :
    IsStageSearchDirection g B c A d ↔
      (wilsonHanPowellStageSubproblem g B c A).IsSearchDirection d.ofLp := Iff.rfl

/-- The Step-4 normal matrix `Aᵀ * A` whose invertibility is needed for the source multiplier
update. -/
def wilsonHanPowellNormalMatrix {n m : ℕ}
    (A : WilsonHanPowellConstraintJacobian n m) : Matrix (Fin m) (Fin m) ℝ :=
  A.transpose * A

/-- Unfolding `wilsonHanPowellNormalMatrix A` gives the matrix product `Aᵀ * A`. -/
theorem wilsonHanPowellNormalMatrix_eq {n m : ℕ}
    (A : WilsonHanPowellConstraintJacobian n m) :
    wilsonHanPowellNormalMatrix A = A.transpose * A := rfl

/-- The Step-4 multiplier update
`λ = -((Aᵀ * A)⁻¹ * (Aᵀ * g))`, where the columns of `A` encode the constraint gradients at the
current iterate. -/
def wilsonHanPowellMultiplierUpdate {n m : ℕ}
    (A : WilsonHanPowellConstraintJacobian n m) (g : WilsonHanPowellPoint n) :
    WilsonHanPowellMultiplier m :=
  WithLp.toLp 2 (-(((wilsonHanPowellNormalMatrix A)⁻¹).mulVec (A.transpose.mulVec g)))

/-- Unfolding `wilsonHanPowellMultiplierUpdate A g` gives the source Step-4 formula
`-((Aᵀ * A)⁻¹ * (Aᵀ * g))`. -/
theorem wilsonHanPowellMultiplierUpdate_eq {n m : ℕ}
    (A : WilsonHanPowellConstraintJacobian n m) (g : WilsonHanPowellPoint n) :
    wilsonHanPowellMultiplierUpdate A g =
      WithLp.toLp 2
        (-(((wilsonHanPowellNormalMatrix A)⁻¹).mulVec (A.transpose.mulVec g))) := rfl

/-- The Step-4 quasi-Newton displacement is `s = α d`. -/
def wilsonHanPowellStepVector {n : ℕ}
    (d : WilsonHanPowellPoint n) (α : ℝ) : WilsonHanPowellPoint n :=
  α • d

/-- Unfolding `wilsonHanPowellStepVector d α` gives the source formula `s = α d`. -/
theorem wilsonHanPowellStepVector_eq {n : ℕ}
    (d : WilsonHanPowellPoint n) (α : ℝ) :
    wilsonHanPowellStepVector d α = α • d := rfl

/-- The Step-4 quasi-Newton gradient difference is
`∇ₓ L(xNext, λ) - ∇ₓ L(x, λ)`. -/
def wilsonHanPowellGradientDifference {n m : ℕ}
    (lagrangianGradient :
      WilsonHanPowellPoint n → WilsonHanPowellMultiplier m → WilsonHanPowellPoint n)
    (x xNext : WilsonHanPowellPoint n) (lam : WilsonHanPowellMultiplier m) :
    WilsonHanPowellPoint n :=
  lagrangianGradient xNext lam - lagrangianGradient x lam

/-- Unfolding `wilsonHanPowellGradientDifference lagrangianGradient x xNext lam` gives the
source formula `∇ₓ L(xNext, λ) - ∇ₓ L(x, λ)`. -/
theorem wilsonHanPowellGradientDifference_eq {n m : ℕ}
    (lagrangianGradient :
      WilsonHanPowellPoint n → WilsonHanPowellMultiplier m → WilsonHanPowellPoint n)
    (x xNext : WilsonHanPowellPoint n) (lam : WilsonHanPowellMultiplier m) :
    wilsonHanPowellGradientDifference lagrangianGradient x xNext lam =
      lagrangianGradient xNext lam - lagrangianGradient x lam := rfl

/-- Chapter12 Algorithm 12.2.2: the Wilson-Han-Powell method records the primitive
algorithm/run data for the SQP iteration. It consists of an objective function `f`, a
constraint map `c`, the positive parameters `σ` and `δ`, the tolerance `ε`, the initial
point `x₁`, the initial Hessian approximation `B₁`, the stage-indexed iterates `x_k`,
directions `d_k`, step sizes `α_k`, multipliers `λ_k`, Hessian approximations `B_k`, errors
`ε_k`, and the recorded stage data `g_k`, `A_k`, and `∇ₓ L(x_k, λ)`. For every stage `k ≥ 1`,
the direction `d_k` solves the canonical Wilson-Han-Powell quadratic subproblem built from
`g_k`, `B_k`, `c(x_k)`, and `A_k`; if `‖d_k‖ ≤ ε` the method stops, and otherwise Step 2
chooses `α_k ∈ [0, δ]` satisfying `(12.2.14)` for the canonical `L₁` exact penalty function.
Step 3 updates `x_(k + 1) = x_k + α_k d_k`, and Step 4 sets
`λ_(k + 1) = -((A_(k + 1)ᵀ * A_(k + 1))⁻¹ * (A_(k + 1)ᵀ * g_(k + 1)))`,
`s_k = α_k d_k`, and
`y_k = ∇ₓ L(x_(k + 1), λ_(k + 1)) - ∇ₓ L(x_k, λ_(k + 1))`, then updates `B_(k + 1)` by the
chosen quasi-Newton formula. The inexact line-search errors satisfy the summability condition
`∑' k, ε_(k + 1) < ∞`, the canonical form of `(12.2.15)`. -/
structure WilsonHanPowellMethod (n m : ℕ) where
  objectiveFunction : WilsonHanPowellPoint n → ℝ
  constraintFunction : WilsonHanPowellPoint n → WilsonHanPowellMultiplier m
  objectiveGradient : ℕ → WilsonHanPowellPoint n
  constraintJacobian : ℕ → WilsonHanPowellConstraintJacobian n m
  lagrangianGradient : ℕ → WilsonHanPowellMultiplier m → WilsonHanPowellPoint n
  quasiNewtonUpdate
      (B : WilsonHanPowellHessianApproximation n)
      (s y : WilsonHanPowellPoint n) :
    WilsonHanPowellHessianApproximation n
  sigma : ℝ
  delta : ℝ
  tolerance : ℝ
  initialPoint : WilsonHanPowellPoint n
  initialHessianApproximation : WilsonHanPowellHessianApproximation n
  iterate : ℕ → WilsonHanPowellPoint n
  direction : ℕ → WilsonHanPowellPoint n
  stepSize : ℕ → ℝ
  multiplier : ℕ → WilsonHanPowellMultiplier m
  hessianApproximation : ℕ → WilsonHanPowellHessianApproximation n
  lineSearchError : ℕ → ℝ
  objectiveGradient_stage_spec (k : ℕ) (hk : 1 ≤ k) :
    HasGradientAt
      objectiveFunction
      (objectiveGradient k)
      (iterate k)
  constraintJacobian_stage_spec (k : ℕ) (hk : 1 ≤ k) (i : Fin m) :
    HasGradientAt
      (fun y : WilsonHanPowellPoint n ↦ constraintFunction y i)
      (wilsonHanPowellConstraintGradient (constraintJacobian k) i)
      (iterate k)
  lagrangianGradient_stage_spec
      (k : ℕ) (hk : 1 ≤ k) (lam : WilsonHanPowellMultiplier m) :
    HasGradientAt
      (fun y : WilsonHanPowellPoint n ↦
        wilsonHanPowellLagrangian objectiveFunction constraintFunction y lam)
      (lagrangianGradient k lam)
      (iterate k)
  sigma_pos : 0 < sigma
  delta_pos : 0 < delta
  tolerance_nonneg : 0 ≤ tolerance
  iterate_one : iterate 1 = initialPoint
  hessianApproximation_one : hessianApproximation 1 = initialHessianApproximation
  direction_solution (k : ℕ) (hk : 1 ≤ k) :
    IsStageSearchDirection
      (objectiveGradient k)
      (hessianApproximation k)
      (constraintFunction (iterate k))
      (constraintJacobian k)
      (direction k)
  lineSearchError_nonneg (k : ℕ) (hk : 1 ≤ k) : 0 ≤ lineSearchError k
  lineSearchError_summable : Summable fun k : ℕ ↦ lineSearchError (k + 1)
  multiplierUpdateMatrix_isUnit
      (k : ℕ) (hk : 1 ≤ k) (h_continue : ¬ ‖direction k‖ ≤ tolerance) :
    IsUnit
      (wilsonHanPowellNormalMatrix
        (constraintJacobian (k + 1)))
  approximatePenaltyStep_spec
      (k : ℕ) (hk : 1 ≤ k) (h_continue : ¬ ‖direction k‖ ≤ tolerance) :
    IsApproximatePenaltyStep
      (fun x σ ↦
        (wilsonHanPowellPenaltyProblem objectiveFunction constraintFunction).nonsmoothExactPenalty
          (fun c ↦ c.sunYuanL1Norm) σ x)
      (iterate k)
      (direction k)
      sigma
      delta
      (stepSize k)
      (lineSearchError k)
  iterate_succ_eq_trialPoint_spec
      (k : ℕ) (hk : 1 ≤ k) (h_continue : ¬ ‖direction k‖ ≤ tolerance) :
    iterate (k + 1) =
      wilsonHanPowellTrialPoint
        (iterate k)
        (direction k)
        (stepSize k)
  multiplier_succ_eq_update_spec
      (k : ℕ) (hk : 1 ≤ k) (h_continue : ¬ ‖direction k‖ ≤ tolerance) :
    multiplier (k + 1) =
      wilsonHanPowellMultiplierUpdate
        (constraintJacobian (k + 1))
        (objectiveGradient (k + 1))
  hessianApproximation_succ_eq_update_spec
      (k : ℕ) (hk : 1 ≤ k) (h_continue : ¬ ‖direction k‖ ≤ tolerance) :
    hessianApproximation (k + 1) =
      quasiNewtonUpdate
        (hessianApproximation k)
        (wilsonHanPowellStepVector
          (direction k)
          (stepSize k))
        (lagrangianGradient (k + 1) (multiplier (k + 1)) -
          lagrangianGradient k (multiplier (k + 1)))

/-- A `WilsonHanPowellMethod` coerces to its primal iterate sequence `k ↦ x_k`. -/
instance {n m : ℕ} :
    CoeFun (WilsonHanPowellMethod n m) (fun _ ↦ ℕ → WilsonHanPowellPoint n) where
  coe method := method.iterate

/-- The objective value recorded at stage `k` is `f(x_k)`. -/
def WilsonHanPowellMethod.objectiveValueAt {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) : ℝ :=
  method.objectiveFunction (method.iterate k)

/-- The gradient recorded at stage `k` is `g_k = ∇ f(x_k)`. -/
def WilsonHanPowellMethod.gradientAt {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) : WilsonHanPowellPoint n :=
  method.objectiveGradient k

/-- The constraint value recorded at stage `k` is `c(x_k)`. -/
def WilsonHanPowellMethod.constraintValueAt {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) : WilsonHanPowellMultiplier m :=
  method.constraintFunction (method.iterate k)

/-- The Jacobian recorded at stage `k` is `A_k`, computed from the current iterate `x_k`. -/
def WilsonHanPowellMethod.constraintJacobianAt {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) :
    WilsonHanPowellConstraintJacobian n m :=
  method.constraintJacobian k

/-- The equality-constrained Wilson-Han-Powell run viewed through the Chapter 10
`StandardPenaltyProblem` owner with `eqCount = m`. -/
def WilsonHanPowellMethod.toStandardPenaltyProblem {n m : ℕ}
    (method : WilsonHanPowellMethod n m) : StandardPenaltyProblem n m :=
  wilsonHanPowellPenaltyProblem method.objectiveFunction method.constraintFunction

/-- The Stage-2 quadratic subproblem objective at stage `k` is the canonical model built from
the recorded `g_k` and `B_k`. -/
def WilsonHanPowellMethod.subproblemObjective {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) :
    WilsonHanPowellPoint n → ℝ :=
  wilsonHanPowellStageObjective
    (method.gradientAt k)
    (method.hessianApproximation k)

/-- The Stage-2 feasible predicate at stage `k` is the canonical linearized constraint system
built from `c(x_k)` and `A_k`. -/
def WilsonHanPowellMethod.subproblemFeasible {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) :
    WilsonHanPowellPoint n → Prop :=
  wilsonHanPowellStageFeasible
    (method.constraintValueAt k)
    (method.constraintJacobianAt k)

/-- The recorded Step-1 quadratic subproblem at stage `k`, specialized to the equality-only
owner `WilsonHanPowellSubproblem n m 0` used elsewhere in Chapter 12. -/
def WilsonHanPowellMethod.subproblemAt {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) :
    WilsonHanPowellSubproblem n m 0 :=
  wilsonHanPowellStageSubproblem
    (method.gradientAt k)
    (method.hessianApproximation k)
    (method.constraintValueAt k)
    (method.constraintJacobianAt k)

/-- `method.isSearchDirectionAt k` means that the recorded `d_k` solves the canonical Chapter 12
subproblem owner attached to stage `k`. -/
def WilsonHanPowellMethod.isSearchDirectionAt {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) : Prop :=
  IsStageSearchDirection
    (method.gradientAt k)
    (method.hessianApproximation k)
    (method.constraintValueAt k)
    (method.constraintJacobianAt k)
    (method.direction k)

/-- The Chapter 10 constraint map of `method.toStandardPenaltyProblem` is exactly the recorded
constraint value `c(x)`. -/
@[simp] theorem WilsonHanPowellMethod.toStandardPenaltyProblem_constraintMap {n m : ℕ}
    (method : WilsonHanPowellMethod n m)
    (x : WilsonHanPowellPoint n) :
    method.toStandardPenaltyProblem.constraintMap x = method.constraintFunction x := by
  change
    (wilsonHanPowellPenaltyProblem method.objectiveFunction method.constraintFunction).constraintMap
      x =
      method.constraintFunction x
  exact
    wilsonHanPowellPenaltyProblem_constraintMap
      method.objectiveFunction
      method.constraintFunction
      x

/-- Because `method.toStandardPenaltyProblem` has only equality constraints, its Chapter 10
violation vector is exactly the recorded constraint value `c(x)`. -/
@[simp] theorem WilsonHanPowellMethod.toStandardPenaltyProblem_constraintViolation {n m : ℕ}
    (method : WilsonHanPowellMethod n m)
    (x : WilsonHanPowellPoint n) :
    c⁽-⁾[method.toStandardPenaltyProblem] x = method.constraintFunction x := by
  change
    c⁽-⁾[wilsonHanPowellPenaltyProblem method.objectiveFunction method.constraintFunction] x =
      method.constraintFunction x
  exact
    wilsonHanPowellPenaltyProblem_constraintViolation
      method.objectiveFunction
      method.constraintFunction
      x

/-- Evaluating the Chapter 10 exact-penalty owner on `method.toStandardPenaltyProblem` gives the
source Wilson-Han-Powell formula `f(x) + σ * ‖c(x)‖₁`. -/
@[simp] theorem WilsonHanPowellMethod.toStandardPenaltyProblem_nonsmoothExactPenalty_apply
    {n m : ℕ} (method : WilsonHanPowellMethod n m)
    (x : WilsonHanPowellPoint n) (σ : ℝ) :
    method.toStandardPenaltyProblem.nonsmoothExactPenalty (fun c ↦ c.sunYuanL1Norm) σ x =
      method.objectiveFunction x + σ * ‖method.constraintFunction x‖₁ := by
  simpa [WilsonHanPowellMethod.toStandardPenaltyProblem] using
    wilsonHanPowellPenaltyProblem_nonsmoothExactPenalty_apply
      method.objectiveFunction
      method.constraintFunction
      x
      σ

/-- The recorded objective gradient at stage `k` is a genuine gradient of the source objective
function at the iterate `x_k`. -/
theorem WilsonHanPowellMethod.objectiveGradient_hasGradientAt {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) (hk : 1 ≤ k) :
    HasGradientAt
      method.objectiveFunction
      (method.objectiveGradient k)
      (method.iterate k) :=
  method.objectiveGradient_stage_spec k hk

/-- Each column of the recorded constraint Jacobian at stage `k` is the gradient of the
corresponding constraint component at the iterate `x_k`. -/
theorem WilsonHanPowellMethod.constraintJacobian_hasGradientAt {n m : ℕ}
    (method : WilsonHanPowellMethod n m)
    (k : ℕ) (hk : 1 ≤ k) (i : Fin m) :
    HasGradientAt
      (fun y : WilsonHanPowellPoint n ↦ method.constraintFunction y i)
      (wilsonHanPowellConstraintGradient
        (method.constraintJacobian k) i)
      (method.iterate k) :=
  method.constraintJacobian_stage_spec k hk i

/-- The recorded Lagrangian gradient at stage `k` is the gradient of
`wilsonHanPowellLagrangian method.objectiveFunction method.constraintFunction` at the iterate
`x_k`. -/
theorem WilsonHanPowellMethod.lagrangianGradient_hasGradientAt {n m : ℕ}
    (method : WilsonHanPowellMethod n m)
    (k : ℕ) (hk : 1 ≤ k) (lam : WilsonHanPowellMultiplier m) :
    HasGradientAt
      (fun y : WilsonHanPowellPoint n ↦
        wilsonHanPowellLagrangian
          method.objectiveFunction
          method.constraintFunction
          y
          lam)
      (method.lagrangianGradient k lam)
      (method.iterate k) :=
  method.lagrangianGradient_stage_spec k hk lam

/-- The source stopping test at stage `k` is `‖d_k‖ ≤ ε`. -/
def WilsonHanPowellMethod.terminatedAt {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) : Prop :=
  ‖method.direction k‖ ≤ method.tolerance

/-- Unfolding `method.terminatedAt k` gives the Step-2 stopping condition `‖d_k‖ ≤ ε`. -/
theorem WilsonHanPowellMethod.terminatedAt_iff {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) :
    method.terminatedAt k ↔ ‖method.direction k‖ ≤ method.tolerance := Iff.rfl

/-- The recorded Step-2 direction at stage `k` solves the canonical Chapter 12 equality-only
subproblem owner attached to that stage. -/
theorem WilsonHanPowellMethod.direction_solution_at {n m : ℕ}
    (method : WilsonHanPowellMethod n m) {k : ℕ} (hk : 1 ≤ k) :
    method.isSearchDirectionAt k :=
  method.direction_solution k hk

/-- At each stage `k`, the recorded subproblem objective is the source quadratic model
built from `g_k` and `B_k`. -/
theorem WilsonHanPowellMethod.subproblemObjective_eq_stageObjective {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) :
    method.subproblemObjective k =
      wilsonHanPowellStageObjective
        (method.gradientAt k)
        (method.hessianApproximation k) := rfl

/-- At each stage `k`, the recorded feasible predicate is the source linearized
constraint equation `c(x_k) + A_kᵀ d = 0`. -/
theorem WilsonHanPowellMethod.subproblemFeasible_iff {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ)
    (d : WilsonHanPowellPoint n) :
    method.subproblemFeasible k d ↔
      wilsonHanPowellStageFeasible
        (method.constraintValueAt k)
        (method.constraintJacobianAt k)
        d := Iff.rfl

/-- At each stage `k`, evaluating `method.subproblemAt k` on a direction recovers the source
quadratic model built from `g_k` and `B_k`. -/
theorem WilsonHanPowellMethod.subproblemAt_objective_eq {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) (d : WilsonHanPowellPoint n) :
    (method.subproblemAt k).objective d.ofLp = method.subproblemObjective k d := rfl

/-- At each stage `k`, membership in `method.subproblemAt k` is exactly the source linearized
constraint equation `c(x_k) + A_kᵀ d = 0`. -/
theorem WilsonHanPowellMethod.mem_subproblemAt_iff {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) (d : WilsonHanPowellPoint n) :
    d.ofLp ∈ method.subproblemAt k ↔ method.subproblemFeasible k d := by
  simpa [WilsonHanPowellMethod.subproblemAt, WilsonHanPowellMethod.subproblemFeasible]
    using wilsonHanPowellStageSubproblem_mem_iff
      (method.gradientAt k)
      (method.hessianApproximation k)
      (method.constraintValueAt k)
      (method.constraintJacobianAt k)
      d

/-- Unfolding `method.isSearchDirectionAt k` gives the canonical Chapter 12 search-direction
predicate for the recorded direction `d_k`. -/
theorem WilsonHanPowellMethod.isSearchDirectionAt_iff {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) :
    method.isSearchDirectionAt k ↔
      (method.subproblemAt k).IsSearchDirection (method.direction k).ofLp := Iff.rfl

/-- The recorded Step-2 direction at stage `k` belongs to the feasible set of the canonical
equality-only subproblem owner attached to that stage. -/
theorem WilsonHanPowellMethod.direction_mem_subproblemAt {n m : ℕ}
    (method : WilsonHanPowellMethod n m) {k : ℕ} (hk : 1 ≤ k) :
    (method.direction k).ofLp ∈ method.subproblemAt k := by
  have hdir : (method.subproblemAt k).IsSearchDirection (method.direction k).ofLp := by
    simpa [WilsonHanPowellMethod.isSearchDirectionAt, WilsonHanPowellMethod.subproblemAt,
      IsStageSearchDirection] using method.direction_solution_at hk
  rw [WilsonHanPowellSubproblem.isSearchDirection_iff,
    WilsonHanPowellSubproblem.isSolution_iff_mem_and_isMinOn] at hdir
  exact hdir.1

/-- The recorded Step-2 direction at stage `k` minimizes the stage quadratic model on the
canonical equality-only feasible set attached to that stage. -/
theorem WilsonHanPowellMethod.direction_minimizes_subproblemAt {n m : ℕ}
    (method : WilsonHanPowellMethod n m) {k : ℕ} (hk : 1 ≤ k) :
    IsMinOn
      (method.subproblemAt k)
      (WilsonHanPowellSubproblem.feasibleSet (method.subproblemAt k))
      (method.direction k).ofLp := by
  have hdir : (method.subproblemAt k).IsSearchDirection (method.direction k).ofLp := by
    simpa [WilsonHanPowellMethod.isSearchDirectionAt, WilsonHanPowellMethod.subproblemAt,
      IsStageSearchDirection] using method.direction_solution_at hk
  rw [WilsonHanPowellSubproblem.isSearchDirection_iff,
    WilsonHanPowellSubproblem.isSolution_iff_mem_and_isMinOn] at hdir
  exact hdir.2

/-- The `k`th recorded line-search output is the approximate penalty minimizer from
`(12.2.14)` whenever stage `k` does not terminate. -/
def WilsonHanPowellMethod.approximatePenaltyStepAt {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) : Prop :=
  IsApproximatePenaltyStep
    (fun x σ ↦ method.toStandardPenaltyProblem.nonsmoothExactPenalty (fun c ↦ c.sunYuanL1Norm) σ x)
    (method.iterate k)
    (method.direction k)
    method.sigma
    method.delta
    (method.stepSize k)
    (method.lineSearchError k)

/-- Unfolding `method.approximatePenaltyStepAt k` gives the Step-2 inexact line-search condition
on the penalty function along the ray `x_k + α d_k`. -/
theorem WilsonHanPowellMethod.approximatePenaltyStepAt_iff {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) :
    method.approximatePenaltyStepAt k ↔
      IsApproximatePenaltyStep
        (fun x σ ↦
          method.toStandardPenaltyProblem.nonsmoothExactPenalty (fun c ↦ c.sunYuanL1Norm) σ x)
        (method.iterate k)
        (method.direction k)
        method.sigma
        method.delta
        (method.stepSize k)
        (method.lineSearchError k) := Iff.rfl

/-- The Step-4 quasi-Newton displacement attached to stage `k` is `s_k = α_k d_k`. -/
def WilsonHanPowellMethod.stepVectorAt {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) : WilsonHanPowellPoint n :=
  wilsonHanPowellStepVector (method.direction k) (method.stepSize k)

/-- Unfolding `method.stepVectorAt k` gives the Step-4 displacement formula `s_k = α_k d_k`. -/
theorem WilsonHanPowellMethod.stepVectorAt_eq {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) :
    method.stepVectorAt k =
      wilsonHanPowellStepVector (method.direction k) (method.stepSize k) := rfl

/-- The Step-4 Lagrangian-gradient difference attached to stage `k` is
`y_k = ∇ₓ L(x_(k + 1), λ_(k + 1)) - ∇ₓ L(x_k, λ_(k + 1))`. -/
def WilsonHanPowellMethod.gradientDifferenceAt {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) : WilsonHanPowellPoint n :=
  method.lagrangianGradient (k + 1) (method.multiplier (k + 1)) -
    method.lagrangianGradient k (method.multiplier (k + 1))

/-- Unfolding `method.gradientDifferenceAt k` gives the source formula for `y_k`. -/
theorem WilsonHanPowellMethod.gradientDifferenceAt_eq {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) :
    method.gradientDifferenceAt k =
      method.lagrangianGradient (k + 1) (method.multiplier (k + 1)) -
        method.lagrangianGradient k (method.multiplier (k + 1)) := rfl

/-- If stage `k ≥ 1` does not terminate, then the recorded line-search output satisfies the
source inexact penalty condition `(12.2.14)`. -/
theorem WilsonHanPowellMethod.approximatePenaltyStep_at {n m : ℕ}
    (method : WilsonHanPowellMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hcont : ¬ method.terminatedAt k) :
    method.approximatePenaltyStepAt k :=
  method.approximatePenaltyStep_spec k hk hcont

/-- If stage `k ≥ 1` does not terminate, then Step 3 updates the iterate by the source formula
`x_(k + 1) = x_k + α_k d_k`. -/
theorem WilsonHanPowellMethod.iterate_succ_eq_trialPoint {n m : ℕ}
    (method : WilsonHanPowellMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hcont : ¬ method.terminatedAt k) :
    method.iterate (k + 1) =
      wilsonHanPowellTrialPoint
        (method.iterate k)
        (method.direction k)
        (method.stepSize k) :=
  method.iterate_succ_eq_trialPoint_spec k hk hcont

/-- If stage `k ≥ 1` does not terminate, then the Step-4 normal matrix
`A_(k + 1)ᵀ * A_(k + 1)` is invertible in the sense needed for the multiplier formula. -/
theorem WilsonHanPowellMethod.multiplierUpdateMatrix_isUnit_at {n m : ℕ}
    (method : WilsonHanPowellMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hcont : ¬ method.terminatedAt k) :
    IsUnit (wilsonHanPowellNormalMatrix (method.constraintJacobianAt (k + 1))) :=
  method.multiplierUpdateMatrix_isUnit k hk hcont

/-- If stage `k ≥ 1` does not terminate, then Step 4 updates the multiplier by the source
least-squares formula built from `A_(k + 1)` and `g_(k + 1)`. -/
theorem WilsonHanPowellMethod.multiplier_succ_eq_update {n m : ℕ}
    (method : WilsonHanPowellMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hcont : ¬ method.terminatedAt k) :
    method.multiplier (k + 1) =
      wilsonHanPowellMultiplierUpdate
        (method.constraintJacobianAt (k + 1))
        (method.gradientAt (k + 1)) :=
  method.multiplier_succ_eq_update_spec k hk hcont

/-- If stage `k ≥ 1` does not terminate, then the next Hessian approximation is obtained from
`B_k`, `s_k`, and `y_k` by the recorded quasi-Newton formula. -/
theorem WilsonHanPowellMethod.hessianApproximation_succ_eq_update {n m : ℕ}
    (method : WilsonHanPowellMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hcont : ¬ method.terminatedAt k) :
    method.hessianApproximation (k + 1) =
      method.quasiNewtonUpdate
        (method.hessianApproximation k)
        (method.stepVectorAt k)
        (method.gradientDifferenceAt k) := by
  simpa [WilsonHanPowellMethod.stepVectorAt, WilsonHanPowellMethod.gradientDifferenceAt] using
    method.hessianApproximation_succ_eq_update_spec k hk hcont

#print axioms wilsonHanPowellTrialPoint
#print axioms wilsonHanPowellConstraintGradient
#print axioms wilsonHanPowellPenaltyProblem
#print axioms wilsonHanPowellLagrangian
#print axioms wilsonHanPowellStageObjective
#print axioms wilsonHanPowellStageFeasible
#print axioms wilsonHanPowellNormalMatrix
#print axioms wilsonHanPowellMultiplierUpdate
#print axioms wilsonHanPowellStepVector
#print axioms wilsonHanPowellGradientDifference
