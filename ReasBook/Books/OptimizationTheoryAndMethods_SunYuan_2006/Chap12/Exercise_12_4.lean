/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_1_extra_1
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Extr

noncomputable section

section

variable {n m me mi : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "Jacobian" => Matrix (Fin n) (Fin m) ℝ
local notation "RelaxedStep" => Point × ℝ
local notation "AugmentedDirection" => Fin (n + 1) → ℝ

-- Domain sampling for this refine pass:
-- * primary domain: mixed equality/inequality SQP quadratic subproblems with a `θ`-relaxed
--   feasibility-restoration variable;
-- * inspected project owners/views for the same constraint-splitting and solution notions:
--   `feasibleConstraintValueSet`,
--   `StandardPenaltyProblem`,
--   `StandardPenaltyProblem.wilsonHanPowellSubproblem`,
--   and `WilsonHanPowellSubproblem.IsSolution`;
-- * best owner abstraction:
--   `StandardPenaltyProblem` fixes the canonical equality/inequality split datum `eqCount ≤ m`,
--   while `WilsonHanPowellSubproblem` is the canonical quadratic-model owner for the subproblem
--   itself;
-- * primitive data vs. derived API:
--   the primitive source-facing data retained here are the textbook objective
--   `gᵀ d + (1 / 2) dᵀ B d + σ (1 - θ)^2`, the linearized constraint vector
--   `Aᵀ d + θ c`, the bounds `0 ≤ θ ≤ 1`, and the augmented-variable embedding `(d, θ) ↦ (d, θ)`;
--   the mixed equality/inequality block decomposition is determined by the explicit source
--   hypothesis `eqCount ≤ m`, rather than by clipping `eqCount` with `min`;
-- * source/core/bridge triage:
--   the textbook `(d, θ)` presentation is `bridge/view`,
--   `WilsonHanPowellSubproblem` is `core/canonical`,
--   and the augmented block data below are the minimal bridge to that owner.
-- This file therefore deletes the parallel local feasibility/optimality owner and presents the
-- exercise through an augmented `WilsonHanPowellSubproblem`, with source-facing `(d, θ)`
-- statements kept only as bridge theorems.

/-- Helper for Chapter12 Exercise 12.4: the Wilson-Han-Powell mixed
equality/inequality SQP subproblem on `ℝ^n`. -/
structure WilsonHanPowellSubproblem (n me mi : ℕ) where
  B : Matrix (Fin n) (Fin n) ℝ
  g : Fin n → ℝ
  Aeq : Matrix (Fin me) (Fin n) ℝ
  ceq : Fin me → ℝ
  Aineq : Matrix (Fin mi) (Fin n) ℝ
  cineq : Fin mi → ℝ

namespace WilsonHanPowellSubproblem

/-- Helper for Chapter12 Exercise 12.4: the Wilson-Han-Powell quadratic objective
`d ↦ gᵀ d + (1 / 2) dᵀ B d`. -/
def objective
    (P : WilsonHanPowellSubproblem n me mi) (d : Fin n → ℝ) : ℝ :=
  dotProduct P.g d + (1 / 2 : ℝ) * dotProduct d (P.B.mulVec d)

/-- Helper for Chapter12 Exercise 12.4: a Wilson-Han-Powell subproblem can be
evaluated as its quadratic objective. -/
instance : CoeFun (WilsonHanPowellSubproblem n me mi) (fun _ ↦ (Fin n → ℝ) → ℝ) where
  coe P := P.objective

/-- Helper for Chapter12 Exercise 12.4: the feasible set consists of the
directions satisfying the equality block and all inequality rows. -/
def feasibleSet (P : WilsonHanPowellSubproblem n me mi) : Set (Fin n → ℝ) :=
  {d | P.Aeq.mulVec d + P.ceq = 0 ∧ ∀ i : Fin mi, 0 ≤ (P.Aineq.mulVec d) i + P.cineq i}

/-- Helper for Chapter12 Exercise 12.4: membership in a Wilson-Han-Powell
subproblem is feasibility for its linearized constraints. -/
instance : Membership (Fin n → ℝ) (WilsonHanPowellSubproblem n me mi) where
  mem P d := d ∈ P.feasibleSet

/-- Helper for Chapter12 Exercise 12.4: unfolding `d ∈ P` gives the equality
and inequality feasibility conditions. -/
@[simp] theorem mem_iff
    (P : WilsonHanPowellSubproblem n me mi) (d : Fin n → ℝ) :
    d ∈ P ↔
      P.Aeq.mulVec d + P.ceq = 0 ∧
        ∀ i : Fin mi, 0 ≤ (P.Aineq.mulVec d) i + P.cineq i :=
  Iff.rfl

/-- Helper for Chapter12 Exercise 12.4: a solution is a feasible direction that
minimizes the quadratic objective over the feasible set. -/
def IsSolution
    (P : WilsonHanPowellSubproblem n me mi) (d : Fin n → ℝ) : Prop :=
  d ∈ P ∧ IsMinOn P P.feasibleSet d

/-- Helper for Chapter12 Exercise 12.4: unfolding `P.IsSolution d` gives
feasibility together with global minimality on `P.feasibleSet`. -/
theorem isSolution_iff_mem_and_isMinOn
    (P : WilsonHanPowellSubproblem n me mi) (d : Fin n → ℝ) :
    P.IsSolution d ↔ d ∈ P ∧ IsMinOn P P.feasibleSet d :=
  Iff.rfl

end WilsonHanPowellSubproblem

/-- The source linearized constraint vector `Aᵀ d + θ c` for the relaxed SQP subproblem. -/
def thetaRelaxedLinearizedConstraintValue
    (c : ConstraintPoint) (A : Jacobian) (d : Point) (θ : ℝ) : ConstraintPoint :=
  Matrix.toEuclideanLin A.transpose d + θ • c

/-- Evaluating `thetaRelaxedLinearizedConstraintValue c A d θ` returns the source coordinate
`aᵢ(x_k)ᵀ d + θ cᵢ(x_k)`. -/
@[simp] theorem thetaRelaxedLinearizedConstraintValue_apply
    (c : ConstraintPoint) (A : Jacobian) (d : Point) (θ : ℝ) (i : Fin m) :
    thetaRelaxedLinearizedConstraintValue c A d θ i =
      (Matrix.toEuclideanLin A.transpose d) i + θ * c i :=
  rfl

/-- The textbook objective of the `θ`-relaxed SQP subproblem on the source variable `(d, θ)`. -/
def thetaRelaxedObjective (g : Point) (B : MatrixN) (σ : ℝ) : RelaxedStep → ℝ
  | (d, θ) => dotProduct g d + (1 / 2 : ℝ) * dotProduct d (B.mulVec d) + σ * (1 - θ)^2

/-- Evaluating `thetaRelaxedObjective g B σ (d, θ)` gives the textbook quadratic-plus-penalty
formula. -/
@[simp] theorem thetaRelaxedObjective_apply
    (g : Point) (B : MatrixN) (σ : ℝ) (d : Point) (θ : ℝ) :
    thetaRelaxedObjective g B σ (d, θ) =
      dotProduct g d + (1 / 2 : ℝ) * dotProduct d (B.mulVec d) + σ * (1 - θ)^2 :=
  rfl

/-- The textbook feasible set of the `θ`-relaxed SQP subproblem consists of the pairs `(d, θ)`
with `0 ≤ θ ≤ 1` and `Aᵀ d + θ c ∈ feasibleConstraintValueSet eqCount`. -/
def thetaRelaxedFeasibleSet
    (eqCount : ℕ) (c : ConstraintPoint) (A : Jacobian) :
    Set RelaxedStep :=
  {z | z.2 ∈ Set.Icc (0 : ℝ) 1 ∧
      thetaRelaxedLinearizedConstraintValue c A z.1 z.2 ∈ feasibleConstraintValueSet eqCount}

/-- Membership in `thetaRelaxedFeasibleSet eqCount c A` is exactly the textbook feasibility
condition on `(d, θ)` for the given equality/inequality split. -/
@[simp] theorem mem_thetaRelaxedFeasibleSet_iff
    (eqCount : ℕ) (c : ConstraintPoint) (A : Jacobian) (z : RelaxedStep) :
    z ∈ thetaRelaxedFeasibleSet eqCount c A ↔
      z.2 ∈ Set.Icc (0 : ℝ) 1 ∧
        thetaRelaxedLinearizedConstraintValue c A z.1 z.2 ∈ feasibleConstraintValueSet eqCount :=
  Iff.rfl

/-- The augmented coordinate embedding of the textbook variable `(d, θ)` into the canonical
Wilson-Han-Powell direction space on `ℝ^(n+1)`. -/
def relaxedStepToDirection (z : RelaxedStep) : AugmentedDirection :=
  Fin.snoc z.1 z.2

/-- Recover the textbook pair `(d, θ)` from an augmented direction in `ℝ^(n+1)`. -/
def directionToRelaxedStep (x : AugmentedDirection) : RelaxedStep :=
  (WithLp.toLp 2 (Fin.init x), x (Fin.last n))

@[simp] theorem directionToRelaxedStep_relaxedStepToDirection (z : RelaxedStep) :
    directionToRelaxedStep (relaxedStepToDirection z) = z := by
  rcases z with ⟨d, θ⟩
  simp [directionToRelaxedStep, relaxedStepToDirection]

@[simp] theorem relaxedStepToDirection_directionToRelaxedStep (x : AugmentedDirection) :
    relaxedStepToDirection (directionToRelaxedStep x) = x := by
  ext i
  cases i using Fin.lastCases with
  | last =>
      simp [directionToRelaxedStep, relaxedStepToDirection]
  | cast i =>
      simp [directionToRelaxedStep, relaxedStepToDirection, Fin.init]

private def thetaRelaxedObjectiveMatrix
    (B : MatrixN) (σ : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j ↦
    Fin.lastCases
      (Fin.lastCases (2 * σ) (fun _ ↦ 0) j)
      (fun i' ↦ Fin.lastCases 0 (fun j' ↦ B i' j') j)
      i

private def thetaRelaxedEqIndex
    (eqCount : ℕ) (hEqCount : eqCount ≤ m) : Fin eqCount → Fin m :=
  fun i ↦ ⟨i.1, Nat.lt_of_lt_of_le i.2 hEqCount⟩

private def thetaRelaxedIneqIndex
    (eqCount : ℕ) (hEqCount : eqCount ≤ m) : Fin (m - eqCount) → Fin m :=
  fun i ↦ ⟨eqCount + i.1, by
    have hi := Nat.add_lt_add_left i.2 eqCount
    simpa [Nat.add_sub_of_le hEqCount, Nat.add_assoc, Nat.add_left_comm] using hi⟩

/-- The textbook `(d, θ)`-relaxed SQP subproblem is the chapter's canonical mixed
equality/inequality quadratic-program owner on the augmented variable `(d, θ)`, with the source
split hypothesis `eqCount ≤ m` carried explicitly through the existing mixed-constraint owner
style. The equality block records the first `eqCount` relaxed linearized constraints, and the
inequality block contains the remaining relaxed linearized constraints together with the bounds
`0 ≤ θ` and `θ ≤ 1`. -/
def thetaRelaxedWilsonHanPowellSubproblem
    (eqCount : ℕ) (hEqCount : eqCount ≤ m) (c : ConstraintPoint) (g : Point)
    (A : Jacobian) (B : MatrixN) (σ : ℝ) :
    WilsonHanPowellSubproblem (n + 1) eqCount (m - eqCount + 2) where
  B := thetaRelaxedObjectiveMatrix B σ
  g := Fin.snoc g (-2 * σ)
  Aeq := fun i ↦
    Fin.snoc (fun j ↦ A j (thetaRelaxedEqIndex eqCount hEqCount i))
      (c (thetaRelaxedEqIndex eqCount hEqCount i))
  ceq := 0
  Aineq := fun i ↦
    Fin.lastCases
      (Fin.snoc (fun _ ↦ 0) (-1))
      (fun i' ↦
        Fin.lastCases
          (Fin.snoc (fun _ ↦ 0) 1)
          (fun j ↦
            Fin.snoc (fun k ↦ A k (thetaRelaxedIneqIndex eqCount hEqCount j))
              (c (thetaRelaxedIneqIndex eqCount hEqCount j)))
          i')
      i
  cineq := Fin.lastCases 1 (fun i ↦ Fin.lastCases 0 (fun _ ↦ 0) i)

private theorem dotProduct_relaxedStepToDirection
    (d d' : Point) (θ θ' : ℝ) :
    dotProduct (relaxedStepToDirection (d, θ)) (relaxedStepToDirection (d', θ')) =
      dotProduct d d' + θ * θ' := by
  simp [relaxedStepToDirection, dotProduct, Fin.sum_univ_castSucc]

private theorem thetaRelaxedObjectiveMatrix_mulVec
    (B : MatrixN) (σ : ℝ) (d : Point) (θ : ℝ) :
    (thetaRelaxedObjectiveMatrix B σ).mulVec (relaxedStepToDirection (d, θ)) =
      Fin.snoc (B.mulVec d) (2 * σ * θ) := by
  -- Read the augmented Hessian one coordinate at a time.
  ext i
  cases i using Fin.lastCases with
  | last =>
      simp [thetaRelaxedObjectiveMatrix, Matrix.mulVec, dotProduct, relaxedStepToDirection,
        Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc,
        mul_left_comm, mul_comm]
  | cast i =>
      simp [thetaRelaxedObjectiveMatrix, Matrix.mulVec, dotProduct, relaxedStepToDirection,
        Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc]

private theorem thetaRelaxedObjective_eq_objective_add
    (eqCount : ℕ) (hEqCount : eqCount ≤ m) (c : ConstraintPoint) (g : Point)
    (A : Jacobian) (B : MatrixN) (σ : ℝ) (z : RelaxedStep) :
    thetaRelaxedObjective g B σ z =
      (thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ).objective
          (relaxedStepToDirection z) + σ := by
  -- The augmented owner stores exactly the quadratic part; the source penalty differs by `+σ`.
  rcases z with ⟨d, θ⟩
  rw [thetaRelaxedObjective_apply, WilsonHanPowellSubproblem.objective]
  simp only [thetaRelaxedWilsonHanPowellSubproblem, one_div]
  rw [thetaRelaxedObjectiveMatrix_mulVec B σ d θ]
  have hg :
      Fin.snoc g.ofLp (-2 * σ) = relaxedStepToDirection (g, -2 * σ) := rfl
  have hb :
      Fin.snoc (B.mulVec d.ofLp) (2 * σ * θ) =
        relaxedStepToDirection (WithLp.toLp 2 (B.mulVec d), 2 * σ * θ) := rfl
  rw [hg, hb]
  rw [dotProduct_relaxedStepToDirection g d (-2 * σ) θ]
  rw [dotProduct_relaxedStepToDirection d (WithLp.toLp 2 (B.mulVec d)) θ (2 * σ * θ)]
  ring

private theorem thetaRelaxedAeq_row
    (eqCount : ℕ) (hEqCount : eqCount ≤ m) (c : ConstraintPoint) (g : Point)
    (A : Jacobian) (B : MatrixN) (σ : ℝ) (d : Point) (θ : ℝ) (i : Fin eqCount) :
    ((thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ).Aeq.mulVec
        (relaxedStepToDirection (d, θ))) i +
      (thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ).ceq i =
        thetaRelaxedLinearizedConstraintValue c A d θ (thetaRelaxedEqIndex eqCount hEqCount i) := by
  -- The equality block is the source linearized constraint restricted to the first `eqCount` rows.
  simp [thetaRelaxedWilsonHanPowellSubproblem, thetaRelaxedLinearizedConstraintValue,
    Matrix.mulVec, dotProduct, relaxedStepToDirection, Fin.sum_univ_castSucc, mul_comm]

private theorem thetaRelaxedAineq_row
    (eqCount : ℕ) (hEqCount : eqCount ≤ m) (c : ConstraintPoint) (g : Point)
    (A : Jacobian) (B : MatrixN) (σ : ℝ) (d : Point) (θ : ℝ) (i : Fin (m - eqCount)) :
    ((thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ).Aineq.mulVec
        (relaxedStepToDirection (d, θ))) i.castSucc.castSucc +
      (thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ).cineq i.castSucc.castSucc =
        thetaRelaxedLinearizedConstraintValue c A d θ
          (thetaRelaxedIneqIndex eqCount hEqCount i) := by
  -- The interior inequality rows are the source inequality constraints after the equality block.
  simp [thetaRelaxedWilsonHanPowellSubproblem, thetaRelaxedLinearizedConstraintValue,
    Matrix.mulVec, dotProduct, relaxedStepToDirection, Fin.sum_univ_castSucc, mul_comm]

private theorem thetaRelaxedThetaNonneg_row
    (eqCount : ℕ) (hEqCount : eqCount ≤ m) (c : ConstraintPoint) (g : Point)
    (A : Jacobian) (B : MatrixN) (σ : ℝ) (d : Point) (θ : ℝ) :
    ((thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ).Aineq.mulVec
        (relaxedStepToDirection (d, θ))) (Fin.castSucc (Fin.last (m - eqCount))) +
      (thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ).cineq
        (Fin.castSucc (Fin.last (m - eqCount))) =
        θ := by
  -- The penultimate inequality row records `θ ≥ 0`.
  simp [thetaRelaxedWilsonHanPowellSubproblem, Matrix.mulVec, dotProduct,
    relaxedStepToDirection, Fin.sum_univ_castSucc]

private theorem thetaRelaxedThetaLeOne_row
    (eqCount : ℕ) (hEqCount : eqCount ≤ m) (c : ConstraintPoint) (g : Point)
    (A : Jacobian) (B : MatrixN) (σ : ℝ) (d : Point) (θ : ℝ) :
    ((thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ).Aineq.mulVec
        (relaxedStepToDirection (d, θ))) (Fin.last (m - eqCount + 1)) +
      (thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ).cineq
        (Fin.last (m - eqCount + 1)) =
        1 - θ := by
  -- The last inequality row records `θ ≤ 1`.
  simp [thetaRelaxedWilsonHanPowellSubproblem, Matrix.mulVec, dotProduct,
    relaxedStepToDirection, Fin.sum_univ_castSucc]
  ring

private theorem mem_thetaRelaxedWilsonHanPowellSubproblem_iff
    (eqCount : ℕ) (hEqCount : eqCount ≤ m) (c : ConstraintPoint) (g : Point)
    (A : Jacobian) (B : MatrixN) (σ : ℝ) (z : RelaxedStep) :
    relaxedStepToDirection z ∈ thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ ↔
      z ∈ thetaRelaxedFeasibleSet eqCount c A := by
  -- Unfold feasibility once, then translate each owner row back to the source constraints.
  rcases z with ⟨d, θ⟩
  rw [WilsonHanPowellSubproblem.mem_iff, mem_thetaRelaxedFeasibleSet_iff,
    mem_feasibleConstraintValueSet_iff]
  constructor
  · intro hz
    rcases hz with ⟨hEq, hIneq⟩
    refine ⟨?_, ?_⟩
    · refine Set.mem_Icc.mpr ⟨?_, ?_⟩
      · have hθ :=
          hIneq (Fin.castSucc (Fin.last (m - eqCount)))
        rwa [thetaRelaxedThetaNonneg_row eqCount hEqCount c g A B σ d θ] at hθ
      · have hθ :=
          hIneq (Fin.last (m - eqCount + 1))
        rw [thetaRelaxedThetaLeOne_row eqCount hEqCount c g A B σ d θ] at hθ
        linarith
    · constructor
      · intro j hj
        let iEq : Fin eqCount := ⟨j.1, hj⟩
        have hcoord :
            ((thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ).Aeq.mulVec
                (relaxedStepToDirection (d, θ))) iEq +
              (thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ).ceq iEq = 0 := by
          simpa [iEq] using congrArg (fun y : Fin eqCount → ℝ => y iEq) hEq
        have hrow :=
          thetaRelaxedAeq_row eqCount hEqCount c g A B σ d θ iEq
        simpa [iEq, thetaRelaxedEqIndex] using hrow.symm.trans hcoord
      · intro j hj
        let iIneq : Fin (m - eqCount) := ⟨j.1 - eqCount, Nat.sub_lt_sub_right hj j.2⟩
        have hrow :=
          thetaRelaxedAineq_row eqCount hEqCount c g A B σ d θ iIneq
        have hcoord :
            0 ≤
              ((thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ).Aineq.mulVec
                  (relaxedStepToDirection (d, θ))) iIneq.castSucc.castSucc +
                (thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ).cineq
                  iIneq.castSucc.castSucc :=
          hIneq iIneq.castSucc.castSucc
        have hlin :
            0 ≤ thetaRelaxedLinearizedConstraintValue c A d θ
              (thetaRelaxedIneqIndex eqCount hEqCount iIneq) := by
          simpa [hrow] using hcoord
        simpa [iIneq, thetaRelaxedIneqIndex, Nat.add_sub_of_le hj] using hlin
  · intro hz
    rcases hz with ⟨hθ, hFeas⟩
    rcases Set.mem_Icc.mp hθ with ⟨hθ0, hθ1⟩
    rcases hFeas with ⟨hEq, hIneq⟩
    refine ⟨?_, ?_⟩
    · ext i
      have hrow := thetaRelaxedAeq_row eqCount hEqCount c g A B σ d θ i
      have hzero :
          thetaRelaxedLinearizedConstraintValue c A d θ
            (thetaRelaxedEqIndex eqCount hEqCount i) = 0 :=
        hEq (thetaRelaxedEqIndex eqCount hEqCount i) (by simp [thetaRelaxedEqIndex, i.2])
      simpa [hrow] using hzero
    · intro i
      cases i using Fin.lastCases with
      | last =>
          have hbound : 0 ≤ 1 - θ := by
            linarith
          simpa [thetaRelaxedThetaLeOne_row eqCount hEqCount c g A B σ d θ] using hbound
      | cast i =>
          cases i using Fin.lastCases with
          | last =>
              simpa [thetaRelaxedThetaNonneg_row eqCount hEqCount c g A B σ d θ] using hθ0
          | cast j =>
              have hlin :
                  0 ≤ thetaRelaxedLinearizedConstraintValue c A d θ
                    (thetaRelaxedIneqIndex eqCount hEqCount j) :=
                hIneq (thetaRelaxedIneqIndex eqCount hEqCount j)
                  (by simp [thetaRelaxedIneqIndex, Nat.le_add_right eqCount j.1])
              simpa [thetaRelaxedAineq_row eqCount hEqCount c g A B σ d θ j] using hlin

private theorem isMinOn_thetaRelaxedObjective_iff
    (eqCount : ℕ) (hEqCount : eqCount ≤ m) (c : ConstraintPoint) (g : Point)
    (A : Jacobian) (B : MatrixN) (σ : ℝ) (z : RelaxedStep) :
    IsMinOn
        (thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ)
        (thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ).feasibleSet
        (relaxedStepToDirection z) ↔
      IsMinOn (thetaRelaxedObjective g B σ) (thetaRelaxedFeasibleSet eqCount c A) z := by
  -- Transport competitors across the augmented embedding, then cancel the additive `σ`.
  rw [isMinOn_iff, isMinOn_iff]
  constructor
  · intro h z' hz'
    have hz'' :
        relaxedStepToDirection z' ∈
          thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ :=
      (mem_thetaRelaxedWilsonHanPowellSubproblem_iff eqCount hEqCount c g A B σ z').2 hz'
    have hle := h (relaxedStepToDirection z') hz''
    have hzEq := thetaRelaxedObjective_eq_objective_add eqCount hEqCount c g A B σ z
    have hz'Eq := thetaRelaxedObjective_eq_objective_add eqCount hEqCount c g A B σ z'
    linarith
  · intro h x hx
    let z' := directionToRelaxedStep x
    have hxmem :
        x ∈ thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ :=
      hx
    have hx' :
        relaxedStepToDirection z' ∈
          thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ := by
      simpa [z'] using hxmem
    have hz' :
        z' ∈ thetaRelaxedFeasibleSet eqCount c A :=
      (mem_thetaRelaxedWilsonHanPowellSubproblem_iff eqCount hEqCount c g A B σ z').1 hx'
    have hle := h z' hz'
    have hzEq := thetaRelaxedObjective_eq_objective_add eqCount hEqCount c g A B σ z
    have hz'Eq := thetaRelaxedObjective_eq_objective_add eqCount hEqCount c g A B σ z'
    have hle' : thetaRelaxedObjective g B σ z ≤ thetaRelaxedObjective g B σ z' := by
      linarith
    have hleOwner :
        (thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ).objective
            (relaxedStepToDirection z) ≤
          (thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ).objective
            (relaxedStepToDirection z') := by
      linarith
    simpa [z'] using hleOwner

/-- Solving the canonical augmented Wilson-Han-Powell owner is exactly solving the textbook
`θ`-relaxed SQP subproblem on `(d, θ)`: the feasible sets agree exactly, and the owner objective
differs from the textbook objective only by the additive constant `σ`, so the minimizers are the
same. -/
theorem thetaRelaxedWilsonHanPowellSubproblem_isSolution_iff
    (eqCount : ℕ) (hEqCount : eqCount ≤ m) (c : ConstraintPoint) (g : Point)
    (A : Jacobian) (B : MatrixN) (σ : ℝ) (z : RelaxedStep) :
    (thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ).IsSolution
        (relaxedStepToDirection z) ↔
      z ∈ thetaRelaxedFeasibleSet eqCount c A ∧
        IsMinOn (thetaRelaxedObjective g B σ) (thetaRelaxedFeasibleSet eqCount c A) z := by
  rw [WilsonHanPowellSubproblem.isSolution_iff_mem_and_isMinOn]
  rw [mem_thetaRelaxedWilsonHanPowellSubproblem_iff eqCount hEqCount c g A B σ z,
    isMinOn_thetaRelaxedObjective_iff eqCount hEqCount c g A B σ z]

/-- Chapter12 Exercise 12.4: if `(d(σ), θ(σ))` solves the `θ`-relaxed SQP subproblem at two
ordered penalty parameters `σ₁ ≤ σ₂`, then `θ(σ)` is nondecreasing. The hypotheses use the
chapter's canonical augmented `WilsonHanPowellSubproblem` owner. -/
theorem thetaSolution_nondecreasing_of_thetaRelaxedWilsonHanPowellSubproblem_isSolution
    (eqCount : ℕ) (hEqCount : eqCount ≤ m) (c : ConstraintPoint) (g : Point)
    (A : Jacobian) (B : MatrixN)
    (d : ℝ → Point) (θ : ℝ → ℝ)
    {σ₁ σ₂ : ℝ}
    (hσ : σ₁ ≤ σ₂)
    (hsol₁ :
      (thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ₁).IsSolution
        (relaxedStepToDirection (d σ₁, θ σ₁)))
    (hsol₂ :
      (thetaRelaxedWilsonHanPowellSubproblem eqCount hEqCount c g A B σ₂).IsSolution
        (relaxedStepToDirection (d σ₂, θ σ₂))) :
    θ σ₁ ≤ θ σ₂ := by
  -- If the penalties coincide, the two function values coincide as well.
  by_cases hEq : σ₁ = σ₂
  · simp [hEq]
  have hσlt : σ₁ < σ₂ := lt_of_le_of_ne hσ hEq
  -- Rewrite both solution hypotheses onto the common source feasible set.
  rcases (thetaRelaxedWilsonHanPowellSubproblem_isSolution_iff
      eqCount hEqCount c g A B σ₁ (d σ₁, θ σ₁)).1 hsol₁ with ⟨hz₁, hmin₁⟩
  rcases (thetaRelaxedWilsonHanPowellSubproblem_isSolution_iff
      eqCount hEqCount c g A B σ₂ (d σ₂, θ σ₂)).1 hsol₂ with ⟨hz₂, hmin₂⟩
  rcases (mem_thetaRelaxedFeasibleSet_iff eqCount c A (d σ₁, θ σ₁)).1 hz₁ with ⟨hθ₁, _⟩
  rcases (mem_thetaRelaxedFeasibleSet_iff eqCount c A (d σ₂, θ σ₂)).1 hz₂ with ⟨hθ₂, _⟩
  rcases Set.mem_Icc.mp hθ₁ with ⟨hθ₁_nonneg, hθ₁_le⟩
  rcases Set.mem_Icc.mp hθ₂ with ⟨hθ₂_nonneg, hθ₂_le⟩
  have hθ₁_nonneg' : 0 ≤ θ σ₁ := by simpa using hθ₁_nonneg
  have hθ₁_le' : θ σ₁ ≤ 1 := by simpa using hθ₁_le
  have hθ₂_nonneg' : 0 ≤ θ σ₂ := by simpa using hθ₂_nonneg
  have hθ₂_le' : θ σ₂ ≤ 1 := by simpa using hθ₂_le
  -- Compare each minimizer against the other feasible point.
  have h12 := (isMinOn_iff.mp hmin₁) (d σ₂, θ σ₂) hz₂
  have h21 := (isMinOn_iff.mp hmin₂) (d σ₁, θ σ₁) hz₁
  rw [thetaRelaxedObjective_apply, thetaRelaxedObjective_apply] at h12
  rw [thetaRelaxedObjective_apply, thetaRelaxedObjective_apply] at h21
  have hOne₁ : 0 ≤ 1 - θ σ₁ := by
    linarith
  have hOne₂ : 0 ≤ 1 - θ σ₂ := by
    linarith
  -- Summing the two optimality inequalities isolates the penalty terms.
  have hpenalty :
      σ₁ * (1 - θ σ₁)^2 + σ₂ * (1 - θ σ₂)^2 ≤
        σ₁ * (1 - θ σ₂)^2 + σ₂ * (1 - θ σ₁)^2 := by
    nlinarith [h12, h21]
  have hσ' : 0 < σ₂ - σ₁ := sub_pos.mpr hσlt
  have hp : (1 - θ σ₂)^2 ≤ (1 - θ σ₁)^2 := by
    nlinarith [hpenalty, hσ']
  have hcomp : 1 - θ σ₂ ≤ 1 - θ σ₁ :=
    (sq_le_sq₀ hOne₂ hOne₁).1 hp
  linarith

/- The source also asks to discuss the extreme case `θ(σ) = 0` for all `σ > 0`.
   No precise downstream theorem for that discussion clause is fixed here, so it is kept as
   source commentary rather than a second owner or wrapper API. -/

end
