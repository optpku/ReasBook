/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Theorem_9_1_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Remark_13_1_extra_1
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

noncomputable section

section

variable {n m : ℕ}

local notation "Step" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)
local notation "Decision" => EuclideanSpace ℝ (Fin (n + 1))
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "Jacobian" => Matrix (Fin n) (Fin m) ℝ

-- Domain-style sampling for this refine pass:
-- * primary domain: trust-region penalty subproblems and their quadratic-program
--   reformulations;
-- * sampled owner declarations:
--   `linftyNorm` and `IsVectorNorm` from Chapter 01, `trustRegionPenaltySubproblem` and
--   `trustRegionPenaltyObjective` from Chapter 13, together with Chapter 9's
--   `QuadraticProgram.objective` and `QuadraticProgram.feasibleSet`;
-- * source-facing owner: `trustRegionPenaltySubproblem`;
-- * core/canonical owner: `QuadraticProgram`;
-- * bridge/view in this file: the quadratic/`ℓ∞`/negative-part specialization and its
--   lifted quadratic-program reformulation.

/-- The quadratic trust-region model
`d ↦ g_kᵀ d + (1 / 2) dᵀ B_k d` on the Chapter 13 step space
`EuclideanSpace ℝ (Fin n)`. -/
def quadraticModelObjective
    (g : Step) (B : MatrixN) (d : Step) : ℝ :=
  dotProduct g d + (1 / 2 : ℝ) * dotProduct d (B.mulVec d)

/-- The decision vector `(d, t)` for the quadratic-program reformulation. -/
def liftDecision
    (d : Step) (t : ℝ) : Decision :=
  WithLp.toLp 2 (Fin.snoc d.ofLp t)

/-- The `d`-component of a reformulation decision vector `(d, t)`. -/
def stepComponent
    (x : Decision) : Step :=
  WithLp.toLp 2 (Fin.init x.ofLp)

/-- The epigraph variable `t` in a reformulation decision vector `(d, t)`. -/
def slackComponent
    (x : Decision) : ℝ :=
  x (Fin.last n)

/-- Projecting the lifted decision `(d, t)` back to the step component recovers `d`. -/
@[simp] theorem stepComponent_liftDecision
    (d : Step) (t : ℝ) :
    stepComponent (liftDecision d t) = d := by
  ext i
  simp [stepComponent, liftDecision]

/-- Projecting the lifted decision `(d, t)` to the slack coordinate recovers `t`. -/
@[simp] theorem slackComponent_liftDecision
    (d : Step) (t : ℝ) :
    slackComponent (liftDecision d t) = t := by
  simp [slackComponent, liftDecision]

/-- The coordinate vector `e_i` in `ℝ^(n+1)`, used to encode the trust-region and `t ≥ 0`
inequalities of the reformulated quadratic program. -/
def decisionCoordinateVector
    (i : Fin (n + 1)) : Decision :=
  EuclideanSpace.single i 1

/-- The `i`-th column of `A_k`, viewed as a step-space vector so that its pairing with `d`
recovers the `i`-th component of `A_kᵀ d`. -/
def constraintColumn
    (A : Jacobian) (i : Fin m) : Step :=
  WithLp.toLp 2 (A.col i)

/-- The symmetric part `(B + Bᵀ) / 2` of the source Hessian block `B`. This is the canonical
quadratic-program owner data because it yields the same quadratic form `dᵀ B d`. -/
def symmetricPart
    (B : MatrixN) : MatrixN :=
  (1 / 2 : ℝ) • (B + B.transpose)

/-- The symmetric part of `B` is symmetric. -/
theorem isSymm_symmetricPart
    (B : MatrixN) :
    (symmetricPart B).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp [symmetricPart]
  ring

/-- The lifted Hessian matrix on `(d, t)` uses the symmetric part of the source block `B_k` on
the `d` coordinates and zeros in the last row and last column, so the reformulated objective
stays quadratic in `d` and linear in `t`. -/
def liftedHessianMatrix
    (B : MatrixN) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Fin.snoc
    (fun i : Fin n ↦ Fin.snoc (fun j : Fin n ↦ symmetricPart B i j) 0)
    (fun _ : Fin (n + 1) ↦ 0)

/-- The inequalities in the quadratic-program reformulation: one family for
`t ≥ -(c_k + A_kᵀ d)`, one for `t ≥ 0`, and two families for `-Δ_k ≤ d_j ≤ Δ_k`. -/
inductive ReformulationConstraintIndex (n m : ℕ)
  | penalty (i : Fin m)
  | slackNonneg
  | trustRegionLower (j : Fin n)
  | trustRegionUpper (j : Fin n)
deriving Fintype, DecidableEq

/-- The coefficient vector of each linear inequality in the reformulated quadratic program. -/
def reformulationConstraintVector
    (A : Jacobian) :
    ReformulationConstraintIndex n m → Decision
  | .penalty i => liftDecision (constraintColumn A i) 1
  | .slackNonneg => decisionCoordinateVector (Fin.last n)
  | .trustRegionLower j => decisionCoordinateVector j.castSucc
  | .trustRegionUpper j => -decisionCoordinateVector j.castSucc

/-- The right-hand side of each linear inequality in the reformulated quadratic program. -/
def reformulationConstraintRhs
    (c : ConstraintPoint) (Δ : ℝ) :
    ReformulationConstraintIndex n m → ℝ
  | .penalty i => -c i
  | .slackNonneg => 0
  | .trustRegionLower _ => -Δ
  | .trustRegionUpper _ => -Δ

/-- Chapter 13 Exercise 13.1: the quadratic/`ℓ∞`/negative-part specialization of the Chapter 13
penalty subproblem is reformulated as the explicit quadratic program on the lifted variable
`(d, t) ∈ ℝ^(n+1)`. This declaration is the bridge/view layer from the Chapter 13
trust-region-penalty source data to Chapter 9's canonical owner `QuadraticProgram`. -/
def reformulatedQuadraticProgram
    (g : Step) (B : MatrixN) (σ : ℝ)
    (c : ConstraintPoint) (A : Jacobian) (Δ : ℝ) :
    QuadraticProgram (n + 1) 0 (Fintype.card (ReformulationConstraintIndex n m)) :=
  let e : ReformulationConstraintIndex n m ≃
      Fin (Fintype.card (ReformulationConstraintIndex n m)) :=
    Fintype.equivFin (ReformulationConstraintIndex n m)
  { G := liftedHessianMatrix B
    hG_symm := by
      rw [Matrix.IsSymm.ext_iff]
      intro i j
      have hSymm := isSymm_symmetricPart B
      induction i using Fin.lastCases with
      | last =>
          induction j using Fin.lastCases <;>
            simp [liftedHessianMatrix, Fin.snoc_last, Fin.snoc_castSucc]
      | cast i =>
          induction j using Fin.lastCases with
          | last =>
              simp [liftedHessianMatrix, Fin.snoc_last, Fin.snoc_castSucc]
          | cast j =>
              simpa [liftedHessianMatrix, Fin.snoc_castSucc] using Matrix.IsSymm.apply hSymm i j
    g := liftDecision g σ
    Aeq := 0
    beq := 0
    Aineq := fun i j ↦ reformulationConstraintVector A (e.symm i) j
    bineq := WithLp.toLp 2 fun i ↦ reformulationConstraintRhs c Δ (e.symm i) }

/-- The Chapter 9 quadratic-program objective of the lifted reformulation is exactly
`g_kᵀ d + (1 / 2) dᵀ B_k d + σ_k t` on the decision variable `(d, t)`. -/
theorem reformulatedQuadraticProgram_objective_eq
    (g : Step) (B : MatrixN) (σ : ℝ)
    (c : ConstraintPoint) (A : Jacobian) (Δ : ℝ) (x : Decision) :
    (reformulatedQuadraticProgram g B σ c A Δ).objective x =
      quadraticModelObjective g B (stepComponent x) + σ * slackComponent x := by
  sorry

/-- Membership in the feasible set of the lifted quadratic program is exactly the conjunction of
the `ℓ∞` trust-region bound, the nonnegativity constraint `t ≥ 0`, and the epigraph
inequalities `-(c_k + A_kᵀ d)_i ≤ t`. -/
@[simp] theorem mem_reformulatedQuadraticProgram_feasibleSet_iff
    (g : Step) (B : MatrixN) (σ : ℝ)
    (c : ConstraintPoint) (A : Jacobian) (Δ : ℝ) (x : Decision) :
    x ∈ (reformulatedQuadraticProgram g B σ c A Δ).feasibleSet ↔
      stepComponent x ∈ trustRegionPenaltyFeasibleSet linftyNorm Δ ∧
        0 ≤ slackComponent x ∧
          ∀ i : Fin m, -(linearizedConstraintValue c A (stepComponent x) i) ≤ slackComponent x := by
  sorry

/-- The feasible set of the lifted quadratic program is exactly the explicit epigraph/trust-region
set cut out by the source inequalities. -/
theorem reformulatedQuadraticProgram_feasibleSet_eq
    (g : Step) (B : MatrixN) (σ : ℝ)
    (c : ConstraintPoint) (A : Jacobian) (Δ : ℝ) :
    (reformulatedQuadraticProgram g B σ c A Δ).feasibleSet =
      {x | stepComponent x ∈ trustRegionPenaltyFeasibleSet linftyNorm Δ ∧
          0 ≤ slackComponent x ∧
            ∀ i : Fin m, -(linearizedConstraintValue c A (stepComponent x) i) ≤
              slackComponent x} := by
  ext x
  exact mem_reformulatedQuadraticProgram_feasibleSet_iff g B σ c A Δ x

/-- Evaluating the lifted quadratic-program objective at `(d, t)` gives
`g_kᵀ d + (1 / 2) dᵀ B_k d + σ_k t`. -/
@[simp] theorem reformulatedQuadraticProgram_objective_liftDecision_eq
    (g : Step) (B : MatrixN) (σ : ℝ)
    (c : ConstraintPoint) (A : Jacobian) (Δ : ℝ)
    (d : Step) (t : ℝ) :
    (reformulatedQuadraticProgram g B σ c A Δ).objective (liftDecision d t) =
      quadraticModelObjective g B d + σ * t := by
  simp [reformulatedQuadraticProgram_objective_eq]

/- Feasibility of `(d, t)` in the lifted reformulation is exactly the conjunction of the
`ℓ∞` trust-region bound, the nonnegativity constraint `t ≥ 0`, and the epigraph inequalities
`-(c_k + A_kᵀ d)_i ≤ t`. -/
@[simp] theorem liftDecision_mem_reformulatedQuadraticProgram_feasibleSet_iff
    (g : Step) (B : MatrixN) (σ : ℝ)
    (c : ConstraintPoint) (A : Jacobian) (Δ : ℝ)
    (d : Step) (t : ℝ) :
    liftDecision d t ∈ (reformulatedQuadraticProgram g B σ c A Δ).feasibleSet ↔
      d ∈ trustRegionPenaltyFeasibleSet linftyNorm Δ ∧ 0 ≤ t ∧
        ∀ i : Fin m, -(linearizedConstraintValue c A d i) ≤ t := by
  rw [mem_reformulatedQuadraticProgram_feasibleSet_iff]
  simp

/-- If `d` is feasible for the specialized Chapter 13 penalty subproblem, then the exact
epigraph lift `(d, ‖(c_k + A_kᵀ d)⁽-⁾‖∞)` is feasible for the reformulated quadratic program,
and the quadratic-program objective at that lift is exactly the value of the canonical Chapter 13
source-facing owner `trustRegionPenaltySubproblem` at `d`. -/
theorem exactEpigraphLift_mem_reformulatedQuadraticProgram_and_subproblem_eq
    (g : Step) (B : MatrixN) (σ : ℝ)
    (c : ConstraintPoint) (A : Jacobian) (Δ : ℝ)
    {d : Step} (hd : d ∈ trustRegionPenaltyFeasibleSet linftyNorm Δ) :
    let x := liftDecision d ‖((linearizedConstraintValue c A d)⁻).ofLp‖∞
    x ∈ (reformulatedQuadraticProgram g B σ c A Δ).feasibleSet ∧
      (reformulatedQuadraticProgram g B σ c A Δ).objective x =
        trustRegionPenaltySubproblem
          linftyNorm
          Δ
          (fun y ↦ ‖(y⁻).ofLp‖∞)
          σ
          (quadraticModelObjective g B)
          c
          A
          ⟨d, hd⟩ := sorry

/-- Every feasible point `(d, t)` of the reformulated quadratic program projects to a
trust-region-feasible step `d`, and its objective dominates the specialized Chapter 13 penalty
objective at that projected step because `t` majorizes `‖(c_k + A_kᵀ d)⁽-⁾‖∞`. -/
theorem projectedStep_mem_trustRegionPenaltyFeasibleSet_and_objective_le_of_reformulatedFeasible
    (g : Step) (B : MatrixN) (σ : ℝ)
    (c : ConstraintPoint) (A : Jacobian) (Δ : ℝ)
    {x : Decision}
    (hx : x ∈ (reformulatedQuadraticProgram g B σ c A Δ).feasibleSet) :
    stepComponent x ∈ trustRegionPenaltyFeasibleSet linftyNorm Δ ∧
      trustRegionPenaltyObjective
        (fun y ↦ ‖(y⁻).ofLp‖∞)
        σ
        (quadraticModelObjective g B)
        c
        A
        (stepComponent x) ≤
      (reformulatedQuadraticProgram g B σ c A Δ).objective x := sorry

#print axioms reformulatedQuadraticProgram

end
