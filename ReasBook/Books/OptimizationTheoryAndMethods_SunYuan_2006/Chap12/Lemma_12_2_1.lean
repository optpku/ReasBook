/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_6_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Definition_12_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.OneSidedDirectionalDeriv
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)
local notation "Multiplier" => EuclideanSpace ℝ (Fin m)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "Jacobian" => Matrix (Fin n) (Fin m) ℝ

-- Domain sampling:
-- * primary domain: Wilson-Han-Powell SQP penalty analysis for a mixed equality/inequality
--   constrained problem on `ℝ^n`
-- * inspected owner abstractions in the project:
--   `StandardPenaltyProblem.constraintMap`, `StandardPenaltyProblem.constraintViolation`, and
--   `StandardPenaltyProblem.nonsmoothExactPenalty` in Chapter 10,
--   `WilsonHanPowellSubproblem` / `WilsonHanPowellSubproblem.SatisfiesKKT` in Chapter 12, and
--   the Chapter 1 `‖·‖₁` and `‖·‖∞` norm notation on finite coordinate spaces
-- * retained source-facing local layer here:
--   the affine linearized constraint residual `c + Aᵀ d`, the mixed-constraint bridge to the
--   canonical Wilson-Han-Powell KKT predicate on a combined multiplier `λ`, the named `L₁`
--   exact penalty `x ↦ f(x) + σ * ‖c⁽-⁾(x)‖₁`, and the scalar path `α ↦ P(xk + α • dk, σ)`

-- Semantic recall: `lineDeriv` / `HasLineDerivAt` is the canonical directional-derivative API,
-- and the repository owner `HasOneSidedDirectionalDerivAt` packages the right directional
-- derivative of the Chapter 12 penalty function along a search direction. The mixed-constraint
-- penalty object itself is already owned upstream by `StandardPenaltyProblem`, and the Chapter 12
-- SQP subproblem/KKT data are already owned by `WilsonHanPowellSubproblem`.

/-- The linearized constraint vector `c + Aᵀ d` of the SQP subproblem. -/
def linearizedConstraintValue
    (c : ConstraintPoint) (A : Jacobian) (d : Point) : ConstraintPoint :=
  c + Matrix.toEuclideanLin A.transpose d

/-- Evaluating `linearizedConstraintValue c A d` gives the source affine constraint vector
`c + Aᵀ d`. -/
@[simp] theorem linearizedConstraintValue_apply
    (c : ConstraintPoint) (A : Jacobian) (d : Point) (i : Fin m) :
    linearizedConstraintValue c A d i = c i + (Matrix.toEuclideanLin A.transpose d) i :=
  rfl

namespace StandardPenaltyProblem

private def eqConstraintIndex
    (problem : StandardPenaltyProblem n m) : Fin problem.eqCount → Fin m :=
  fun i ↦ ⟨i.1, Nat.lt_of_lt_of_le i.2 problem.eqCount_le⟩

private def ineqConstraintIndex
    (problem : StandardPenaltyProblem n m) : Fin (m - problem.eqCount) → Fin m :=
  fun i ↦ ⟨problem.eqCount + i.1, by
    have hi := Nat.add_lt_add_left i.2 problem.eqCount
    simpa [Nat.add_sub_of_le problem.eqCount_le, Nat.add_assoc, Nat.add_left_comm] using hi⟩

private def eqConstraintBlock
    (problem : StandardPenaltyProblem n m) (c : ConstraintPoint) : Fin problem.eqCount → ℝ :=
  fun i ↦ c (problem.eqConstraintIndex i)

private def ineqConstraintBlock
    (problem : StandardPenaltyProblem n m) (c : ConstraintPoint) :
    Fin (m - problem.eqCount) → ℝ :=
  fun i ↦ c (problem.ineqConstraintIndex i)

private def eqJacobianBlock
    (problem : StandardPenaltyProblem n m) (A : Jacobian) :
    Matrix (Fin problem.eqCount) (Fin n) ℝ :=
  fun i j ↦ A j (problem.eqConstraintIndex i)

private def ineqJacobianBlock
    (problem : StandardPenaltyProblem n m) (A : Jacobian) :
    Matrix (Fin (m - problem.eqCount)) (Fin n) ℝ :=
  fun i j ↦ A j (problem.ineqConstraintIndex i)

/-- The equality block of a source multiplier `λ`, indexed by the equality constraints of
`problem`. -/
def eqMultiplierBlock
    (problem : StandardPenaltyProblem n m) (lam : Multiplier) : Fin problem.eqCount → ℝ :=
  fun i ↦ lam ⟨i.1, Nat.lt_of_lt_of_le i.2 problem.eqCount_le⟩

/-- The inequality block of a source multiplier `λ`, indexed by the inequality constraints of
`problem`. -/
def ineqMultiplierBlock
    (problem : StandardPenaltyProblem n m) (lam : Multiplier) :
    Fin (m - problem.eqCount) → ℝ :=
  fun i ↦ lam ⟨problem.eqCount + i.1, by
    have hi := Nat.add_lt_add_left i.2 problem.eqCount
    simpa [Nat.add_sub_of_le problem.eqCount_le, Nat.add_assoc, Nat.add_left_comm] using hi⟩

/-- The mixed equality/inequality SQP model at `(c, g, A, B)` viewed through the canonical
Chapter 12 owner `WilsonHanPowellSubproblem`. -/
def wilsonHanPowellSubproblem
    (problem : StandardPenaltyProblem n m)
    (c : ConstraintPoint)
    (g : Point)
    (A : Jacobian)
    (B : MatrixN) :
    WilsonHanPowellSubproblem n problem.eqCount (m - problem.eqCount) where
  B := B
  g := g.ofLp
  Aeq := problem.eqJacobianBlock A
  ceq := problem.eqConstraintBlock c
  Aineq := problem.ineqJacobianBlock A
  cineq := problem.ineqConstraintBlock c

/-- The source multiplier `lam` satisfies the canonical Chapter 12 KKT system for the mixed
SQP subproblem at `(c, g, A, B)` and Euclidean direction `d`, viewed through
`problem.wilsonHanPowellSubproblem c g A B`. This is a thin bridge to the owner
`WilsonHanPowellSubproblem.SatisfiesKKT`. -/
abbrev SatisfiesKKT
    (problem : StandardPenaltyProblem n m)
    (c : ConstraintPoint)
    (g : Point)
    (A : Jacobian)
    (B : MatrixN)
    (d : Point)
    (lam : Multiplier) : Prop :=
  (problem.wilsonHanPowellSubproblem c g A B).SatisfiesKKT
    d.ofLp
    (problem.eqMultiplierBlock lam)
    (problem.ineqMultiplierBlock lam)

/-- Unfolding `problem.SatisfiesKKT c g A B d lam` gives the canonical Chapter 12 KKT predicate
on the transported direction and multiplier blocks. -/
theorem satisfiesKKT_iff
    (problem : StandardPenaltyProblem n m)
    (c : ConstraintPoint)
    (g : Point)
    (A : Jacobian)
    (B : MatrixN)
    (d : Point)
    (lam : Multiplier) :
    problem.SatisfiesKKT c g A B d lam ↔
      (problem.wilsonHanPowellSubproblem c g A B).SatisfiesKKT
        d.ofLp
        (problem.eqMultiplierBlock lam)
        (problem.ineqMultiplierBlock lam) :=
  Iff.rfl

/-- The linearized SQP constraint vector `c + Aᵀ d` is primal feasible exactly when it belongs
to `problem.feasibleConstraintSet`. -/
theorem mem_feasibleConstraintSet_iff_linearizedConstraintValue
    (problem : StandardPenaltyProblem n m) (c : ConstraintPoint) (A : Jacobian) (d : Point) :
    linearizedConstraintValue c A d ∈ problem.feasibleConstraintSet ↔
      (∀ i : Fin m, i.1 < problem.eqCount → linearizedConstraintValue c A d i = 0) ∧
        ∀ i : Fin m, problem.eqCount ≤ i.1 → 0 ≤ linearizedConstraintValue c A d i :=
  problem.mem_feasibleConstraintSet_iff (linearizedConstraintValue c A d)

/-- A direction is feasible for `problem.wilsonHanPowellSubproblem c g A B` exactly when the
source linearized constraint vector `c + Aᵀ d` belongs to `problem.feasibleConstraintSet`. -/
theorem mem_wilsonHanPowellSubproblem_iff_linearizedConstraintValue_mem_feasibleConstraintSet
    (problem : StandardPenaltyProblem n m)
    (c : ConstraintPoint)
    (g : Point)
    (A : Jacobian)
    (B : MatrixN)
    (d : Point) :
    d.ofLp ∈ problem.wilsonHanPowellSubproblem c g A B ↔
      linearizedConstraintValue c A d ∈ problem.feasibleConstraintSet := by
  sorry

/-- If `lam` satisfies the canonical Chapter 12 KKT conditions for the mixed SQP subproblem,
then the source linearized constraint vector `c + Aᵀ d` is primal feasible. -/
theorem linearizedConstraintValue_mem_feasibleConstraintSet_of_satisfiesKKT
    {problem : StandardPenaltyProblem n m}
    {c : ConstraintPoint}
    {g : Point}
    {A : Jacobian}
    {B : MatrixN}
    {d : Point}
    {lam : Multiplier}
    (h : problem.SatisfiesKKT c g A B d lam) :
    linearizedConstraintValue c A d ∈ problem.feasibleConstraintSet := by
  exact
    (mem_wilsonHanPowellSubproblem_iff_linearizedConstraintValue_mem_feasibleConstraintSet
      problem c g A B d).1 h.feasible

/-- The Chapter 12 `L₁` exact penalty attached to `problem` is the exact penalty
`x ↦ problem.objective x + σ * ‖c⁽-⁾[problem] x‖₁`. -/
def l1ExactPenalty
    (problem : StandardPenaltyProblem n m) (σ : ℝ) : Point → ℝ :=
  problem.nonsmoothExactPenalty (fun c ↦ ‖c‖₁) σ

/-- Evaluating `problem.l1ExactPenalty σ` gives the source formula
`f(x) + σ * ‖c⁽-⁾[problem] x‖₁`. -/
@[simp] theorem l1ExactPenalty_apply
    (problem : StandardPenaltyProblem n m) (σ : ℝ) (x : Point) :
    problem.l1ExactPenalty σ x =
      problem.objective x + σ * ‖c⁽-⁾[problem] x‖₁ :=
  rfl

end StandardPenaltyProblem

/-- `IsOneSidedDescentDirection φ x d` means that moving from `x` along `d` with all
sufficiently small positive step sizes strictly decreases `φ`. -/
def IsOneSidedDescentDirection
    (φ : Point → ℝ) (x d : Point) : Prop :=
  ∃ δ > 0, ∀ α ∈ Set.Ioo (0 : ℝ) δ, φ (x + α • d) < φ x

/-- Unfolding `IsOneSidedDescentDirection φ x d` gives the small-positive-step decrease
condition. -/
theorem isOneSidedDescentDirection_iff
    (φ : Point → ℝ) (x d : Point) :
    IsOneSidedDescentDirection φ x d ↔
      ∃ δ > 0, ∀ α ∈ Set.Ioo (0 : ℝ) δ, φ (x + α • d) < φ x :=
  Iff.rfl

/-- Thin scalar-path bridge from the Chapter 12 exact-penalty owner to scalar derivative APIs. -/
abbrev sqpPenaltyPath
    (problem : StandardPenaltyProblem n m)
    (xk dk : Point)
    (σ : ℝ) (α : ℝ) : ℝ :=
  problem.l1ExactPenalty σ (xk + α • dk)

/-- Evaluating `sqpPenaltyPath problem xk dk σ α` gives `P(xk + α • dk, σ)`. -/
@[simp] theorem sqpPenaltyPath_apply
    (problem : StandardPenaltyProblem n m)
    (xk dk : Point)
    (σ : ℝ) (α : ℝ) :
    sqpPenaltyPath problem xk dk σ α =
      problem.l1ExactPenalty σ (xk + α • dk) :=
  rfl

/- Chapter12 Lemma 12.2.1 (1): let `dk` and `lamk` satisfy the source mixed-block
Wilson-Han-Powell KKT conditions for the linearized SQP model at `xk`, viewed through the
canonical owner `problem.wilsonHanPowellSubproblem (problem.constraintMap xk) gk Ak Bk`. If `gk`
and `Ak` are the directional first-order data of the objective and constraints at `xk` along
`dk`, then the one-sided directional derivative of the exact-penalty owner
`problem.l1ExactPenalty σ` at `xk` along `dk` is bounded above by
`- dkᵀ Bk dk - σ * ‖c⁽-⁾(xk)‖₁ + lamkᵀ c(xk)`. -/
/-- Under the KKT and directional-derivative hypotheses of Chapter 12 Lemma 12.2.1, the
canonical one-sided directional derivative of `problem.l1ExactPenalty σ` at `xk` along `dk`
exists. -/
theorem sqpPenalty_hasOneSidedDirectionalDerivAt_of_satisfiesKKT
    (problem : StandardPenaltyProblem n m)
    (σ : ℝ)
    (xk dk gk : Point)
    (Bk : MatrixN)
    (Ak : Jacobian)
    (lamk : Multiplier)
    (h_objective :
      HasLineDerivAt ℝ problem.objective (dotProduct gk dk) xk dk)
    (h_constraint :
      ∀ i : Fin m,
        HasLineDerivAt ℝ (problem.constraint i) ((Matrix.toEuclideanLin Ak.transpose dk) i) xk dk)
    (h_kkt : problem.SatisfiesKKT (problem.constraintMap xk) gk Ak Bk dk lamk) :
    HasOneSidedDirectionalDerivAt
      (problem.l1ExactPenalty σ)
      (oneSidedDirectionalDeriv (problem.l1ExactPenalty σ) xk dk)
      xk
      dk := by
  sorry

/-- Chapter12 Lemma 12.2.1 (1): under the KKT and directional-derivative hypotheses, the
canonical one-sided directional derivative of the exact-penalty owner is bounded above by the
source quadratic and multiplier expression. -/
theorem sqpPenaltyRightDeriv_le_of_satisfiesKKT
    (problem : StandardPenaltyProblem n m)
    (σ : ℝ)
    (xk dk gk : Point)
    (Bk : MatrixN)
    (Ak : Jacobian)
    (lamk : Multiplier)
    (h_objective :
      HasLineDerivAt ℝ problem.objective (dotProduct gk dk) xk dk)
    (h_constraint :
      ∀ i : Fin m,
        HasLineDerivAt ℝ (problem.constraint i) ((Matrix.toEuclideanLin Ak.transpose dk) i) xk dk)
    (h_kkt : problem.SatisfiesKKT (problem.constraintMap xk) gk Ak Bk dk lamk) :
    oneSidedDirectionalDeriv (problem.l1ExactPenalty σ) xk dk ≤
      -dotProduct dk (Matrix.toEuclideanLin Bk dk)
        - σ * (c⁽-⁾[problem] xk).sunYuanL1Norm
        + dotProduct lamk (problem.constraintMap xk) := by
  sorry

/-- Chapter12 Lemma 12.2.1 (2): under the hypotheses of part (1), if `dkᵀ Bk dk > 0` and
`σ ≥ ‖lamk‖∞`, then `dk` is a descent direction of the `L₁` penalty function at `xk`. -/
theorem isOneSidedDescentDirection_sqpL1Penalty_of_satisfiesKKT
    (problem : StandardPenaltyProblem n m)
    (σ : ℝ)
    (xk dk gk : Point)
    (Bk : MatrixN)
    (Ak : Jacobian)
    (lamk : Multiplier)
    (h_objective :
      HasLineDerivAt ℝ problem.objective (dotProduct gk dk) xk dk)
    (h_constraint :
      ∀ i : Fin m,
        HasLineDerivAt ℝ (problem.constraint i) ((Matrix.toEuclideanLin Ak.transpose dk) i) xk dk)
    (h_kkt : problem.SatisfiesKKT (problem.constraintMap xk) gk Ak Bk dk lamk)
    (h_curvature : 0 < dotProduct dk (Matrix.toEuclideanLin Bk dk))
    (hσ : ‖lamk‖∞ ≤ σ) :
    IsOneSidedDescentDirection (problem.l1ExactPenalty σ) xk dk := sorry

#print axioms linearizedConstraintValue
#print axioms StandardPenaltyProblem.eqMultiplierBlock
#print axioms StandardPenaltyProblem.ineqMultiplierBlock
#print axioms StandardPenaltyProblem.wilsonHanPowellSubproblem
#print axioms StandardPenaltyProblem.l1ExactPenalty
#print axioms sqpPenaltyPath

end
