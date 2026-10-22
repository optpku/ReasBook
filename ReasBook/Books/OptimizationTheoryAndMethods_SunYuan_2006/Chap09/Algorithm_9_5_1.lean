/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Definition_9_1_extra_1

noncomputable section

section Chapter09Algorithm951

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Multiplier" => EuclideanSpace ℝ (Fin m)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "ConstraintMatrix" => Matrix (Fin m) (Fin n) ℝ

-- Semantic search note: `lean_leansearch` surfaced only unrelated simplex/linear-programming
-- infrastructure, not a ready-made owner for the Sun-Yuan dual method. Nearby Chapter 9
-- precedent therefore favors reusing the canonical inequality-only owner
-- `QuadraticProgram n 0 m` together with explicit inverse-Hessian data, while keeping the
-- algorithm-run structures for the iterate, active-set, and multiplier data.

/-- The dual method of Algorithm 9.5.1 uses the canonical Chapter 9 owner
`QuadraticProgram n 0 m` for an inequality-only quadratic program, together with an explicit
inverse `Ginv` of the Hessian `G`. The inherited inequality block `Aineq x ≥ bineq` is written
rowwise, so the `i`-th constraint is `(Aineq.mulVec x) i ≥ bineq i`. -/
structure DualMethodProblem (n m : ℕ) extends QuadraticProgram n 0 m where
  Ginv : Matrix (Fin n) (Fin n) ℝ
  G_mul_Ginv : G * Ginv = 1
  Ginv_mul_G : Ginv * G = 1

namespace DualMethodProblem

/-- The transpose of the inherited inequality matrix, used in the full-size encoding of
`A A_k^*`. -/
abbrev constraintTranspose (P : DualMethodProblem n m) : Matrix (Fin n) (Fin m) ℝ :=
  P.Aineq.transpose

/-- The `i`-th constraint normal `a_i` of `P`, viewed as a vector in `ℝ^n`. -/
abbrev constraint (P : DualMethodProblem n m) (i : Fin m) : Point :=
  Matrix.toEuclideanLin P.constraintTranspose (EuclideanSpace.single i (1 : ℝ))

/-- The residual vector `r(x)` of the inequality system, with entries
`r_i(x) = b_i - a_iᵀ x`. -/
def residual (P : DualMethodProblem n m) (x : Point) : Multiplier :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm fun i ↦ P.bineq i - (P.Aineq.mulVec x) i

/-- Evaluating `residual` at `i` gives `b_i - a_iᵀ x`. -/
theorem residual_apply (P : DualMethodProblem n m) (x : Point) (i : Fin m) :
    P.residual x i = P.bineq i - (P.Aineq.mulVec x) i :=
  by simp [DualMethodProblem.residual]

/-- Membership in the inherited feasible set is exactly the coordinatewise residual condition
`r_i(x) ≤ 0`. -/
theorem mem_feasibleSet_iff (P : DualMethodProblem n m) (x : Point) :
    x ∈ P.toQuadraticProgram.feasibleSet ↔ ∀ i : Fin m, P.residual x i ≤ 0 := by
  rw [QuadraticProgram.mem_feasibleSet_iff]
  constructor
  · intro hx i
    rw [P.residual_apply]
    exact sub_nonpos.mpr (hx.2 i)
  · intro hx
    refine ⟨?_, fun i ↦ ?_⟩
    · ext i
      exact Fin.elim0 i
    · have hi : P.bineq i - (P.Aineq.mulVec x) i ≤ 0 := by
        simpa [P.residual_apply] using hx i
      exact sub_nonpos.mp hi

end DualMethodProblem

/-- A point `x` has a positive residual for `P` when at least one inequality constraint is
violated strictly. -/
def HasPositiveResidual (P : DualMethodProblem n m) (x : Point) : Prop :=
  ∃ i : Fin m, 0 < P.residual x i

/-- An index `p` is most violated for the residual vector `r` when `r p` is maximal. -/
def IsMostViolatedConstraint (r : Multiplier) (p : Fin m) : Prop :=
  ∀ i : Fin m, r i ≤ r p

/-- Unfolding `IsMostViolatedConstraint` gives the maximal-residual rule used in Step 2. -/
theorem isMostViolatedConstraint_iff (r : Multiplier) (p : Fin m) :
    IsMostViolatedConstraint r p ↔ ∀ i : Fin m, r i ≤ r p :=
  Iff.rfl

/-- The Step-3 set `{j | (y_k)_j > 0, j ∈ S_k}` is nonempty exactly when the full-size dual
search vector `y` has a positive component on the current working set. -/
def HasPositiveWorkingComponent
    (workingSet : Finset (Fin m)) (y : Multiplier) : Prop :=
  ∃ i : Fin m, i ∈ workingSet ∧ 0 < y i

/-- Unfolding `HasPositiveWorkingComponent` gives the source positivity test on `y_k`. -/
theorem hasPositiveWorkingComponent_iff
    (workingSet : Finset (Fin m)) (y : Multiplier) :
    HasPositiveWorkingComponent workingSet y ↔
      ∃ i : Fin m, i ∈ workingSet ∧ 0 < y i :=
  Iff.rfl

/-- The Step-3 leaving-index rule for the dual method: `leaving` lies in the current working set,
its dual-search component is positive, and `α` is the minimum ratio
`multiplier j / y j` over the positive working-set components of `y`. -/
def IsDualMethodLeavingIndex
    (workingSet : Finset (Fin m))
    (multiplier y : Multiplier) (α : ℝ) (leaving : Fin m) : Prop :=
  leaving ∈ workingSet ∧
    0 < y leaving ∧
    α = multiplier leaving / y leaving ∧
    ∀ i : Fin m, i ∈ workingSet → 0 < y i → α ≤ multiplier i / y i

/-- Unfolding `IsDualMethodLeavingIndex` gives the minimum-ratio rule `(9.5.28)`. -/
theorem isDualMethodLeavingIndex_iff
    (workingSet : Finset (Fin m))
    (multiplier y : Multiplier) (α : ℝ) (leaving : Fin m) :
    IsDualMethodLeavingIndex workingSet multiplier y α leaving ↔
      leaving ∈ workingSet ∧
        0 < y leaving ∧
        α = multiplier leaving / y leaving ∧
        ∀ i : Fin m, i ∈ workingSet → 0 < y i → α ≤ multiplier i / y i :=
  Iff.rfl

/-- The dual-method multiplier update `λ + α(-y, 1)` encoded on a full-size multiplier vector:
the temporary entering index `entering` receives the new `+ α` component and every old
component is shifted by `- α y`. -/
def multiplierPivotUpdate
    (multiplier y : Multiplier) (entering : Fin m) (α : ℝ) : Multiplier :=
  multiplier + α • (EuclideanSpace.single entering (1 : ℝ) - y)

/-- Evaluating `multiplierPivotUpdate` at a coordinate gives the full-size version of
`λ + α(-y, 1)`. -/
theorem multiplierPivotUpdate_apply
    (multiplier y : Multiplier) (entering : Fin m) (α : ℝ) (i : Fin m) :
    multiplierPivotUpdate multiplier y entering α i =
      multiplier i + α * (EuclideanSpace.single entering (1 : ℝ) i - y i) :=
  rfl

/-- A full-size multiplier vector is supported on the current working set together with an
optional remembered entering index. Step-2 states use `entering = none`, while continuation
states in the Step-3/4/7 loop use `entering = some p`. -/
def DualMethodMultiplierSupported
    (workingSet : Finset (Fin m))
    (entering : Option (Fin m))
    (multiplier : Multiplier) : Prop :=
  ∀ i : Fin m,
    i ∉ Option.elim entering workingSet (fun p ↦ insert p workingSet) →
      multiplier i = 0

/-- Unfolding `DualMethodMultiplierSupported` gives the full-size support condition for the
temporary multiplier vector `λ̄_k`. -/
theorem dualMethodMultiplierSupported_iff
    (workingSet : Finset (Fin m))
    (entering : Option (Fin m))
    (multiplier : Multiplier) :
    DualMethodMultiplierSupported workingSet entering multiplier ↔
      ∀ i : Fin m,
        i ∉ Option.elim entering workingSet (fun p ↦ insert p workingSet) →
          multiplier i = 0 :=
  Iff.rfl

/-- A dual-method state is terminal exactly when every residual is nonpositive, matching the
Step-2 stopping criterion `r_i ≤ 0` for all `i`. -/
def IsDualMethodTerminalState
    (P : DualMethodProblem n m) (x : Point) : Prop :=
  ∀ i : Fin m, P.residual x i ≤ 0

/-- Unfolding `IsDualMethodTerminalState` gives the source Step-2 stopping criterion. -/
theorem isDualMethodTerminalState_iff
    (P : DualMethodProblem n m) (x : Point) :
    IsDualMethodTerminalState P x ↔ ∀ i : Fin m, P.residual x i ≤ 0 :=
  Iff.rfl

/-- A dual-method state is infeasible exactly in the Step-4 branch where some residual remains
positive, `direction = 0`, and no positive working-set component exists, so the source
`α_k = ∞` branch stops with infeasibility. -/
def IsDualMethodInfeasibleState
    (P : DualMethodProblem n m)
    (x direction : Point)
    (workingSet : Finset (Fin m))
    (dualSearch : Multiplier) : Prop :=
  HasPositiveResidual P x ∧
    direction = 0 ∧
    ¬ HasPositiveWorkingComponent workingSet dualSearch

/-- Unfolding `IsDualMethodInfeasibleState` gives the source Step-4 infeasibility branch. -/
theorem isDualMethodInfeasibleState_iff
    (P : DualMethodProblem n m)
    (x direction : Point)
    (workingSet : Finset (Fin m))
    (dualSearch : Multiplier) :
    IsDualMethodInfeasibleState P x direction workingSet dualSearch ↔
      HasPositiveResidual P x ∧
        direction = 0 ∧
        ¬ HasPositiveWorkingComponent workingSet dualSearch :=
  Iff.rfl

/-- A full-size matrix `Astar` represents the source `A_k^*` for the working set `S` when it
vanishes off `S` and restricts to the identity on the active constraints, so it behaves as the
active-set inverse used in `A_k A_k^*`. -/
def IsDualMethodActiveSetInverse
    (P : DualMethodProblem n m)
    (workingSet : Finset (Fin m))
    (Astar : ConstraintMatrix) : Prop :=
  (∀ i : Fin m, i ∉ workingSet → Astar i = 0) ∧
    ∀ i j : Fin m, i ∈ workingSet → j ∈ workingSet →
      (Astar * P.constraintTranspose) i j = if i = j then 1 else 0

/-- Unfolding `IsDualMethodActiveSetInverse` gives the full-size support and active-set identity
conditions that encode the source matrix `A_k^*`. -/
theorem isDualMethodActiveSetInverse_iff
    (P : DualMethodProblem n m)
    (workingSet : Finset (Fin m))
    (Astar : ConstraintMatrix) :
    IsDualMethodActiveSetInverse P workingSet Astar ↔
      (∀ i : Fin m, i ∉ workingSet → Astar i = 0) ∧
        ∀ i j : Fin m, i ∈ workingSet → j ∈ workingSet →
          (Astar * P.constraintTranspose) i j = if i = j then 1 else 0 :=
  Iff.rfl

/-- A single stage of the dual method stores the current primal iterate `x_k`, objective value
`f_k`, working set `S_k`, temporary multiplier `λ̄_k`, and the matrices `Ĝ_k` and `A_k^*`. -/
structure DualMethodState (n m : ℕ) where
  x : EuclideanSpace ℝ (Fin n)
  objectiveValue : ℝ
  workingSet : Finset (Fin m)
  multiplier : EuclideanSpace ℝ (Fin m)
  hatG : Matrix (Fin n) (Fin n) ℝ
  aStar : Matrix (Fin m) (Fin n) ℝ

/-- A control state for Algorithm 9.5.1 augments the stage data with the currently chosen
entering constraint. `entering = none` means the algorithm is at Step 2 before choosing `p`,
whereas `entering = some p` means the Step-3/4/7 loop continues with that fixed source choice. -/
structure DualMethodControlState (n m : ℕ) where
  stage : DualMethodState n m
  entering : Option (Fin m)

/-- A stage state is consistent with the source data when `Ĝ_k = G⁻¹ (I - A A_k^*)`, the stored
`A_k^*` is a full-size active-set inverse for `S_k`, the stored objective value is the current
quadratic-program objective `f_k = Q(x_k)`, the working-set constraints are active, and every
active-set row of `A` annihilates each dual-method direction `Ĝ_k a_i`. Multiplier support is
tracked separately at the control-state level so continuation states may also carry the temporary
entering component. -/
structure IsDualMethodConsistentState
    (P : DualMethodProblem n m) (s : DualMethodState n m) : Prop where
  hatG_eq :
    s.hatG = P.Ginv * (1 - P.constraintTranspose * s.aStar)
  aStar_spec :
    IsDualMethodActiveSetInverse P s.workingSet s.aStar
  objectiveValue_eq :
    s.objectiveValue = P.toQuadraticProgram s.x
  workingSet_active :
    ∀ i : Fin m, i ∈ s.workingSet → P.residual s.x i = 0
  hatG_workingSet_annihilation :
    ∀ entering i : Fin m, i ∈ s.workingSet →
      (P.Aineq.mulVec (s.hatG.mulVec (P.constraint entering))) i = 0

/-- A control state is consistent with Algorithm 9.5.1 when its stage data is consistent and the
full-size multiplier vector is supported on the current working set together with any remembered
entering index. -/
class IsDualMethodConsistentControlState
    (P : DualMethodProblem n m)
    (s : DualMethodControlState n m) : Prop where
  stage_consistent : IsDualMethodConsistentState P s.stage
  multiplier_support :
    DualMethodMultiplierSupported s.stage.workingSet s.entering s.stage.multiplier

/-- Forgetting the remembered entering index from a consistent control state recovers the
underlying stage consistency. -/
theorem isDualMethodConsistentControlState_toStage
    (P : DualMethodProblem n m)
    (s : DualMethodControlState n m)
    (h : IsDualMethodConsistentControlState P s) :
    IsDualMethodConsistentState P s.stage :=
  h.stage_consistent

/-- The dual method is active at a state exactly when some residual is positive. -/
def DualMethodState.active
    (s : DualMethodState n m) (P : DualMethodProblem n m) : Prop :=
  HasPositiveResidual P s.x

/-- Unfolding `DualMethodState.active` gives the Step-2 condition that some residual is strictly
positive. -/
theorem DualMethodState.active_iff
    (s : DualMethodState n m) (P : DualMethodProblem n m) :
    s.active P ↔ ∃ i : Fin m, 0 < P.residual s.x i :=
  Iff.rfl

/-- The dual method is terminal at a state exactly when every residual is nonpositive. -/
def DualMethodState.terminated
    (s : DualMethodState n m) (P : DualMethodProblem n m) : Prop :=
  IsDualMethodTerminalState P s.x

/-- Unfolding `DualMethodState.terminated` gives the Step-2 stopping test `r_i ≤ 0` for all
`i`. -/
theorem DualMethodState.terminated_iff
    (s : DualMethodState n m) (P : DualMethodProblem n m) :
    s.terminated P ↔ ∀ i : Fin m, P.residual s.x i ≤ 0 :=
  Iff.rfl

/-- If no residual is positive at `s`, then `s` is in the Step-2 terminal branch. -/
theorem DualMethodState.terminated_of_not_active
    (s : DualMethodState n m) (P : DualMethodProblem n m)
    (hInactive : ¬ s.active P) :
    s.terminated P := by
  rw [DualMethodState.terminated_iff, DualMethodState.active_iff] at *
  intro i
  by_contra hi
  exact hInactive ⟨i, lt_of_not_ge hi⟩

/-- A positive residual at `i` certifies that the state is active. -/
theorem DualMethodState.active_of_residual_pos
    (s : DualMethodState n m) (P : DualMethodProblem n m)
    {i : Fin m} (hi : 0 < P.residual s.x i) :
    s.active P :=
  ⟨i, hi⟩

/-- In a consistent state, any constraint with positive residual lies outside the working set,
since working-set constraints satisfy the active-set equation `r_i(x) = 0`. -/
theorem IsDualMethodConsistentState.not_mem_workingSet_of_residual_pos
    {P : DualMethodProblem n m} {s : DualMethodState n m}
    (h : IsDualMethodConsistentState P s)
    {i : Fin m} (hi : 0 < P.residual s.x i) :
    i ∉ s.workingSet := by
  intro hi_mem
  exact hi.ne' (h.workingSet_active i hi_mem)

/-- The Step-1 initialization branch stores the textbook start state
`x₁ = -G⁻¹ g`, `f₁ = (1 / 2) gᵀ x₁`, with empty working set, zero multiplier, and the
initial matrices `Ĝ₁ = G⁻¹`, `A₁^* = 0`. -/
structure DualMethodInitialization
    (P : DualMethodProblem n m) (s : DualMethodState n m) : Prop where
  consistent :
    IsDualMethodConsistentState P s
  x_eq :
    s.x = -P.Ginv.mulVec P.g
  objectiveValue_eq :
    s.objectiveValue = (1 / 2 : ℝ) * dotProduct P.g s.x
  workingSet_eq :
    s.workingSet = ∅
  multiplier_eq :
    s.multiplier = 0
  hatG_eq :
    s.hatG = P.Ginv
  aStar_eq :
    s.aStar = 0

/-- The Step-2 stopping branch records a consistent state with no positive residual. -/
structure DualMethodTerminalStep
    (P : DualMethodProblem n m) (s : DualMethodState n m) : Prop where
  consistent :
    IsDualMethodConsistentState P s
  terminated :
    s.terminated P

/-- The Step-2 continuation branch chooses the most violated inactive constraint `entering` and
records it for the subsequent Step-3/4/7 loop without changing the stage data. The maximality
check belongs to this selection step only; later continuation branches reuse the remembered
source choice without re-running the global residual comparison after intermediate updates. -/
structure DualMethodSelectionStep
    (P : DualMethodProblem n m)
    (s : DualMethodState n m)
    (entering : Fin m) : Prop where
  consistent :
    IsDualMethodConsistentState P s
  mostViolated :
    IsMostViolatedConstraint (P.residual s.x) entering
  entering_residual_pos :
    0 < P.residual s.x entering
  entering_multiplier_eq :
    s.multiplier entering = 0

/-- The Step-4 infeasible stop branch for a fixed entering constraint records the zero direction
and dual-search data that force the `α_k = ∞` termination. -/
inductive DualMethodInfeasibleStep
    (P : DualMethodProblem n m)
    (s : DualMethodState n m)
    (entering : Fin m) : Prop where
  | mk
      (direction : Point)
      (dualSearch : Multiplier)
      (consistent : IsDualMethodConsistentState P s)
      (entering_residual_pos : 0 < P.residual s.x entering)
      (direction_eq : direction = s.hatG.mulVec (P.constraint entering))
      (dualSearch_eq : dualSearch = s.aStar.mulVec (P.constraint entering))
      (infeasible :
        IsDualMethodInfeasibleState
          P s.x direction s.workingSet dualSearch) :
      DualMethodInfeasibleStep P s entering

/-- The `d_k = 0` pivot branch removes a blocking working-set index while leaving the primal
iterate fixed. -/
inductive DualMethodDropStep
    (P : DualMethodProblem n m)
    (s t : DualMethodState n m)
    (entering : Fin m) : Prop where
  | mk
      (leaving : Fin m)
      (α : ℝ)
      (direction : Point)
      (dualSearch : Multiplier)
      (source_consistent : IsDualMethodConsistentState P s)
      (target_consistent : IsDualMethodConsistentState P t)
      (entering_residual_pos : 0 < P.residual s.x entering)
      (direction_eq : direction = s.hatG.mulVec (P.constraint entering))
      (dualSearch_eq : dualSearch = s.aStar.mulVec (P.constraint entering))
      (direction_zero : direction = 0)
      (leaving_spec :
        IsDualMethodLeavingIndex
          s.workingSet s.multiplier dualSearch α leaving)
      (x_eq : t.x = s.x)
      (objectiveValue_eq : t.objectiveValue = s.objectiveValue)
      (workingSet_eq : t.workingSet = s.workingSet.erase leaving)
      (multiplier_eq :
        t.multiplier =
          multiplierPivotUpdate s.multiplier dualSearch entering α) :
      DualMethodDropStep P s t entering

/-- The short-step branch takes `stepSize = min α hatAlpha` with `stepSize < hatAlpha`, so the
blocking working-set index leaves before the new constraint becomes active. -/
inductive DualMethodShortStep
    (P : DualMethodProblem n m)
    (s t : DualMethodState n m)
    (entering : Fin m) : Prop where
  | mk
      (leaving : Fin m)
      (α hatAlpha stepSize : ℝ)
      (direction : Point)
      (dualSearch : Multiplier)
      (source_consistent : IsDualMethodConsistentState P s)
      (target_consistent : IsDualMethodConsistentState P t)
      (entering_residual_pos : 0 < P.residual s.x entering)
      (direction_eq : direction = s.hatG.mulVec (P.constraint entering))
      (dualSearch_eq : dualSearch = s.aStar.mulVec (P.constraint entering))
      (direction_ne_zero : direction ≠ 0)
      (leaving_spec :
        IsDualMethodLeavingIndex
          s.workingSet s.multiplier dualSearch α leaving)
      (hatAlpha_eq :
        hatAlpha =
          -(P.residual s.x entering) / (P.Aineq.mulVec direction) entering)
      (stepSize_eq : stepSize = min α hatAlpha)
      (stepSize_lt_hatAlpha : stepSize < hatAlpha)
      (x_eq : t.x = s.x + stepSize • direction)
      (objectiveValue_eq :
        t.objectiveValue =
          s.objectiveValue +
            stepSize * (P.Aineq.mulVec direction) entering *
              ((1 / 2 : ℝ) * stepSize + s.multiplier entering))
      (multiplier_eq :
        t.multiplier =
          multiplierPivotUpdate s.multiplier dualSearch entering stepSize)
      (workingSet_eq : t.workingSet = s.workingSet.erase leaving) :
      DualMethodShortStep P s t entering

/-- The full-step branch reaches `hatAlpha` and adds the entering constraint because either no
positive working-set dual component exists or every blocking ratio is at least `hatAlpha`. -/
inductive DualMethodFullStep
    (P : DualMethodProblem n m)
    (s t : DualMethodState n m)
    (entering : Fin m) : Prop where
  | mk
      (hatAlpha : ℝ)
      (direction : Point)
      (dualSearch : Multiplier)
      (source_consistent : IsDualMethodConsistentState P s)
      (target_consistent : IsDualMethodConsistentState P t)
      (entering_residual_pos : 0 < P.residual s.x entering)
      (direction_eq : direction = s.hatG.mulVec (P.constraint entering))
      (dualSearch_eq : dualSearch = s.aStar.mulVec (P.constraint entering))
      (direction_ne_zero : direction ≠ 0)
      (hatAlpha_eq :
        hatAlpha =
          -(P.residual s.x entering) / (P.Aineq.mulVec direction) entering)
      (blocking :
        (¬ HasPositiveWorkingComponent s.workingSet dualSearch) ∨
          ∃ α : ℝ, ∃ leaving : Fin m,
            IsDualMethodLeavingIndex
                s.workingSet s.multiplier dualSearch α leaving ∧
              hatAlpha ≤ α)
      (x_eq : t.x = s.x + hatAlpha • direction)
      (objectiveValue_eq :
        t.objectiveValue =
          s.objectiveValue +
            hatAlpha * (P.Aineq.mulVec direction) entering *
              ((1 / 2 : ℝ) * hatAlpha + s.multiplier entering))
      (multiplier_eq :
        t.multiplier =
          multiplierPivotUpdate s.multiplier dualSearch entering hatAlpha)
      (workingSet_eq : t.workingSet = insert entering s.workingSet) :
      DualMethodFullStep P s t entering

/-- A control state is an initialization target when it carries no remembered entering
constraint and its stage satisfies the Step-1 initialization conditions. -/
structure DualMethodInitControlStep
    (P : DualMethodProblem n m)
    (t : DualMethodControlState n m) : Prop where
  consistent : IsDualMethodConsistentControlState P t
  entering_none : t.entering = none
  initialization : DualMethodInitialization P t.stage

/-- A control state is a terminal stop when it is a Step-2 state with no remembered entering
constraint and its stage satisfies the terminal branch conditions. -/
structure DualMethodStopControlStep
    (P : DualMethodProblem n m)
    (s : DualMethodControlState n m) : Prop where
  consistent : IsDualMethodConsistentControlState P s
  entering_none : s.entering = none
  terminal : DualMethodTerminalStep P s.stage

/-- A control state is an infeasible stop when it remembers an entering constraint whose stage
data satisfies the Step-4 infeasibility branch. -/
inductive DualMethodInfeasibleControlStep
    (P : DualMethodProblem n m)
    (s : DualMethodControlState n m) : Prop where
  | mk
      (entering : Fin m)
      (consistent : IsDualMethodConsistentControlState P s)
      (entering_eq : s.entering = some entering)
      (infeasible : DualMethodInfeasibleStep P s.stage entering) :
      DualMethodInfeasibleControlStep P s

/-- A control-state transition is a Step-2 selection when it records a newly chosen entering
constraint while leaving the stage data unchanged. -/
inductive DualMethodSelectControlStep
    (P : DualMethodProblem n m)
    (s t : DualMethodControlState n m) : Prop where
  | mk
      (entering : Fin m)
      (source_consistent : IsDualMethodConsistentControlState P s)
      (target_consistent : IsDualMethodConsistentControlState P t)
      (source_entering_none : s.entering = none)
      (target_entering_eq : t.entering = some entering)
      (stage_eq : t.stage = s.stage)
      (selection : DualMethodSelectionStep P s.stage entering) :
      DualMethodSelectControlStep P s t

/-- A control-state transition is a Step-4/7 drop step when it keeps the remembered entering
constraint and updates only the stage data by dropping a blocking working-set index. -/
inductive DualMethodDropControlStep
    (P : DualMethodProblem n m)
    (s t : DualMethodControlState n m) : Prop where
  | mk
      (entering : Fin m)
      (source_consistent : IsDualMethodConsistentControlState P s)
      (target_consistent : IsDualMethodConsistentControlState P t)
      (source_entering_eq : s.entering = some entering)
      (target_entering_eq : t.entering = some entering)
      (drop : DualMethodDropStep P s.stage t.stage entering) :
      DualMethodDropControlStep P s t

/-- A control-state transition is a Step-5/7 short step when it keeps the remembered entering
constraint and performs the short-step stage update. -/
inductive DualMethodShortControlStep
    (P : DualMethodProblem n m)
    (s t : DualMethodControlState n m) : Prop where
  | mk
      (entering : Fin m)
      (source_consistent : IsDualMethodConsistentControlState P s)
      (target_consistent : IsDualMethodConsistentControlState P t)
      (source_entering_eq : s.entering = some entering)
      (target_entering_eq : t.entering = some entering)
      (short : DualMethodShortStep P s.stage t.stage entering) :
      DualMethodShortControlStep P s t

/-- A control-state transition is a Step-5/6 full step when it forgets the remembered entering
constraint after taking the full-step stage update back to Step 2. -/
inductive DualMethodFullControlStep
    (P : DualMethodProblem n m)
    (s t : DualMethodControlState n m) : Prop where
  | mk
      (entering : Fin m)
      (source_consistent : IsDualMethodConsistentControlState P s)
      (target_consistent : IsDualMethodConsistentControlState P t)
      (source_entering_eq : s.entering = some entering)
      (target_entering_none : t.entering = none)
      (full : DualMethodFullStep P s.stage t.stage entering) :
      DualMethodFullControlStep P s t

/-- Chapter09 Algorithm 9.5.1: the dual method as a one-step transition relation on control
states. `entering = none` records the Step-2 state before an entering constraint is chosen, while
`entering = some p` records that the Step-3/4/7 loop continues with the fixed source choice `p`.
`IsDualMethodStep P none (some s)` is the Step-1 initialization into Step 2. A Step-2 state may
either stop, or choose an entering constraint without changing the stage data. A continuation
state with remembered `p` may either stop infeasibly, continue the Step-4/7 drop or Step-5/7
short-step loop with the same `p`, or take the Step-5/6 full step and return to Step 2 at the
next stage. -/
def IsDualMethodStep
    (P : DualMethodProblem n m)
    (source target : Option (DualMethodControlState n m)) : Prop :=
  match source, target with
  | none, some s =>
      DualMethodInitControlStep P s
  | some s, none =>
      DualMethodStopControlStep P s ∨
        DualMethodInfeasibleControlStep P s
  | some s, some t =>
      DualMethodSelectControlStep P s t ∨
        DualMethodDropControlStep P s t ∨
        DualMethodShortControlStep P s t ∨
        DualMethodFullControlStep P s t
  | none, none => False

/-- Characterizing `IsDualMethodStep` gives the initialization, stopping, and update branches of
Algorithm 9.5.1 case by case on the source and target control states. -/
theorem isDualMethodStep_iff
    (P : DualMethodProblem n m)
    (source target : Option (DualMethodControlState n m)) :
    IsDualMethodStep P source target ↔
      match source, target with
      | none, some s =>
          IsDualMethodConsistentControlState P s ∧
            s.entering = none ∧
            DualMethodInitialization P s.stage
      | some s, none =>
          (IsDualMethodConsistentControlState P s ∧
            s.entering = none ∧
            DualMethodTerminalStep P s.stage) ∨
            ∃ entering : Fin m,
              IsDualMethodConsistentControlState P s ∧
                s.entering = some entering ∧
                DualMethodInfeasibleStep P s.stage entering
      | some s, some t =>
          (∃ entering : Fin m,
              IsDualMethodConsistentControlState P s ∧
                IsDualMethodConsistentControlState P t ∧
                s.entering = none ∧
                t.entering = some entering ∧
                t.stage = s.stage ∧
                DualMethodSelectionStep P s.stage entering) ∨
            (∃ entering : Fin m,
              IsDualMethodConsistentControlState P s ∧
                IsDualMethodConsistentControlState P t ∧
                s.entering = some entering ∧
                t.entering = some entering ∧
                DualMethodDropStep P s.stage t.stage entering) ∨
            (∃ entering : Fin m,
              IsDualMethodConsistentControlState P s ∧
                IsDualMethodConsistentControlState P t ∧
                s.entering = some entering ∧
                t.entering = some entering ∧
                DualMethodShortStep P s.stage t.stage entering) ∨
            ∃ entering : Fin m,
              IsDualMethodConsistentControlState P s ∧
                IsDualMethodConsistentControlState P t ∧
                s.entering = some entering ∧
                t.entering = none ∧
                DualMethodFullStep P s.stage t.stage entering
      | none, none => False := by
  cases source with
  | none =>
      cases target with
      | none =>
          exact Iff.rfl
      | some t =>
          constructor
          · intro h
            exact ⟨h.consistent, h.entering_none, h.initialization⟩
          · rintro ⟨hConsistent, hEntering, hInitialization⟩
            exact ⟨hConsistent, hEntering, hInitialization⟩
  | some s =>
      cases target with
      | none =>
          constructor
          · intro h
            rcases h with hStop | hInfeasible
            · exact Or.inl ⟨hStop.consistent, hStop.entering_none, hStop.terminal⟩
            · rcases hInfeasible with ⟨entering, hConsistent, hEntering, hStep⟩
              exact Or.inr ⟨entering, hConsistent, hEntering, hStep⟩
          · intro h
            rcases h with hStop | hInfeasible
            · rcases hStop with ⟨hConsistent, hEntering, hTerminal⟩
              exact Or.inl ⟨hConsistent, hEntering, hTerminal⟩
            · rcases hInfeasible with ⟨entering, hConsistent, hEntering, hStep⟩
              exact Or.inr ⟨entering, hConsistent, hEntering, hStep⟩
      | some t =>
          constructor
          · intro h
            rcases h with hSelect | hDrop | hShort | hFull
            · rcases hSelect with
                ⟨entering, hSource, hTarget, hSourceEntering, hTargetEntering, hStage, hStep⟩
              exact Or.inl
                ⟨entering, hSource, hTarget, hSourceEntering, hTargetEntering, hStage, hStep⟩
            · rcases hDrop with
                ⟨entering, hSource, hTarget, hSourceEntering, hTargetEntering, hStep⟩
              exact Or.inr <| Or.inl
                ⟨entering, hSource, hTarget, hSourceEntering, hTargetEntering, hStep⟩
            · rcases hShort with
                ⟨entering, hSource, hTarget, hSourceEntering, hTargetEntering, hStep⟩
              exact Or.inr <| Or.inr <| Or.inl
                ⟨entering, hSource, hTarget, hSourceEntering, hTargetEntering, hStep⟩
            · rcases hFull with
                ⟨entering, hSource, hTarget, hSourceEntering, hTargetEntering, hStep⟩
              exact Or.inr <| Or.inr <| Or.inr
                ⟨entering, hSource, hTarget, hSourceEntering, hTargetEntering, hStep⟩
          · intro h
            rcases h with hSelect | hRest
            · rcases hSelect with
                ⟨entering, hSource, hTarget, hSourceEntering, hTargetEntering, hStage, hStep⟩
              exact Or.inl
                ⟨entering, hSource, hTarget, hSourceEntering, hTargetEntering, hStage, hStep⟩
            · rcases hRest with hDrop | hRest
              · rcases hDrop with
                  ⟨entering, hSource, hTarget, hSourceEntering, hTargetEntering, hStep⟩
                exact Or.inr <| Or.inl
                  ⟨entering, hSource, hTarget, hSourceEntering, hTargetEntering, hStep⟩
              · rcases hRest with hShort | hFull
                · rcases hShort with
                    ⟨entering, hSource, hTarget, hSourceEntering, hTargetEntering, hStep⟩
                  exact Or.inr <| Or.inr <| Or.inl
                    ⟨entering, hSource, hTarget, hSourceEntering, hTargetEntering, hStep⟩
                · rcases hFull with
                    ⟨entering, hSource, hTarget, hSourceEntering, hTargetEntering, hStep⟩
                  exact Or.inr <| Or.inr <| Or.inr
                    ⟨entering, hSource, hTarget, hSourceEntering, hTargetEntering, hStep⟩

end Chapter09Algorithm951
