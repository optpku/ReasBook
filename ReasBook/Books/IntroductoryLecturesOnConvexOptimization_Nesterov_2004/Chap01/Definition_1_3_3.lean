/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 1.3.3 lies in the basic domain of box-constrained minimization problems.

Sampled owner-style declarations in the surrounding project:
* `FunctionalConstraintsMinimizationProblem` and `GeneralMinimizationProblem` in
  `Chap01/Definition_1_1_3`, the earlier Chapter 1 ambient owner and its Euclidean specialization;
* `SetConstrainedMinimizationProblem.unconstrained`, the owner-level bridge that packages an
  unconstrained objective on an ambient type as the same minimization-problem owner;
* `SmoothMinimaxProblem.toSetConstrainedMinimizationProblem` in `Chap02/Definition_2_38`, which
  uses the same owner object as the ambient constrained problem attached to a richer source-facing
  structure;
* `LinearEqualityConstrainedConvexProblem` in `Chap03/Definition_3_27`, which extends the same
  owner object and keeps equality-constraint data as extra source-facing structure rather than
  replacing the owner.

Best owner abstraction:
* `SetConstrainedMinimizationProblem X`, whose primitive data are exactly a feasible set and a
  real-valued objective on the ambient space `X`;
* the primary earlier-project bridge is the generic zero-constraint owner
  `FunctionalConstraintsMinimizationProblem X 0`;
* `GeneralMinimizationProblem n 0` is only the `ℝⁿ` specialization of that generic bridge.

Primitive data:
* `feasibleSet : Set X`
* `objective : X → ℝ`

Derived API:
* the coercion to the objective function;
* the generic constrained argmin set `constrainedArgmin Q f`;
* the source-facing specialization `zeroOneBoxProblem n f` for the textbook box `B_n = [0,1]^n`;
* the generic bridge
  `SetConstrainedMinimizationProblem.toFunctionalConstraintsMinimizationProblem`;
* the Euclidean specialization `SetConstrainedMinimizationProblem.toGeneralMinimizationProblem`.

Source/core/bridge triage:
* source-facing: the textbook box problem `min_{x ∈ B_n} f(x)`;
* core/canonical: `SetConstrainedMinimizationProblem` and `constrainedArgmin`;
* bridge/view:
  `SetConstrainedMinimizationProblem.toFunctionalConstraintsMinimizationProblem`, together with
  its Euclidean specialization `SetConstrainedMinimizationProblem.toGeneralMinimizationProblem`
  and the direct source-facing specialization `zeroOneBoxProblem n f`. -/

/-- A real-valued minimization problem with a specified feasible set in an ambient space `X`. -/
structure SetConstrainedMinimizationProblem (X : Type u) where
  /-- The feasible set on which the minimization problem is posed. -/
  feasibleSet : Set X
  /-- The real-valued objective function to be minimized on the feasible set. -/
  objective : X → ℝ

/-- A set-constrained minimization problem can be used as its objective function. -/
instance : CoeFun (SetConstrainedMinimizationProblem X) (fun _ ↦ X → ℝ) where
  coe problem := problem.objective

/-- The constrained optimal set `argmin_{x ∈ Q} f(x)`. -/
abbrev constrainedArgmin
    {X : Type u} {Y : Type v} [Preorder Y] (Q : Set X) (f : X → Y) : Set X :=
  {x | x ∈ Q ∧ IsMinOn f Q x}

namespace ConstrainedArgmin

scoped notation:max "argmin[" Q "]" => constrainedArgmin Q

end ConstrainedArgmin

open scoped ConstrainedArgmin

/-- Membership in `argmin[Q] f` means belonging to `Q` and minimizing `f` on `Q`. -/
-- Proof sketch: unfold the defining set comprehension for `constrainedArgmin`.
@[simp] theorem mem_constrainedArgmin_iff
    {X : Type u} {Y : Type v} [Preorder Y] {Q : Set X} {f : X → Y} {x : X} :
    x ∈ argmin[Q] f ↔ x ∈ Q ∧ IsMinOn f Q x :=
  Iff.rfl

namespace SetConstrainedMinimizationProblem

variable {X : Type u}
variable {Y : Type v}

/-- Evaluating a set-constrained minimization problem returns its objective value. -/
-- Proof sketch: unfold the `CoeFun` instance for `SetConstrainedMinimizationProblem`.
@[simp] theorem coe_apply (problem : SetConstrainedMinimizationProblem X) (x : X) :
  problem x = problem.objective x :=
  rfl

/-- The unconstrained minimization problem with objective `f` on the whole ambient space. -/
def unconstrained (f : X → ℝ) : SetConstrainedMinimizationProblem X where
  feasibleSet := Set.univ
  objective := f

/-- The feasible set of `unconstrained f` is all of the ambient space. -/
@[simp] theorem unconstrained_feasibleSet (f : X → ℝ) :
    (unconstrained f).feasibleSet = Set.univ :=
  rfl

/-- Evaluating `unconstrained f` recovers the ambient objective `f`. -/
@[simp] theorem unconstrained_apply (f : X → ℝ) (x : X) :
    unconstrained f x = f x :=
  rfl

/-- Pulling back a constrained problem along an equivalence gives the same minimization problem on
the source ambient space. -/
def comap (problem : SetConstrainedMinimizationProblem Y) (e : X ≃ Y) :
    SetConstrainedMinimizationProblem X where
  feasibleSet := e ⁻¹' problem.feasibleSet
  objective := problem ∘ e

/-- The feasible set of `problem.comap e` is the preimage of the original feasible set. -/
-- Proof sketch: unfold `SetConstrainedMinimizationProblem.comap`.
@[simp] theorem comap_feasibleSet
    (problem : SetConstrainedMinimizationProblem Y) (e : X ≃ Y) :
    (problem.comap e).feasibleSet = e ⁻¹' problem.feasibleSet :=
  rfl

/-- Evaluating the pullback problem `problem.comap e` applies `problem` after `e`. -/
-- Proof sketch: unfold `SetConstrainedMinimizationProblem.comap`.
@[simp] theorem comap_apply
    (problem : SetConstrainedMinimizationProblem Y) (e : X ≃ Y) (x : X) :
    problem.comap e x = problem (e x) :=
  rfl

/-- A set-constrained minimization problem canonically yields the earlier ambient owner with zero
scalar constraints by taking its feasible set as the basic feasible set. -/
def toFunctionalConstraintsMinimizationProblem
    (problem : SetConstrainedMinimizationProblem X) :
    FunctionalConstraintsMinimizationProblem X 0 where
  basicFeasibleSet := problem.feasibleSet
  objective := fun x ↦ problem x
  constraints := Fin.elim0
  senses := Fin.elim0

/-- The basic feasible set of the zero-constraint bridge is the original feasible set. -/
-- Proof sketch: unfold `toFunctionalConstraintsMinimizationProblem`.
@[simp] theorem toFunctionalConstraintsMinimizationProblem_basicFeasibleSet
    (problem : SetConstrainedMinimizationProblem X) :
    problem.toFunctionalConstraintsMinimizationProblem.basicFeasibleSet = problem.feasibleSet :=
  rfl

/-- The feasible-set coercion of the zero-constraint bridge recovers the original feasible set. -/
-- Proof sketch: extensionality on ambient points, then unfold the zero-constraint feasibility
-- predicate.
@[simp] theorem toFunctionalConstraintsMinimizationProblem_feasibleSet_coe
    (problem : SetConstrainedMinimizationProblem X) :
    ((problem.toFunctionalConstraintsMinimizationProblem.feasibleSet : Set X) =
      problem.feasibleSet) := by
  -- Expand ambient membership in the subtype feasible set and remove the vacuous constraints.
  ext x
  simp [FunctionalConstraintsMinimizationProblem.feasibleSet,
    FunctionalConstraintsMinimizationProblem.IsFeasible]

/-- The objective of the zero-constraint bridge agrees with the original objective. -/
-- Proof sketch: unfold `toFunctionalConstraintsMinimizationProblem`.
@[simp] theorem toFunctionalConstraintsMinimizationProblem_objective_apply
    (problem : SetConstrainedMinimizationProblem X)
    (x : problem.toFunctionalConstraintsMinimizationProblem.basicFeasibleSet) :
    problem.toFunctionalConstraintsMinimizationProblem.objective x = problem x :=
  rfl

/-- Every point of the basic feasible set is feasible for the zero-constraint bridge. -/
-- Proof sketch: unfold the feasible-set predicate and use `Fin.elim0`.
@[simp] theorem toFunctionalConstraintsMinimizationProblem_feasibleSet
    (problem : SetConstrainedMinimizationProblem X) :
    problem.toFunctionalConstraintsMinimizationProblem.feasibleSet = Set.univ := by
  -- Expand feasibility inside the subtype and use that `Fin 0` has no points.
  ext x
  simp [FunctionalConstraintsMinimizationProblem.feasibleSet,
    FunctionalConstraintsMinimizationProblem.IsFeasible]

end SetConstrainedMinimizationProblem

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Definition 1.3.3: the textbook box problem `min_{x ∈ B_n} f(x)` with `B_n = [0,1]^n`. -/
abbrev zeroOneBoxProblem (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n)) where
  feasibleSet := zeroOneBox n
  objective := f

/-- The feasible set of `zeroOneBoxProblem n f` is the textbook box `B_n = [0,1]^n`. -/
-- Proof sketch: unfold `zeroOneBoxProblem`.
@[simp] theorem zeroOneBoxProblem_feasibleSet (f : E → ℝ) :
    (zeroOneBoxProblem n f).feasibleSet = zeroOneBox n :=
  rfl

/-- A point is feasible for `zeroOneBoxProblem n f` exactly when it belongs to the textbook box
`B_n = [0,1]^n`. -/
-- Proof sketch: rewrite the feasible set of `zeroOneBoxProblem n f` using
-- `zeroOneBoxProblem_feasibleSet`.
@[simp] theorem zeroOneBoxProblem_mem_feasibleSet_iff (f : E → ℝ) {x : E} :
    x ∈ (zeroOneBoxProblem n f).feasibleSet ↔ x ∈ zeroOneBox n :=
  Iff.rfl

/-- The constrained argmin set of `zeroOneBoxProblem n f` is exactly the constrained argmin of
`f` on the textbook box `B_n = [0,1]^n`. -/
-- Proof sketch: extensionality on points, then rewrite membership with
-- `mem_constrainedArgmin_iff`, `zeroOneBoxProblem_feasibleSet`, and
-- `zeroOneBoxProblem_isMinOn_iff`.
@[simp] theorem zeroOneBoxProblem_argmin (f : E → ℝ) :
    argmin[(zeroOneBoxProblem n f).feasibleSet] (zeroOneBoxProblem n f) =
      argmin[zeroOneBox n] f := by
  -- Compare the two argmin sets pointwise and simplify both memberships definitionally.
  ext x
  simp

/-- Minimizing `zeroOneBoxProblem n f` on its feasible set is exactly minimizing `f` on the
textbook box `B_n = [0,1]^n`. -/
-- Proof sketch: unfold the feasible set and the objective of `zeroOneBoxProblem`.
@[simp] theorem zeroOneBoxProblem_isMinOn_iff (f : E → ℝ) {x : E} :
    IsMinOn (zeroOneBoxProblem n f) (zeroOneBoxProblem n f).feasibleSet x ↔
      IsMinOn f (zeroOneBox n) x :=
  Iff.rfl

/-- The constrained argmin set of `zeroOneBoxProblem n f` is exactly the set of minimizers of
`f` on the textbook box `B_n = [0,1]^n`. -/
-- Proof sketch: rewrite membership with `mem_constrainedArgmin_iff`, then use
-- `zeroOneBoxProblem_feasibleSet` and `zeroOneBoxProblem_isMinOn_iff`.
@[simp] theorem zeroOneBoxProblem_spec (f : E → ℝ) {x : E} :
    x ∈ argmin[(zeroOneBoxProblem n f).feasibleSet] (zeroOneBoxProblem n f) ↔
      x ∈ zeroOneBox n ∧ IsMinOn f (zeroOneBox n) x := by
  -- Unfold argmin membership and identify the feasible set and objective definitionally.
  simp

/-- A point is feasible for `zeroOneBoxProblem n f` exactly when each coordinate lies in
`[0,1]`. -/
-- Proof sketch: combine `zeroOneBoxProblem_mem_feasibleSet_iff` with `mem_zeroOneBox_iff`.
@[simp] theorem mem_zeroOneBoxProblem_feasibleSet_iff (f : E → ℝ) {x : E} :
    x ∈ (zeroOneBoxProblem n f).feasibleSet ↔
      ∀ i : Fin n, x i ∈ Set.Icc (0 : ℝ) 1 := by
  -- Reduce feasibility to box membership and then to the coordinatewise interval condition.
  simp

namespace SetConstrainedMinimizationProblem

variable {n : ℕ}

/-- The Euclidean specialization of the generic zero-constraint bridge. -/
abbrev toGeneralMinimizationProblem
    (problem : SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n))) :
    GeneralMinimizationProblem n 0 :=
  problem.toFunctionalConstraintsMinimizationProblem

end SetConstrainedMinimizationProblem
