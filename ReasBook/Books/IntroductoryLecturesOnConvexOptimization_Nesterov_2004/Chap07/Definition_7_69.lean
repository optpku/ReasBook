/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_18

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u v

variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
variable {ι : Type v} [Fintype ι] [Nonempty ι]

/- Definition 7.69 lies in the finite convex-minimax / simplex-duality domain.

Mandatory domain-style sampling before refinement:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with an ambient real-valued objective;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  constrained value owner attached to that ambient problem;
- `maxTypeObjective` and `maxTypeObjective_apply` in `Chap02/Lemma_2_18`, the project owner and
  evaluation bridge for finite maxima of nonempty families;
- mathlib `StdSimplex`, the canonical owner for simplex weight data;
- `exists_stdSimplex_minimax_linearization_of_bounded_familyMaximumSublevelSets` in
  `Chap03/Corollary_3_1_2_1`, the chapter pattern for expressing finite-max linearization directly
  through `StdSimplex`.

Best owner abstraction:
- source-facing: `ConvexMinimaxProblem E ι`;
- core/canonical: `SetConstrainedMinimizationProblem E`, its owner value `optimalValue`,
  `maxTypeObjective`, and `StdSimplex ℝ ι`;
- bridge/view: `toSetConstrainedMinimizationProblem`, the weighted objective, and the dual-value
  surfaces below.

Primitive data:
- the feasible set `S ⊆ E`, with its nonemptiness, closedness, and convexity;
- the nonnegative component family `fᵢ : E → ℝ≥0`;
- convexity of each component on `S`.

Derived API:
- the pointwise-maximum objective `maxTypeObjective (fun i x ↦ (fᵢ x : ℝ))`;
- the Chapter 1 constrained-minimization owner for `S` and that objective;
- the minimax value, simplex-weighted objectives, weighted constrained minima, dual function, and
  dual value.

Source/core/bridge triage:
- source-facing: `ConvexMinimaxProblem` and the minimax / dual-value declarations below;
- core/canonical: `SetConstrainedMinimizationProblem`, `optimalValue`, `maxTypeObjective`, and
  `StdSimplex`;
- bridge/view: `toSetConstrainedMinimizationProblem`.

The previous file duplicated the finite-max owner by rebuilding the objective on the feasible-set
subtype and also fixed the index family to `Fin m`, although only a nonempty finite family is
mathematically used. This refinement keeps the source-facing problem structure, but moves the
ambient problem layer onto `SetConstrainedMinimizationProblem`, reuses `maxTypeObjective` for the
finite maximum, expresses the dual weights directly through `StdSimplex`, and keeps the value
layer on the Chapter 1 `optimalValue` owner instead of rebuilding raw `ℝ` infima.
-/

/-- Definition 7.69: a convex minimax problem consists of a nonempty closed convex feasible set
`S ⊆ E` in a real topological module together with a nonempty finite family of nonnegative
component functions `fᵢ : E → ℝ≥0` whose restrictions to `S` are convex. Its objective is the
pointwise maximum of the component family, minimized over `S`, and its dual side is obtained from
simplex-weighted convex combinations of the same family. -/
structure ConvexMinimaxProblem (E : Type u) (ι : Type v)
    [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] [Fintype ι] [Nonempty ι] where
  /-- The feasible set `S`. -/
  feasibleSet : Set E
  /-- The feasible set is nonempty. -/
  feasibleSet_nonempty : feasibleSet.Nonempty
  /-- The feasible set is closed. -/
  feasibleSet_isClosed : IsClosed feasibleSet
  /-- The feasible set is convex. -/
  feasibleSet_convex : Convex ℝ feasibleSet
  /-- The nonnegative component family `fᵢ : E → ℝ≥0`. -/
  componentFun : ι → E → NNReal
  /-- Each component function is convex on the feasible set `S`. -/
  componentFun_convex (i : ι) :
    ConvexOn ℝ feasibleSet (fun x ↦ (componentFun i x : ℝ))

namespace ConvexMinimaxProblem

/-- The pointwise-maximum objective `x ↦ maxᵢ fᵢ(x)` attached to the component family. -/
def objective (problem : ConvexMinimaxProblem E ι) : E → ℝ :=
  maxTypeObjective fun i x ↦ (problem.componentFun i x : ℝ)

/-- The canonical Chapter 1 constrained-minimization owner attached to a convex minimax problem. -/
def toSetConstrainedMinimizationProblem
    (problem : ConvexMinimaxProblem E ι) : SetConstrainedMinimizationProblem E where
  feasibleSet := problem.feasibleSet
  objective := problem.objective

@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : ConvexMinimaxProblem E ι) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : ConvexMinimaxProblem E ι) (x : E) :
    problem.toSetConstrainedMinimizationProblem x = problem.objective x :=
  rfl

/-- A convex minimax problem can be used as its ambient objective function. -/
instance : CoeFun (ConvexMinimaxProblem E ι) (fun _ ↦ E → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

@[simp] theorem coe_apply
    (problem : ConvexMinimaxProblem E ι) (x : E) :
    problem x = problem.objective x :=
  rfl

/-- Evaluating the objective recovers the finite maximum of the component values. -/
@[simp] theorem objective_apply
    (problem : ConvexMinimaxProblem E ι) (x : E) :
    problem.objective x =
      Finset.univ.sup' Finset.univ_nonempty (fun i : ι ↦ (problem.componentFun i x : ℝ)) := by
  simpa [objective] using
    (maxTypeObjective_apply (fun i x ↦ (problem.componentFun i x : ℝ)) x)

/-- The minimax value `ψ⋆ = min_{x ∈ S} maxᵢ fᵢ(x)`, formalized through the canonical Chapter 1
constrained optimal-value owner. -/
def minimaxValue (problem : ConvexMinimaxProblem E ι) : EReal :=
  problem.toSetConstrainedMinimizationProblem.optimalValue

/-- Expanding `minimaxValue` gives the extended-real infimum of the objective over the feasible
set. -/
theorem minimaxValue_eq_sInf_image
    (problem : ConvexMinimaxProblem E ι) :
    problem.minimaxValue =
      sInf ((fun x ↦ (problem x : EReal)) '' problem.feasibleSet) := by
  simpa [minimaxValue] using
    problem.toSetConstrainedMinimizationProblem.optimalValue_eq_sInf_image

/-- For simplex weights `y`, the weighted objective is `x ↦ ∑ᵢ yᵢ fᵢ(x)`. -/
def weightedObjective (problem : ConvexMinimaxProblem E ι)
    (y : StdSimplex ℝ ι) : E → ℝ :=
  fun x ↦ ∑ i : ι, y.weights i * (problem.componentFun i x : ℝ)

/-- Evaluating `weightedObjective` recovers the weighted component sum. -/
@[simp] theorem weightedObjective_apply
    (problem : ConvexMinimaxProblem E ι) (y : StdSimplex ℝ ι) (x : E) :
    problem.weightedObjective y x =
      ∑ i : ι, y.weights i * (problem.componentFun i x : ℝ) := by
  rfl

/-- The simplex-parameterized dual function
`ψ(y) = min_{x ∈ S} ∑ᵢ yᵢ fᵢ(x)`, formalized through the Chapter 1 constrained optimal-value owner
for the weighted objective. -/
def dualFunction (problem : ConvexMinimaxProblem E ι) : StdSimplex ℝ ι → EReal :=
  fun y ↦ (SetConstrainedMinimizationProblem.mk
    problem.feasibleSet (problem.weightedObjective y)).optimalValue

/-- Evaluating `dualFunction` at simplex weights gives the infimum of the corresponding weighted
objective over the feasible set in `EReal`. -/
theorem dualFunction_apply
    (problem : ConvexMinimaxProblem E ι) (y : StdSimplex ℝ ι) :
    problem.dualFunction y =
      sInf ((fun x ↦ (problem.weightedObjective y x : EReal)) '' problem.feasibleSet) := by
  simpa [dualFunction] using
    (SetConstrainedMinimizationProblem.mk
      problem.feasibleSet (problem.weightedObjective y)).optimalValue_eq_sInf_image

/-- If a simplex-weighted objective attains its minimum at `x`, then `dualFunction` equals that
attained value. -/
theorem dualFunction_eq_of_isMinOn
    (problem : ConvexMinimaxProblem E ι) (y : StdSimplex ℝ ι) {x : E}
    (hx : x ∈ problem.feasibleSet)
    (hmin : IsMinOn (problem.weightedObjective y) problem.feasibleSet x) :
    problem.dualFunction y = (problem.weightedObjective y x : EReal) := by
  simpa [dualFunction] using
    (SetConstrainedMinimizationProblem.mk
      problem.feasibleSet (problem.weightedObjective y)).optimalValue_eq_of_isMinOn hx hmin

/-- The dual value `max_y ψ(y)` over the standard simplex, formalized as the supremum of the dual
function on that simplex. -/
def dualValue (problem : ConvexMinimaxProblem E ι) : EReal :=
  sSup (Set.range problem.dualFunction)

/-- Expanding `dualValue` gives the supremum of `ψ(y)` over simplex weights. -/
theorem dualValue_eq_sSup_range
    (problem : ConvexMinimaxProblem E ι) :
    problem.dualValue = sSup (Set.range problem.dualFunction) := by
  rfl

/-- The dual function is well-defined when each simplex-weighted objective attains its minimum on
the feasible set. This is an attainment condition only; the actual dual-form equality needs
additional minimax hypotheses such as the boundedness or compactness assumptions used earlier in
the chapter. -/
def dualFunctionWellDefined (problem : ConvexMinimaxProblem E ι) : Prop :=
  ∀ y : StdSimplex ℝ ι, ∃ x ∈ problem.feasibleSet,
    IsMinOn (problem.weightedObjective y) problem.feasibleSet x

/-- The convex minimax problem admits the textbook dual form when its minimax value equals the
supremum of the dual function over the standard simplex. -/
def hasDualForm (problem : ConvexMinimaxProblem E ι) : Prop :=
  problem.minimaxValue = problem.dualValue

end ConvexMinimaxProblem

end
