/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_56

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {P : Type u} {S : Type v}

/- Definition 7.59 lies in the Chapter 7 saddle-representation / maximization-value domain.

Sampled owner-style declarations:
- `maximalValueOn` in `Chap07/Definition_7_56`, the chapter maximization owner implemented through
  the canonical Chapter 1 minimization owner;
- `maximalValueOn_eq_sSup_image` in `Chap07/Definition_7_56`, the expansion theorem identifying
  that owner with the supremum of feasible objective values;
- `StructuredObjectiveModel.adjointObjective_eq_saddleFunction_of_isMinOn` in
  `Chap06/Text_6_1_2_Adjoint_Problem_Tractability_Caveat`, the nearby attained-inner-minimum
  bridge stated from canonical minimizer data rather than a bare infimum formula;
- `IsLeast.csInf_eq` in mathlib, the canonical bridge from an attained least value to the
  corresponding `sInf` identity.

Best owner abstraction:
- source-facing: `SaddlePointRepresentation P S`;
- core/canonical for the inner minimum: `IsLeast (Set.range (Ψ x)) (f x)`;
- core/canonical for the outer value: `maximalValueOn Set.univ f`;
- bridge/view: the derived `sInf` equality and the outer `sSup`-range expansion theorem.

Primitive data:
- the represented objective `f : P → ℝ`;
- the saddle function `Ψ : P → S → ℝ`;
- the pointwise least-value witness `IsLeast (Set.range (Ψ x)) (f x)`.

Derived API:
- the coercion to the represented objective;
- the derived equality `f x = sInf (Set.range (Ψ x))`;
- the chapter-canonical maximization value of that objective on `P`.

Source/core/bridge triage:
- source-facing: `SaddlePointRepresentation`;
- core/canonical for the inner minimum: `IsLeast`;
- core/canonical for the outer value: `maximalValueOn`;
- bridge/view: `objective_eq` and `optimalValue_eq_sSup_range`.

The representation itself is source-facing and should stay explicit. The inner textbook minimum
must be stored as attained least-value data, not as a raw real `sInf`, while the outer value
should keep reusing the Chapter 7 owner `maximalValueOn` instead of restating a raw supremum.
-/

/-- Definition 7.59: [Saddle-point representation] a concave maximization problem on a feasible
set `P` admits a saddle-point representation if it is given by an objective `f : P → ℝ` together
with a function `Ψ : P → S → ℝ` whose partial minimum over `S` recovers `f(x)` for every
`x ∈ P`. -/
structure SaddlePointRepresentation (P : Type u) (S : Type v) where
  /-- The objective function `f : P → ℝ` of the maximization problem. -/
  objective : P → ℝ
  /-- The saddle function `Ψ : P → S → ℝ` whose minimum over `S` recovers the objective. -/
  saddleFunction : P → S → ℝ
  /-- For each feasible point `x ∈ P`, the objective value is a least element of the saddle slice
  `Ψ(x, ·)`. This is the faithful owner form of the textbook identity
  `f(x) = \min_{w ∈ S} Ψ(x, w)`. -/
  objective_isLeast (x : P) : IsLeast (Set.range (saddleFunction x)) (objective x)

namespace SaddlePointRepresentation

/-- A saddle-point representation can be used as its objective function. -/
instance : CoeFun (SaddlePointRepresentation P S) (fun _ ↦ P → ℝ) where
  coe representation := representation.objective

/-- Evaluating a saddle-point representation as a function means evaluating its represented
objective. -/
@[simp] theorem coe_apply (representation : SaddlePointRepresentation P S) (x : P) :
    representation x = representation.objective x :=
  rfl

/-- The pointwise least-value witness recovers the textbook minimum identity
`f(x) = \inf_{w ∈ S} Ψ(x, w)` as a derived `sInf` equality. -/
theorem objective_eq (representation : SaddlePointRepresentation P S) (x : P) :
    representation.objective x = sInf (Set.range (representation.saddleFunction x)) :=
  (representation.objective_isLeast x).csInf_eq.symm

/-- The optimal value `f⋆` of a saddle-point representation is the chapter-canonical maximal
value of its represented objective on the feasible type `P`, viewed in `EReal` so empty or
unbounded objective-value sets are represented faithfully. -/
def optimalValue (representation : SaddlePointRepresentation P S) : EReal :=
  maximalValueOn Set.univ representation

-- Proof sketch: unfold `optimalValue`; then use `maximalValueOn_eq_sSup_image` on `Set.univ`, and
-- simplify the image of the universal feasible set to the range of the objective.
/-- Expanding `optimalValue` gives the supremum of the objective values attained on `P`, viewed in
`EReal`. -/
theorem optimalValue_eq_sSup_range (representation : SaddlePointRepresentation P S) :
    representation.optimalValue = sSup (Set.range fun x : P ↦ (representation x : EReal)) := by
  rw [optimalValue, maximalValueOn_eq_sSup_image]
  simp

end SaddlePointRepresentation

end

end
