/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_5

open scoped Gradient SmoothConvex

noncomputable section

universe u

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

local notation "p" => normSeminorm ℝ E
local notation "SmoothObjective[" L "]" => { f : E → ℝ // f ∈ 𝓕[L, p]¹¹ }

local instance smoothObjectiveCoeFun {L : NNReal} :
    CoeFun (SmoothObjective[L]) (fun _ ↦ E → ℝ) where
  coe f := f.1

/- Definition 2.8 lies in the chapter's smooth convex first-order black-box domain on a real
finite-dimensional inner-product space.

Sampled owner-style declarations:
* `BlackBoxOptimizationProblemClass` in `Chap01/Definition_1_2_4`, the Chapter 1 owner of the
  model/oracle/stopping-criterion triple;
* `OptimizationOracle.IsLocal` in `Chap01/Definition_1_2_13`, the owner locality predicate for a
  class oracle;
* `SetConstrainedMinimizationProblem.unconstrained` and
  `SetConstrainedMinimizationProblem.IsApproximateMinimizer` in Chapter 1, the canonical owner
  bridge from an unconstrained objective to the `ε`-approximate-solution condition;
* `ConvexC1SeminormSmooth.gradient_lipschitz` in `Theorem_2_5`, the derived gradient-Lipschitz
  view of the objective-side owner `f ∈ 𝓕[L, p]¹¹`.

Best owner abstraction:
* source-facing: the smooth convex first-order black-box problem class at accuracy `ε`;
* core/canonical: `BlackBoxOptimizationProblemClass` with model
  `{f : E → ℝ // f ∈ 𝓕[L, p]¹¹}`;
* bridge/view: the Chapter 1 unconstrained approximate-minimizer predicate and the locality
  theorem for the owner oracle.

Primitive data:
* the ambient real finite-dimensional inner-product space `E`;
* the smoothness constant `L : NNReal`;
* the accuracy threshold `ε : ℝ`.

Derived API:
* the model subtype of objectives in `𝓕[L, p]¹¹`;
* the first-order oracle reply `(f x, ∇ f x)`;
* the stopping criterion expressed through
  `SetConstrainedMinimizationProblem.unconstrained f`;
* the locality bridge for the owner oracle.

Source/core/bridge triage:
* source-facing: `smoothConvexProblemClass L ε`;
* core/canonical: `BlackBoxOptimizationProblemClass` and the smooth-objective subtype
  `{f : E → ℝ // f ∈ 𝓕[L, p]¹¹}`;
* bridge/view:
  `SetConstrainedMinimizationProblem.unconstrained_isApproximateMinimizer_iff_sub_le` and
  `smoothConvexProblemClass_oracle_isLocal`.

Definition 2.8 is therefore refined to the actual Chapter 1 problem-class owner rather than a
list of recalled ingredients. The textbook objective-gap stopping condition is kept as a thin
bridge theorem, not as separate primitive data. -/

section ProblemClass

variable (L : NNReal) (ε : ℝ)

/-- Definition 2.8: the smooth convex first-order black-box class on a real finite-dimensional
inner-product space `E` at smoothness constant `L` and accuracy `ε`. Its model is the subtype of
smooth convex objectives
`f ∈ 𝓕[L, p]¹¹`, its oracle returns the value-gradient reply `(f x, ∇ f x)`, and its stopping
criterion accepts exactly those pairs `(f, x̄)` for which `x̄` is an `ε`-approximate minimizer of
the canonical unconstrained Chapter 1 problem attached to `f`. The textbook `ℝⁿ` statement is the
specialization `E = EuclideanSpace ℝ (Fin n)`. -/
def smoothConvexProblemClass :
    BlackBoxOptimizationProblemClass E (ℝ × E) (SmoothObjective[L] × E) where
  model := SmoothObjective[L]
  oracle := fun f x ↦ (f x, ∇ f x)
  stoppingCriterion := { state | let ⟨f, xBar⟩ := state
    (SetConstrainedMinimizationProblem.unconstrained f).IsApproximateMinimizer ε xBar }

/-- The oracle of `smoothConvexProblemClass L ε` is the canonical first-order reply
`(f, x) ↦ (f x, ∇ f x)`. -/
@[simp] theorem smoothConvexProblemClass_oracle_apply
    (f : SmoothObjective[L]) (x : E) :
    (smoothConvexProblemClass E L ε).oracle f x = (f x, ∇ f x) :=
  rfl

/-- A state belongs to the stopping criterion of `smoothConvexProblemClass L ε` exactly when its
endpoint is an `ε`-approximate minimizer of the unconstrained owner problem attached to the model
objective. -/
@[simp] theorem smoothConvexProblemClass_stops_iff
    (f : SmoothObjective[L]) (xBar : E) :
    (f, xBar) ∈ (smoothConvexProblemClass E L ε).stoppingCriterion ↔
      (SetConstrainedMinimizationProblem.unconstrained f).IsApproximateMinimizer ε xBar :=
  Iff.rfl

end ProblemClass

namespace SetConstrainedMinimizationProblem

variable {X : Type u}

/-- Relative to a chosen global minimizer `x*`, the Chapter 1 unconstrained approximate-minimizer
owner is exactly the textbook objective-gap inequality `f(x̄) - f(x*) ≤ ε`. -/
theorem unconstrained_isApproximateMinimizer_iff_sub_le
    (f : X → ℝ) {xStar xBar : X} (hxStar : IsMinOn f Set.univ xStar) (ε : ℝ) :
    (unconstrained f).IsApproximateMinimizer ε xBar ↔
      f xBar - f xStar ≤ ε := by
  have hoptimalValue :
      (unconstrained f).optimalValue = (f xStar : EReal) := by
    simpa using (unconstrained f).optimalValue_eq_of_isMinOn (by simp) hxStar
  rw [(unconstrained f).isApproximateMinimizer_iff, unconstrained_feasibleSet, hoptimalValue]
  constructor
  · rintro ⟨_, happrox⟩
    refine sub_le_iff_le_add'.mpr ?_
    have happrox' : ((f xBar : ℝ) : EReal) ≤ ((f xStar + ε : ℝ) : EReal) := by
      simpa [EReal.coe_add] using happrox
    exact EReal.coe_le_coe_iff.mp happrox'
  · intro hgap
    have hgap' : f xBar ≤ f xStar + ε :=
      sub_le_iff_le_add'.mp hgap
    refine ⟨by simp, ?_⟩
    have happrox : ((f xBar : ℝ) : EReal) ≤ ((f xStar + ε : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr hgap'
    simpa [EReal.coe_add] using happrox

end SetConstrainedMinimizationProblem

section ProblemClassBridge

variable (L : NNReal) (ε : ℝ)

/-- The stopping rule of `smoothConvexProblemClass L ε` is exactly the textbook objective-gap
criterion once a global minimizer `x*` of the model objective has been fixed. -/
theorem smoothConvexProblemClass_stops_iff_sub_le
    (f : SmoothObjective[L]) {xStar xBar : E} (hxStar : IsMinOn f Set.univ xStar) :
    (f, xBar) ∈ (smoothConvexProblemClass E L ε).stoppingCriterion ↔
      f xBar - f xStar ≤ ε := by
  change (SetConstrainedMinimizationProblem.unconstrained f).IsApproximateMinimizer ε xBar ↔ _
  simpa using
    SetConstrainedMinimizationProblem.unconstrained_isApproximateMinimizer_iff_sub_le f hxStar ε

end ProblemClassBridge

section Locality

variable (L : NNReal) (ε : ℝ)
variable (sameDataNear : (E → ℝ) → (E → ℝ) → E → Prop)

/-- Any locality statement for the raw smooth-objective first-order reply immediately induces the
corresponding locality statement for the owner oracle of `smoothConvexProblemClass L ε`. -/
theorem smoothConvexProblemClass_oracle_isLocal
    (hlocal :
      OptimizationOracle.IsLocal
        (fun (f : SmoothObjective[L]) x ↦ (f x, ∇ f x))
        (fun (f₁ f₂ : SmoothObjective[L]) (x : E) ↦ sameDataNear f₁ f₂ x)) :
    OptimizationOracle.IsLocal
      (smoothConvexProblemClass E L ε).oracle
      (fun (f₁ f₂ : SmoothObjective[L]) (x : E) ↦ sameDataNear f₁ f₂ x) := by
  simpa using hlocal

end Locality

end
