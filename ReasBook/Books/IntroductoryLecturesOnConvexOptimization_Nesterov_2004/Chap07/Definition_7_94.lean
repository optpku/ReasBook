/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 7.94 lies in the constrained minimization / shifted-objective domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for an
  ambient objective together with a feasible set;
- `GeneralMinimizationProblem.objectiveOnAmbient` in `Chap01/Definition_1_1_4_3`, the chapter
  pattern that treats subtype-level data as a bridge to an ambient owner;
- `simplexEuclideanProxFunction` in `Chap06/Definition_6_13`, where the public source-facing
  function on a subtype is refined to the restriction of an ambient owner;
- `StrictlyPositiveObjectiveMinimizationProblem` in `Chap07/Definition_7_85`, the later chapter
  owner for positive objectives on a feasible type.

Best owner abstraction:
- source-facing: the restriction of the shifted objective to a feasible set `Q`;
- core/canonical: the ambient shifted function `shiftedObjective φ x₀ L R : E → ℝ`;
- bridge/view: evaluation of that ambient owner on subtype points `x : Q`.

Primitive data:
- the ambient objective `φ : E → ℝ`;
- the base point `x₀ : E`;
- the constants `L` and `R`.

Derived API:
- the feasible-set restriction `fun x : Q ↦ shiftedObjective φ x₀ L R x`;
- the pointwise formula `φ x - φ x₀ + 2 * L * R`;
- the base-point value `2 * L * R`.

The previous file used the feasible set `Q` as primitive data even though the mathematical content
is just the ambient shifted function and the `Q`-level version is its restriction along
`Subtype.val`. This refinement keeps the source semantics unchanged while moving the owner to the
canonical ambient level. The public owner is now named neutrally, since positivity is not part of
the definition itself and only appears later under additional hypotheses. -/

variable {E : Type u}

/-- Definition 7.94: the shifted objective attached to `φ`, `x₀`, `L`, and `R` is the ambient
function `x ↦ φ(x) - φ(x₀) + 2LR`. For a feasible set `Q`, the source-facing objective on `Q` is
its restriction along `Subtype.val : Q → E`. The surrounding radius bound `‖x - x₀‖ ≤ R` for
`x ∈ Q` motivates the constant shift but is not primitive data of the definition. -/
def shiftedObjective (φ : E → ℝ) (x₀ : E) (L R : ℝ) : E → ℝ :=
  fun x ↦ φ x - φ x₀ + 2 * L * R

/-- Expanding `shiftedObjective φ x₀ L R` recovers the ambient function
`x ↦ φ(x) - φ(x₀) + 2LR`. -/
-- Proof sketch: unfold `shiftedObjective`; the statement is definitional.
theorem shiftedObjective_def
    (φ : E → ℝ) (x₀ : E) (L R : ℝ) :
    shiftedObjective φ x₀ L R = fun x ↦ φ x - φ x₀ + 2 * L * R :=
by
  -- Unfold the owner definition to expose the ambient function formula.
  rfl

/-- Evaluating the shifted objective at `x` gives `φ(x) - φ(x₀) + 2LR`. In particular, the same
formula applies to feasible points `x : Q` by restriction. -/
-- Proof sketch: apply `shiftedObjective_def` and evaluate both sides at `x`.
@[simp] theorem shiftedObjective_apply
    (φ : E → ℝ) (x₀ x : E) (L R : ℝ) :
    shiftedObjective φ x₀ L R x = φ x - φ x₀ + 2 * L * R :=
by
  -- Evaluate the ambient owner at `x`; this is still definitional.
  rfl

/-- At the base point `x₀`, the shifted objective takes the value `2LR`; the same formula
therefore holds for any subtype evaluation of `x₀` along a feasible-set restriction. -/
-- Proof sketch: specialize `shiftedObjective_apply` at `x = x₀` and simplify.
@[simp] theorem shiftedObjective_basePoint
    (φ : E → ℝ) (x₀ : E) (L R : ℝ) :
    shiftedObjective φ x₀ L R x₀ = 2 * L * R :=
by
  -- Specialize the pointwise formula at the base point and cancel `φ x₀ - φ x₀`.
  simp [shiftedObjective_apply]
