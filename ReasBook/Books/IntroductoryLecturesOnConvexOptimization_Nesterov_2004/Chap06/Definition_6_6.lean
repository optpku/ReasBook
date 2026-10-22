/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- A structured objective model consists of bounded closed convex sets `Q₁ ⊆ E₁` and
`Q₂ ⊆ E₂`, continuous convex functions `\hat f` on `Q₁` and `\hat φ` on `Q₂`, and a linear
operator `A : E₁ → E₂*`. -/
structure StructuredObjectiveModel (E₁ : Type u) (E₂ : Type v)
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] where
  /-- The primal set `Q₁ ⊆ E₁`. -/
  primalSet : Set E₁
  /-- The primal set `Q₁` is bounded. -/
  primalSet_bounded : Bornology.IsBounded primalSet
  /-- The primal set `Q₁` is closed. -/
  primalSet_closed : IsClosed primalSet
  /-- The primal set `Q₁` is convex. -/
  primalSet_convex : Convex ℝ primalSet
  /-- The dual set `Q₂ ⊆ E₂`. -/
  dualSet : Set E₂
  /-- The dual set `Q₂` is bounded. -/
  dualSet_bounded : Bornology.IsBounded dualSet
  /-- The dual set `Q₂` is closed. -/
  dualSet_closed : IsClosed dualSet
  /-- The dual set `Q₂` is convex. -/
  dualSet_convex : Convex ℝ dualSet
  /-- The continuous convex term `\hat f : E₁ → ℝ`, considered on `Q₁`. -/
  smoothPart : E₁ → ℝ
  /-- The continuous convex term `\hat φ : E₂ → ℝ`, considered on `Q₂`. -/
  dualPenalty : E₂ → ℝ
  /-- The linear operator `A : E₁ → E₂*`. -/
  linearMap : E₁ →L[ℝ] StrongDual ℝ E₂
  /-- The term `\hat f` is continuous on `Q₁`. -/
  smoothPart_continuous : ContinuousOn smoothPart primalSet
  /-- The term `\hat f` is convex on `Q₁`. -/
  smoothPart_convex : ConvexOn ℝ primalSet smoothPart
  /-- The term `\hat φ` is continuous on `Q₂`. -/
  dualPenalty_continuous : ContinuousOn dualPenalty dualSet
  /-- The term `\hat φ` is convex on `Q₂`. -/
  dualPenalty_convex : ConvexOn ℝ dualSet dualPenalty

namespace StructuredObjectiveModel

/-- The affine-convex maximand `u ↦ ⟪A x, u⟫ - \hat φ(u)` associated to a fixed `x ∈ Q₁`. -/
def maximand (problem : StructuredObjectiveModel E₁ E₂) (x : problem.primalSet) :
    problem.dualSet → ℝ :=
  fun u ↦ problem.linearMap x u - problem.dualPenalty u

/-- For Definition 6.6 [Chapter6_1.json:11], the saddle function is
`Ψ(x, u) = \hat f(x) + ⟪A x, u⟫ - \hat φ(u)` on `Q₁ × Q₂`; this saddle-point reformulation is
the basis for the primal and adjoint value functions defined below. -/
def saddleFunction (problem : StructuredObjectiveModel E₁ E₂) :
    problem.primalSet → problem.dualSet → ℝ :=
  fun x u ↦ problem.smoothPart x + problem.linearMap x u - problem.dualPenalty u

-- Proof sketch: unfold `saddleFunction`; the statement is definitionally true.
/-- Evaluating the saddle function recovers `\hat f(x) + ⟪A x, u⟫ - \hat φ(u)`. -/
theorem saddleFunction_apply (problem : StructuredObjectiveModel E₁ E₂)
    (x : problem.primalSet) (u : problem.dualSet) :
    problem.saddleFunction x u =
      problem.smoothPart x + problem.linearMap x u - problem.dualPenalty u :=
  by
    -- Unfold the saddle definition to expose the displayed affine-convex expression.
    rfl

/-- The primal objective `f(x) = sup_{u ∈ Q₂} Ψ(x, u)` attached to a structured objective model,
viewed in `EReal` so the supremum is represented faithfully without extra attainment or
boundedness hypotheses on the saddle slice. -/
def objective (problem : StructuredObjectiveModel E₁ E₂) : problem.primalSet → EReal :=
  fun x ↦ sSup (Set.range fun u : problem.dualSet ↦ (problem.saddleFunction x u : EReal))

/-- A structured objective model can be evaluated as its objective on the primal set `Q₁`. -/
instance : CoeFun (StructuredObjectiveModel E₁ E₂) (fun problem ↦ problem.primalSet → EReal) where
  coe problem := problem.objective

-- Proof sketch: unfold `objective`; the value is the displayed supremum by reflexivity.
/-- Evaluating the structured objective recovers the extended-real supremum of the saddle slice
`u ↦ Ψ(x, u)` on `Q₂`. -/
theorem objective_apply (problem : StructuredObjectiveModel E₁ E₂) (x : problem.primalSet) :
    problem.objective x =
      sSup (Set.range fun u : problem.dualSet ↦ (problem.saddleFunction x u : EReal)) :=
  by
    -- Unfold the objective definition; the supremum formula is the stored value.
    rfl

/-- The primal optimal value attached to a structured objective model, encoded as the infimum of
the objective values on `Q₁`, taken in `EReal` so empty or unbounded-below outer problems are
represented faithfully. This is the canonical value denoted `f^*` in the textbook; when the
infimum is attained and finite, it agrees with the corresponding minimum value. -/
def primalOptimalValue (problem : StructuredObjectiveModel E₁ E₂) : EReal :=
  sInf (Set.range problem.objective)

/-- The adjoint objective `φ(u) = inf_{x ∈ Q₁} Ψ(x, u)`, valued in `EReal` so the infimum is
represented faithfully without extra attainment assumptions on the primal slice. -/
def adjointObjective (problem : StructuredObjectiveModel E₁ E₂) : problem.dualSet → EReal :=
  fun u ↦ sInf (Set.range fun x : problem.primalSet ↦ (problem.saddleFunction x u : EReal))

/-- The adjoint optimal value `f_*`, encoded as the supremum of the adjoint objective over
`Q₂`, taken in `EReal` so empty or unbounded-above dual problems are represented faithfully; when
the supremum is attained and finite, it agrees with the corresponding maximum value. -/
def adjointOptimalValue (problem : StructuredObjectiveModel E₁ E₂) : EReal :=
  sSup (Set.range problem.adjointObjective)

-- Proof sketch: unfold `primalOptimalValue`; then unfold `problem.objective`.
/-- Definition 6.6 [Chapter6_1.json:11]: the primal optimal value is the infimum of the
saddle-point maximization `x ↦ sup_{u ∈ Q₂} Ψ(x, u)`. Under additional attainment or compactness
hypotheses, this agrees with the textbook minimum formula. -/
theorem primalOptimalValue_eq_saddle_form (problem : StructuredObjectiveModel E₁ E₂) :
    problem.primalOptimalValue =
      sInf (Set.range fun x : problem.primalSet ↦
        sSup (Set.range fun u : problem.dualSet ↦ (problem.saddleFunction x u : EReal))) :=
  by
    -- Expand the primal value into the infimum over the objective slices.
    unfold primalOptimalValue objective
    -- After unfolding both definitions, the saddle-point formula is definitionally identical.
    rfl

-- Proof sketch: unfold `adjointObjective`; the formula is the defining infimum of the saddle slice.
/-- Evaluating the adjoint objective recovers the extended-real infimum of the saddle slice
`x ↦ Ψ(x, u)` on `Q₁`. -/
theorem adjointObjective_apply (problem : StructuredObjectiveModel E₁ E₂)
    (u : problem.dualSet) :
    problem.adjointObjective u =
      sInf (Set.range fun x : problem.primalSet ↦ (problem.saddleFunction x u : EReal)) :=
  by
    -- Unfold the adjoint objective to reveal the defining infimum over primal points.
    rfl

-- Proof sketch: unfold `adjointOptimalValue`; the statement is the defining equality.
/-- Expanding `adjointOptimalValue` gives the supremum of the adjoint objective on `Q₂`. -/
theorem adjointOptimalValue_def (problem : StructuredObjectiveModel E₁ E₂) :
    problem.adjointOptimalValue = sSup (Set.range problem.adjointObjective) :=
  by
    -- Unfold the adjoint optimal value; it is defined as this supremum.
    rfl

end StructuredObjectiveModel

end
