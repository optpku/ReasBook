/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_50
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_68

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped LevelMethodNotation

/- Algorithm 3.10 lives in the level-method-history / projection-step owner domain.

Sampled owner declarations:
* `levelMethodHistoryFromApproximateValues` in `Proposition_3_50`
* `levelMethodApproximateProblem` in `Proposition_3_50`, together with the owner theorem
  `(levelMethodApproximateProblem problem.feasibleSet approximateObjective k)
    .optimalValue_eq_sInf_image`, the faithful owner bridge for exact model minima
* `LevelMethodHistory` and `LevelMethodHistory.levelValue` in `Lemma_3_3_1`
* `constrainedSublevelSet` in `Definition_3_3`, recalled in `Definition_3_68`
* `LevelMethodHistory.shouldStop` in `Lemma_3_3_1`
* `IsProjectionPointOn` in `Chap07/Definition_7_3`

Best owner abstraction:
* the source-facing method owner is a complete-data run over a fixed constrained problem
  `problem : SetConstrainedMinimizationProblem E`
* its exact lower-value owner at step `k` is the canonical
  `(levelMethodApproximateProblem problem.feasibleSet approximateObjective k).optimalValue`
* its scalar value history bridge is
  `levelMethodHistoryFromApproximateValues hatf problem xSeq`

Source/core/bridge triage:
* source-facing: `CompleteLevelMethod problem`
* core/canonical: `SetConstrainedMinimizationProblem E`, `LevelMethodHistory`,
  `LevelMethodHistory.levelValue`, and `constrainedSublevelSet`
* bridge/view: `CompleteLevelMethod.history`, its exactness certificate
  `CompleteLevelMethod.approximateOptimalValue_eq_optimalValue`, and the level-set membership
  consequence for the next iterate

Primitive data:
* the approximate models, iterate sequence, and the scalar parameters `ε`, `α`, over the fixed
  owner problem `problem`

Derived API:
* the canonical `EReal` exact model minimum at each step
* the explicit real lower-value sequence `\hat f_k^*` together with its `EReal` exactness bridge
* the scalar history bridge `(\hat f_k^*, f_k^*)`
* the level sets `𝓛_k(α)` written as
  `𝓛[problem.feasibleSet, model, history](α, k)`
* the stopping predicate `δ_k ≤ ε`, read directly as
  `method.history.shouldStop method.epsilon k`

Accordingly, `CompleteLevelMethod` is parameterized by the project's constrained-problem owner,
keeps only the primitive algorithm data that do not already belong to that owner, stores the real
lower values `\hat f_k^*` explicitly together with their canonical `EReal` exactness bridge,
derives its `LevelMethodHistory` through `levelMethodHistoryFromApproximateValues`, derives the
stopping rule from `LevelMethodHistory.shouldStop`, and records the textbook projection step directly on
`(x_k, x_{k + 1})` rather than through a separate total projection choice. The source side
conditions `ε > 0` and `α ∈ (0, 1)` are theorem-level hypotheses, not primitive run data, so
they are not stored in this owner. Since the public owner only uses feasible-set membership and
the metric projection predicate `IsProjectionPointOn`, it lives over the weaker ambient metric
layer; normed-space hypotheses belong only to downstream estimate files that use norms. -/

/- Algorithm 3.10 is stated in the text on `Q ⊆ ℝⁿ`, but the owner data only uses the ambient
metric geometry needed for projection points and real-valued model levels. The public owner
therefore lives over an arbitrary ambient type `E` equipped only with the corresponding metric
structure. -/
/-- Algorithm 3.10: for a fixed constrained problem `problem : SetConstrainedMinimizationProblem E`
with feasible set `Q ⊆ E` and objective `f`, a complete-data level method records the iterate
sequence `x₀, x₁, ...`, the approximate models `\hat f_k(X; ·)`, the scalar parameters `ε` and
`α`, and the textbook step condition that each successor `x_{k+1}` is a projection point of `x_k`
onto the level set
`𝓛_k(α) = {x ∈ Q | \hat f_k(X; x) ≤ (1 - α)\hat f_k^* + α f_k^*}`. The stopping rule is the
derived owner predicate `history.shouldStop ε k`, i.e. the gap test `δ_k ≤ ε`; whenever later
results use the source side conditions `ε > 0` or `α ∈ (0, 1)`, those conditions are imposed in
the theorem statement rather than stored as primitive fields of the run owner. The run owner
itself is metric-level: downstream normed or inner-product estimates are separate companions, not
part of the primitive algorithm data. -/
structure CompleteLevelMethod {E : Type u} [PseudoMetricSpace E]
    (problem : SetConstrainedMinimizationProblem E) where
  /-- The approximate model `\hat f_k(X; ·)` used at iteration `k`. -/
  approximateObjective : ℕ → E → ℝ
  /-- The explicit real lower value `\hat f_k^*` attached to the `k`-th model. -/
  approximateOptimalValue : ℕ → ℝ
  /-- The supplied real lower value agrees with the canonical exact `EReal` model minimum. -/
  approximateOptimalValue_eq_optimalValue (k : ℕ) :
      ((approximateOptimalValue k : ℝ) : EReal) =
        (levelMethodApproximateProblem problem.feasibleSet approximateObjective k).optimalValue
  /-- The prescribed initial point `x₀`. -/
  initialPoint : E
  /-- The initial point lies in the feasible set `Q`. -/
  initialPoint_mem : initialPoint ∈ problem.feasibleSet
  /-- The accuracy parameter `ε`. -/
  epsilon : ℝ
  /-- The level coefficient `α`. -/
  levelCoefficient : ℝ
  /-- The iterate sequence `x₀, x₁, ...`. -/
  iterate : ℕ → E
  /-- The iterate sequence starts from the prescribed point `x₀`. -/
  iterate_zero : iterate 0 = initialPoint
  /-- The update step sends `x_k` to a projection point `x_{k+1}` on the current level set
  `𝓛_k(α)`. -/
  step_isProjectionPointOn (k : ℕ) :
      let history :=
        levelMethodHistoryFromApproximateValues
          approximateOptimalValue
          problem
          iterate
      IsProjectionPointOn
        (𝓛[problem.feasibleSet, approximateObjective, history](levelCoefficient, k))
        (iterate k)
        (iterate (k + 1))

namespace CompleteLevelMethod

variable {E : Type u} [PseudoMetricSpace E]
variable {problem : SetConstrainedMinimizationProblem E}

/-- The canonical scalar value history attached to a complete-data level method. -/
abbrev history (method : CompleteLevelMethod problem) : LevelMethodHistory :=
  levelMethodHistoryFromApproximateValues
    method.approximateOptimalValue
    problem
    method.iterate

/-- A complete level method can be used as its underlying iterate sequence `x₀, x₁, x₂, ...`. -/
instance : CoeFun (CompleteLevelMethod problem) (fun _ ↦ ℕ → E) where
  coe method := method.iterate

/-- The update rule places the next iterate in the current level set. -/
theorem iterate_succ_mem_levelSet
    (method : CompleteLevelMethod problem) (k : ℕ) :
    method (k + 1) ∈
      𝓛[problem.feasibleSet, method.approximateObjective,
        method.history](method.levelCoefficient, k) := by
  exact (method.step_isProjectionPointOn k).1

/-- Every iterate produced by a complete level method lies in the feasible set. -/
theorem iterate_mem
    (method : CompleteLevelMethod problem) (k : ℕ) :
    method k ∈ problem.feasibleSet := by
  induction k with
  | zero =>
      simpa [method.iterate_zero] using method.initialPoint_mem
  | succ k _ =>
      exact (mem_constrainedSublevelSet_iff.mp
        (method.iterate_succ_mem_levelSet k)).1

end CompleteLevelMethod
