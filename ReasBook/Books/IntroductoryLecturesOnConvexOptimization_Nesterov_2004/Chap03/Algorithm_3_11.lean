/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Algorithm_3_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_52

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [PseudoMetricSpace E]

/-
Primary domain: two-level constrained level methods whose inner blocks are complete-data level
methods for constrained parametric max-objectives.

Owner abstractions sampled before refining:
* `CompleteLevelMethod` and `CompleteLevelMethod.history` from `Algorithm_3_10.lean`;
* `setConstrainedParametricObjective` from `Proposition_3_52.lean`, the chapter owner for the
  exact constrained slice `x ↦ max (f x - t) (fBar x)`;
* `constrainedThreshold` from `Lemma_3_3_4.lean`, the chapter owner for the canonical threshold
  `t_k^*(X)`;
* `ConstrainedMinimizationMethod`, `ConstrainedMinimizationMethod.x`, and
  `ConstrainedMinimizationMethod.t` from `Chap02/Algorithm_2_11.lean`, the project's owner
  pattern for a recursive two-level outer scheme on `(x_k, t_k) ∈ E × ℝ`.

Best owner abstraction:
* the source-facing owner is the recursive outer method itself;
* the fixed-stage exact slice remains the canonical owner
  `setConstrainedParametricObjective objective constraint t`;
* the fixed-stage threshold remains the canonical owner `constrainedThreshold`;
* the stage-local inner block remains the canonical owner
  `CompleteLevelMethod (stageProblemAt t)`.

Source/core/bridge triage:
* source-facing: the recursive outer scheme `ConstrainedLevelMethod`;
* core/canonical: `CompleteLevelMethod`, `setConstrainedParametricObjective`,
  `constrainedThreshold`, and `LevelMethodHistory`;
* bridge/view: the stage-local history, stopping indices, selected prefix iterate, and selected
  threshold attached to one actual master stage.

Primitive data:
* the feasible set `Q`, exact objective `f`, constraint function `fBar`, upper-model family
  `\hat f_{k,j}(X; ·)`, initial data `(x₀, t₀)`, and the stage-local internal trajectory rule.

Derived API:
* the exact constrained slice and its stage-local complete-data inner run;
* the first relative stopping index `j(k)`, the selected prefix iterate, and the selected
  threshold at an actual master stage;
* the recursive outer state `(x_k, t_k) ∈ E × ℝ`, with the continuing-step update used only on
  stages that have not yet met the global exact-value stopping criterion;
* the `EReal` threshold owner remains a bridge attached to one stage, not the public outer-state
  carrier.
-/

/-- Primitive input data for Algorithm 3.11 before imposing the recursive outer update rule. The
public owner of the method itself is the recursive scheme `ConstrainedLevelMethod` below; this
input record stores only the exact problem data, the upper models, and the stage-local complete
level-method trajectory rule. -/
structure ConstrainedLevelMethodInput (E : Type u) [PseudoMetricSpace E] where
  /-- The feasible set `Q ⊆ E`. -/
  feasibleSet : Set E
  /-- The exact objective `f : E → ℝ`. -/
  objective : E → ℝ
  /-- The constraint function `fBar : E → ℝ`. -/
  constraint : E → ℝ
  /-- The upper-model family `\hat f_{k,j}(X; ·)` attached to master stage `k`. -/
  upperModel : ℕ → ℕ → E → ℝ
  /-- The explicit real lower value `\hat f_{k,j}^*(X; t)` attached to the stage-local model
  family at master stage `k`, outer state `xBar`, parameter `t`, and internal index `j`. -/
  approximateOptimalValueAt : ℕ → E → ℝ → ℕ → ℝ
  /-- The supplied stage-local real lower value agrees with the canonical exact `EReal`
  minimum of the corresponding constrained model problem. -/
  approximateOptimalValueAt_eq_optimalValue
      (k : ℕ) (xBar : E) (t : ℝ) (j : ℕ) :
      ((approximateOptimalValueAt k xBar t j : ℝ) : EReal) =
        (levelMethodApproximateProblem
          feasibleSet
          (fun i ↦ setConstrainedParametricObjective (upperModel k i) constraint t)
          j).optimalValue
  /-- The prescribed initial point `x₀`. -/
  initialPoint : E
  /-- The initial point is feasible. -/
  initialPoint_mem : initialPoint ∈ feasibleSet
  /-- The prescribed initial parameter `t₀`. -/
  initialParameter : ℝ
  /-- The scalar parameter `χ`. -/
  chi : ℝ
  /-- The global accuracy parameter `ε`. -/
  epsilon : ℝ
  /-- The common inner level coefficient `α`. -/
  levelCoefficient : ℝ
  /-- At master stage `k`, started from an outer state `(x, t)`, this is the internal trajectory
  `x_{k,0}, x_{k,1}, x_{k,2}, ...` of the complete-data level process. -/
  internalIterateAt : ℕ → E → ℝ → ℕ → E
  /-- Every stage-local internal trajectory starts from the supplied outer point. -/
  internalIterateAt_zero (k : ℕ) (xBar : E) (t : ℝ) :
      internalIterateAt k xBar t 0 = xBar
  /-- Each internal successor step is the textbook projection update on the current level set for
  the stage-local constrained slice and stage-local model family. -/
  internalStep_isProjectionPointOn
      (k : ℕ) (xBar : E) (t : ℝ) (j : ℕ) :
      let history :=
        levelMethodHistoryFromApproximateValues
          (approximateOptimalValueAt k xBar t)
          (setConstrainedParametricObjective objective constraint t)
          (internalIterateAt k xBar t)
      IsProjectionPointOn
        (constrainedSublevelSet
          feasibleSet
          (fun x ↦
            (setConstrainedParametricObjective (upperModel k j) constraint t x : WithTop ℝ))
          (history.levelValue levelCoefficient j))
        (internalIterateAt k xBar t j)
        (internalIterateAt k xBar t (j + 1))

namespace ConstrainedLevelMethodInput

/-- The exact constrained slice at parameter `t`. -/
def exactObjectiveAt (method : ConstrainedLevelMethodInput E) (t : ℝ) : E → ℝ :=
  setConstrainedParametricObjective method.objective method.constraint t

/-- The constrained minimization owner for the exact slice at parameter `t`. -/
abbrev stageProblemAt
    (method : ConstrainedLevelMethodInput E) (t : ℝ) : SetConstrainedMinimizationProblem E :=
  .mk method.feasibleSet (method.exactObjectiveAt t)

/-- The approximate constrained slice family at master stage `k` and parameter `t`. -/
abbrev approximateObjectiveAt
    (method : ConstrainedLevelMethodInput E) (k : ℕ) (t : ℝ) : ℕ → E → ℝ :=
  fun j ↦ setConstrainedParametricObjective (method.upperModel k j) method.constraint t

/-- The scalar history attached to the stage-local internal run at the fixed outer state
`(k, x, t)`. -/
abbrev historyAt
    (method : ConstrainedLevelMethodInput E) (k : ℕ) (xBar : E) (t : ℝ) : LevelMethodHistory :=
  levelMethodHistoryFromApproximateValues
    (method.approximateOptimalValueAt k xBar t)
    (method.exactObjectiveAt t)
    (method.internalIterateAt k xBar t)

/-- The stage-local relative stopping predicate
`\hat f_j^*(X; t) ≥ (1 - χ) f_j^*(X; t)`. -/
def stoppingCriterionAt
    (method : ConstrainedLevelMethodInput E) (k : ℕ) (xBar : E) (t : ℝ) (j : ℕ) : Prop :=
  let history := method.historyAt k xBar t
  history.approximateOptimalValue j ≥ (1 - method.chi) * history.optimalValue j

/-- The global exact-value stopping predicate `f_j^*(X; t) ≤ ε` at the fixed outer state
`(k, x, t)`. -/
def globalStopCriterionAt
    (method : ConstrainedLevelMethodInput E) (k : ℕ) (xBar : E) (t : ℝ) (j : ℕ) : Prop :=
  (method.historyAt k xBar t).optimalValue j ≤ method.epsilon

/-- The stage-local state `(k, x, t)` is globally stopping once some exact record value is at
most `ε`. -/
def globallyStopsAtState
    (method : ConstrainedLevelMethodInput E) (k : ℕ) (xBar : E) (t : ℝ) : Prop :=
  ∃ j : ℕ, method.globalStopCriterionAt k xBar t j

/-- Supporting hypothesis: every stage-local state admits an index satisfying the relative
stopping criterion. This is a theorem-level recursion hypothesis, not primitive method data. -/
def RelativeStoppingExists (method : ConstrainedLevelMethodInput E) : Prop :=
  ∀ k : ℕ, ∀ xBar : E, ∀ t : ℝ, ∃ j : ℕ, method.stoppingCriterionAt k xBar t j

/-- The canonical first internal index satisfying the relative stopping criterion at the fixed
state `(k, x, t)`. -/
noncomputable def stoppingIndexAt
    (method : ConstrainedLevelMethodInput E) (hrelative : method.RelativeStoppingExists)
    (k : ℕ) (xBar : E) (t : ℝ) : ℕ :=
  by
    classical
    let _ : DecidablePred (method.stoppingCriterionAt k xBar t) := inferInstance
    exact Nat.find (hrelative k xBar t)

/-- The canonical stopping index is first with respect to the stage-local relative termination
criterion. -/
theorem stoppingIndexAt_isLeast
    (method : ConstrainedLevelMethodInput E) (hrelative : method.RelativeStoppingExists)
    (k : ℕ) (xBar : E) (t : ℝ) :
    IsLeast
      {j : ℕ | method.stoppingCriterionAt k xBar t j}
      (method.stoppingIndexAt hrelative k xBar t) := by
  classical
  let _ : DecidablePred (method.stoppingCriterionAt k xBar t) := inferInstance
  simpa [stoppingIndexAt, stoppingCriterionAt] using Nat.isLeast_find (hrelative k xBar t)

/-- Some produced prefix iterate realizes the selected record value
`f_{j(k)}^*(X; t)`. -/
theorem selectedIndexAt_exists
    (method : ConstrainedLevelMethodInput E) (hrelative : method.RelativeStoppingExists)
    (k : ℕ) (xBar : E) (t : ℝ) :
    ∃ j : ℕ,
      j ≤ method.stoppingIndexAt hrelative k xBar t ∧
        method.exactObjectiveAt t (method.internalIterateAt k xBar t j) =
          (method.historyAt k xBar t).optimalValue
            (method.stoppingIndexAt hrelative k xBar t) := by
  classical
  let p := method.stoppingIndexAt hrelative k xBar t
  let values : ℕ → ℝ := fun j ↦ method.exactObjectiveAt t (method.internalIterateAt k xBar t j)
  let s : Finset ℕ := Finset.range (p + 1)
  have hs : s.Nonempty := by
    refine ⟨0, ?_⟩
    simp [s]
  obtain ⟨j, hj_mem, hj_min⟩ := Finset.exists_min_image s values hs
  have hj_le : j ≤ p := Nat.lt_succ_iff.mp (by simpa [s] using Finset.mem_range.mp hj_mem)
  have hleft : values j ≤ bestFunctionValueUpTo values p := by
    rw [bestFunctionValueUpTo]
    refine le_ciInf fun i : Fin (p + 1) ↦ ?_
    exact hj_min i (by simpa [s] using Finset.mem_range.mpr i.isLt)
  have hright : bestFunctionValueUpTo values p ≤ values j :=
    bestFunctionValueUpTo_le ⟨j, Nat.lt_succ_of_le hj_le⟩
  refine ⟨j, hj_le, ?_⟩
  calc
    values j = bestFunctionValueUpTo values p := le_antisymm hleft hright
    _ = (method.historyAt k xBar t).optimalValue p := by
      symm
      simpa [historyAt, approximateObjectiveAt, exactObjectiveAt, values] using
        levelMethodHistoryFromApproximateValues_optimalValue_eq
          (method.approximateOptimalValueAt k xBar t)
          (method.exactObjectiveAt t)
          (method.internalIterateAt k xBar t)
          p

/-- The canonical selected prefix index at the fixed state `(k, x, t)`. -/
noncomputable def selectedIndexAt
    (method : ConstrainedLevelMethodInput E) (hrelative : method.RelativeStoppingExists)
    (k : ℕ) (xBar : E) (t : ℝ) : ℕ :=
  Nat.find (method.selectedIndexAt_exists hrelative k xBar t)

/-- The canonical selected prefix iterate at the fixed state `(k, x, t)`. -/
def selectedIterateAt
    (method : ConstrainedLevelMethodInput E) (hrelative : method.RelativeStoppingExists)
    (k : ℕ) (xBar : E) (t : ℝ) : E :=
  method.internalIterateAt k xBar t (method.selectedIndexAt hrelative k xBar t)

/-- The canonical threshold `t_j^*(X)` for the stage-`k` upper-model family. -/
def stageThreshold (method : ConstrainedLevelMethodInput E) (k j : ℕ) : EReal :=
  constrainedThreshold
    method.feasibleSet
    (fun i _ ↦ method.upperModel k i)
    (fun _ _ ↦ method.constraint)
    j
    ()

/-- The selected threshold at the fixed state `(k, x, t)`. -/
def selectedThresholdAt
    (method : ConstrainedLevelMethodInput E) (hrelative : method.RelativeStoppingExists)
    (k : ℕ) (xBar : E) (t : ℝ) : EReal :=
  method.stageThreshold k (method.stoppingIndexAt hrelative k xBar t)

/-- Supporting hypothesis: every selected threshold is finite, so the recursive outer parameter is
stored canonically as a finite extended-real value and can then be read faithfully as a real
number. -/
def SelectedThresholdFinite
    (method : ConstrainedLevelMethodInput E) (hrelative : method.RelativeStoppingExists) : Prop :=
  ∀ k : ℕ, ∀ xBar : E, ∀ t : ℝ,
    let τ := method.selectedThresholdAt hrelative k xBar t
    τ ≠ ⊤ ∧ τ ≠ ⊥

/-- The selected threshold at a fixed stage-local state is finite. -/
theorem selectedThresholdAt_ne_top_bot
    (method : ConstrainedLevelMethodInput E) (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative)
    (k : ℕ) (xBar : E) (t : ℝ) :
    method.selectedThresholdAt hrelative k xBar t ≠ ⊤ ∧
      method.selectedThresholdAt hrelative k xBar t ≠ ⊥ := by
  simpa [SelectedThresholdFinite] using hfinite k xBar t

/-- The real threshold used by the outer recursion at the fixed state `(k, x, t)`, read from the
canonical finite threshold witness. -/
def selectedParameterAt
    (method : ConstrainedLevelMethodInput E) (hrelative : method.RelativeStoppingExists)
    (k : ℕ) (xBar : E) (t : ℝ) : ℝ :=
  (method.selectedThresholdAt hrelative k xBar t).toReal

/-- Coercing the real selected parameter back to `EReal` recovers the canonical selected
threshold. -/
theorem coe_selectedParameterAt
    (method : ConstrainedLevelMethodInput E) (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative)
    (k : ℕ) (xBar : E) (t : ℝ) :
    ((method.selectedParameterAt hrelative k xBar t : ℝ) : EReal) =
      method.selectedThresholdAt hrelative k xBar t := by
  exact EReal.coe_toReal
    (method.selectedThresholdAt_ne_top_bot hrelative hfinite k xBar t).1
    (method.selectedThresholdAt_ne_top_bot hrelative hfinite k xBar t).2

/-- Every internal iterate stays in the feasible set once the stage-local outer point is feasible.
-/
theorem internalIterateAt_mem_feasible
    (method : ConstrainedLevelMethodInput E) (k : ℕ) (xBar : E)
    (hxBar : xBar ∈ method.feasibleSet) (t : ℝ) :
    ∀ j : ℕ, method.internalIterateAt k xBar t j ∈ method.feasibleSet
  | 0 => by
      simpa [method.internalIterateAt_zero k xBar t] using hxBar
  | j + 1 => by
      exact (mem_constrainedSublevelSet_iff.mp
        (method.internalStep_isProjectionPointOn k xBar t j).1).1

/-- The selected iterate is feasible whenever the stage-local outer point is feasible. -/
theorem selectedIterateAt_mem_feasible
    (method : ConstrainedLevelMethodInput E) (hrelative : method.RelativeStoppingExists)
    (k : ℕ) (xBar : E) (hxBar : xBar ∈ method.feasibleSet) (t : ℝ) :
    method.selectedIterateAt hrelative k xBar t ∈ method.feasibleSet := by
  unfold selectedIterateAt
  exact method.internalIterateAt_mem_feasible k xBar hxBar t
    (method.selectedIndexAt hrelative k xBar t)

/-- The stage-local inner block at a feasible outer state, exposed through the canonical owner
`CompleteLevelMethod`. -/
def completeRunAt
    (method : ConstrainedLevelMethodInput E) (k : ℕ) (xBar : E)
    (hxBar : xBar ∈ method.feasibleSet) (t : ℝ) :
    CompleteLevelMethod (method.stageProblemAt t) where
  approximateObjective := method.approximateObjectiveAt k t
  approximateOptimalValue := method.approximateOptimalValueAt k xBar t
  approximateOptimalValue_eq_optimalValue :=
    method.approximateOptimalValueAt_eq_optimalValue k xBar t
  initialPoint := xBar
  initialPoint_mem := hxBar
  epsilon := method.epsilon
  levelCoefficient := method.levelCoefficient
  iterate := method.internalIterateAt k xBar t
  iterate_zero := method.internalIterateAt_zero k xBar t
  step_isProjectionPointOn := method.internalStep_isProjectionPointOn k xBar t

/-- The canonical first internal index where the global exact-value stopping rule holds at the
fixed state `(k, x, t)`. -/
noncomputable def globalStopIndexAt
    (method : ConstrainedLevelMethodInput E) (k : ℕ) (xBar : E) (t : ℝ)
    (hstop : method.globallyStopsAtState k xBar t) : ℕ :=
  by
    classical
    let _ : DecidablePred (method.globalStopCriterionAt k xBar t) := inferInstance
    exact Nat.find hstop

/-- The global exact-value stopping index is first with respect to `f_j^*(X; t) ≤ ε` at the fixed
state `(k, x, t)`. -/
theorem globalStopIndexAt_isLeast
    (method : ConstrainedLevelMethodInput E) (k : ℕ) (xBar : E) (t : ℝ)
    (hstop : method.globallyStopsAtState k xBar t) :
    IsLeast
      {j : ℕ | method.globalStopCriterionAt k xBar t j}
      (method.globalStopIndexAt k xBar t hstop) := by
  classical
  let _ : DecidablePred (method.globalStopCriterionAt k xBar t) := inferInstance
  simpa [globalStopIndexAt, globallyStopsAtState, globalStopCriterionAt] using
    Nat.isLeast_find hstop

end ConstrainedLevelMethodInput

/- The outer recursion stores its threshold internally as a finite `EReal`, but that carrier is
implementation detail rather than part of the public source-facing API. -/
private abbrev FiniteThreshold := {τ : EReal // τ ≠ ⊤ ∧ τ ≠ ⊥}

private def finiteThresholdReal (τ : FiniteThreshold) : ℝ :=
  τ.1.toReal

@[simp] private theorem coe_finiteThresholdReal (τ : FiniteThreshold) :
    ((finiteThresholdReal τ : ℝ) : EReal) = τ.1 := by
  exact EReal.coe_toReal τ.2.1 τ.2.2

private def initialFiniteThreshold
    (method : ConstrainedLevelMethodInput E) : FiniteThreshold :=
  ⟨(method.initialParameter : EReal), by simp⟩

private def selectedFiniteThresholdAt
    (method : ConstrainedLevelMethodInput E) (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative)
    (k : ℕ) (xBar : E) (t : ℝ) : FiniteThreshold :=
  ⟨method.selectedThresholdAt hrelative k xBar t,
    method.selectedThresholdAt_ne_top_bot hrelative hfinite k xBar t⟩

/-- Algorithm 3.11: the recursive outer constrained level method generated from the primitive
stage-local data `method`. Internally the threshold state is stored as a finite `EReal` value so
that the finiteness hypothesis `hfinite` is part of the actual recursion, not merely a later
bridge. At master step `k`, the next state equals the current state if the stage already
satisfies the global exact-value stopping rule; otherwise the method performs the continuing-step
update by moving to the selected produced iterate and the selected threshold
`t_{j(k)}^*(X_k)`, stored together with its finiteness proof. -/
private noncomputable def constrainedLevelMethodState
    (method : ConstrainedLevelMethodInput E)
    (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative) :
    ℕ → E × FiniteThreshold
  | 0 => (method.initialPoint, initialFiniteThreshold method)
  | k + 1 =>
      by
        classical
        let statek := constrainedLevelMethodState method hrelative hfinite k
        let tk := finiteThresholdReal statek.2
        let _ : Decidable (method.globallyStopsAtState k statek.1 tk) := inferInstance
        exact
          if hstop : method.globallyStopsAtState k statek.1 tk then
            statek
          else
            ( method.selectedIterateAt hrelative k statek.1 tk
            , selectedFiniteThresholdAt method hrelative hfinite k statek.1 tk )

/-- Algorithm 3.11: the recursive outer constrained level method generated from the primitive
stage-local data `method`. At master step `k`, the next state equals the current state if the
stage already satisfies the global exact-value stopping rule; otherwise the method performs the
continuing-step update by moving to the selected produced iterate and the selected real threshold
`t_{j(k)}^*(X_k)`. The public real parameter is read from the finite-threshold core recursion
above. -/
noncomputable def ConstrainedLevelMethod
    (method : ConstrainedLevelMethodInput E)
    (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative) :
    ℕ → E × ℝ :=
  fun k ↦
    let statek := constrainedLevelMethodState method hrelative hfinite k
    (statek.1, finiteThresholdReal statek.2)

namespace ConstrainedLevelMethod

variable (method : ConstrainedLevelMethodInput E)
variable (hrelative : method.RelativeStoppingExists)
variable (hfinite : method.SelectedThresholdFinite hrelative)

local notation "coreScheme" => constrainedLevelMethodState method hrelative hfinite

/-- The recursive outer state `(x_k, t_k)`. -/
abbrev state (k : ℕ) : E × ℝ :=
  ConstrainedLevelMethod method hrelative hfinite k

/-- The master iterate sequence `x₀, x₁, x₂, ...`. -/
def masterIterate (k : ℕ) : E :=
  (coreScheme k).1

/-- The master-threshold sequence `t₀, t₁, t₂, ...`. -/
def parameter (k : ℕ) : ℝ :=
  finiteThresholdReal (coreScheme k).2

@[simp] theorem masterIterate_zero :
    masterIterate method hrelative hfinite 0 = method.initialPoint :=
  rfl

@[simp] theorem parameter_zero :
    parameter method hrelative hfinite 0 = method.initialParameter :=
  by
    simp [parameter, initialFiniteThreshold, finiteThresholdReal, constrainedLevelMethodState]

/-- Every master iterate produced by the recursive outer method remains feasible. -/
theorem masterIterate_mem :
    ∀ k : ℕ, masterIterate method hrelative hfinite k ∈ method.feasibleSet := by
  have hmem :
      ∀ k : ℕ, (constrainedLevelMethodState method hrelative hfinite k).1 ∈ method.feasibleSet := by
    intro k
    induction k with
    | zero =>
        simpa [constrainedLevelMethodState] using method.initialPoint_mem
    | succ k ih =>
        let statek := constrainedLevelMethodState method hrelative hfinite k
        let tk := finiteThresholdReal statek.2
        by_cases hstop : method.globallyStopsAtState k statek.1 tk
        · simpa [constrainedLevelMethodState, statek, tk, hstop] using ih
        · have hk : statek.1 ∈ method.feasibleSet := by
            simpa [statek] using ih
          simpa [constrainedLevelMethodState, statek, tk, hstop] using
            method.selectedIterateAt_mem_feasible hrelative k statek.1 hk tk
  intro k
  simpa [masterIterate] using hmem k

/-- The actual inner run executed at master step `k`, exposed through the canonical owner
`CompleteLevelMethod`. -/
abbrev completeRun (k : ℕ) :
    CompleteLevelMethod (method.stageProblemAt (parameter method hrelative hfinite k)) :=
  method.completeRunAt
    k
    (masterIterate method hrelative hfinite k)
    (masterIterate_mem method hrelative hfinite k)
    (parameter method hrelative hfinite k)

/-- The canonical scalar history attached to the actual inner run at master step `k`. -/
abbrev history (k : ℕ) : LevelMethodHistory :=
  (completeRun method hrelative hfinite k).history

/-- The `j`-th internal iterate produced at master iteration `k`. -/
def internalIterate (k j : ℕ) : E :=
  (completeRun method hrelative hfinite k) j

/-- The internal relative stopping predicate at master step `k` and internal index `j`. -/
def stoppingCriterion (k j : ℕ) : Prop :=
  method.stoppingCriterionAt
    k
    (masterIterate method hrelative hfinite k)
    (parameter method hrelative hfinite k)
    j

/-- The canonical first internal index `j(k)` satisfying the relative stopping criterion. -/
noncomputable def stoppingIndex (k : ℕ) : ℕ :=
  method.stoppingIndexAt
    hrelative
    k
    (masterIterate method hrelative hfinite k)
    (parameter method hrelative hfinite k)

/-- The global exact-value stopping predicate at master step `k` and internal index `j`. -/
def globalStopCriterion (k j : ℕ) : Prop :=
  method.globalStopCriterionAt
    k
    (masterIterate method hrelative hfinite k)
    (parameter method hrelative hfinite k)
    j

/-- The method globally stops on master step `k` once some internal exact record value is at most
`ε`. -/
def globallyStopsAt (k : ℕ) : Prop :=
  method.globallyStopsAtState
    k
    (masterIterate method hrelative hfinite k)
    (parameter method hrelative hfinite k)

/-- The canonical first internal index where the global exact-value stopping rule holds. -/
noncomputable def globalStopIndex (k : ℕ) (hstop : globallyStopsAt method hrelative hfinite k) :
    ℕ :=
  method.globalStopIndexAt
    k
    (masterIterate method hrelative hfinite k)
    (parameter method hrelative hfinite k)
    hstop

/-- The selected prefix index at master step `k`. -/
noncomputable def selectedIndex (k : ℕ) : ℕ :=
  method.selectedIndexAt
    hrelative
    k
    (masterIterate method hrelative hfinite k)
    (parameter method hrelative hfinite k)

/-- The selected prefix iterate at master step `k`. -/
def selectedIterate (k : ℕ) : E :=
  method.selectedIterateAt
    hrelative
    k
    (masterIterate method hrelative hfinite k)
    (parameter method hrelative hfinite k)

/-- The selected real parameter at master step `k`. -/
def selectedParameter (k : ℕ) : ℝ :=
  method.selectedParameterAt
    hrelative
    k
    (masterIterate method hrelative hfinite k)
    (parameter method hrelative hfinite k)

/-- The selected constrained threshold at master step `k`, kept as the `EReal` bridge to the
chapter threshold owner. -/
def selectedThreshold (k : ℕ) : EReal :=
  method.selectedThresholdAt
    hrelative
    k
    (masterIterate method hrelative hfinite k)
    (parameter method hrelative hfinite k)

/-- Coercing the selected real parameter back to `EReal` recovers the canonical selected
threshold. -/
theorem coe_selectedParameter (k : ℕ) :
    ((selectedParameter method hrelative hfinite k : ℝ) : EReal) =
      selectedThreshold method hrelative hfinite k := by
  simpa [selectedParameter, selectedThreshold] using
    method.coe_selectedParameterAt
      hrelative
      hfinite
      k
      (masterIterate method hrelative hfinite k)
      (parameter method hrelative hfinite k)

/-- The canonical stopping index is first with respect to the internal relative termination
criterion. -/
theorem stoppingIndex_isLeast (k : ℕ) :
    IsLeast
      {j : ℕ | stoppingCriterion method hrelative hfinite k j}
      (stoppingIndex method hrelative hfinite k) := by
  simpa [stoppingCriterion, stoppingIndex] using
    method.stoppingIndexAt_isLeast
      hrelative
      k
      (masterIterate method hrelative hfinite k)
      (parameter method hrelative hfinite k)

/-- The global exact-value stopping index is first with respect to `f_j^*(X; t_k) ≤ ε`. -/
theorem globalStopIndex_isLeast
    (k : ℕ) (hstop : globallyStopsAt method hrelative hfinite k) :
    IsLeast
      {j : ℕ | globalStopCriterion method hrelative hfinite k j}
      (globalStopIndex method hrelative hfinite k hstop) := by
  simpa [globalStopCriterion, globalStopIndex] using
    method.globalStopIndexAt_isLeast
      k
      (masterIterate method hrelative hfinite k)
      (parameter method hrelative hfinite k)
      hstop

/-- Every internal run starts from the current master iterate `x_k`. -/
theorem internalIterate_zero (k : ℕ) :
    internalIterate method hrelative hfinite k 0 =
      masterIterate method hrelative hfinite k := by
  simpa [internalIterate, completeRun] using (completeRun method hrelative hfinite k).iterate_zero

/-- The selected prefix index lies on the produced prefix `0, ..., j(k)`. -/
theorem selectedIndex_le_stoppingIndex (k : ℕ) :
    selectedIndex method hrelative hfinite k ≤ stoppingIndex method hrelative hfinite k := by
  change
    method.selectedIndexAt
        hrelative
        k
        (masterIterate method hrelative hfinite k)
        (parameter method hrelative hfinite k) ≤
      method.stoppingIndexAt
        hrelative
        k
        (masterIterate method hrelative hfinite k)
        (parameter method hrelative hfinite k)
  exact
    (Nat.find_spec
      (method.selectedIndexAt_exists
        hrelative
        k
        (masterIterate method hrelative hfinite k)
        (parameter method hrelative hfinite k))).1

/-- The selected prefix iterate realizes the selected record value
`f_{j(k)}^*(X; t_k)`. -/
theorem selectedIterate_eq_optimalValue (k : ℕ) :
    method.exactObjectiveAt (parameter method hrelative hfinite k)
        (selectedIterate method hrelative hfinite k) =
      (history method hrelative hfinite k).optimalValue
        (stoppingIndex method hrelative hfinite k) := by
  change
    method.exactObjectiveAt (parameter method hrelative hfinite k)
        (method.internalIterateAt
          k
          (masterIterate method hrelative hfinite k)
          (parameter method hrelative hfinite k)
          (method.selectedIndexAt
            hrelative
            k
            (masterIterate method hrelative hfinite k)
            (parameter method hrelative hfinite k))) =
      (method.historyAt
        k
        (masterIterate method hrelative hfinite k)
        (parameter method hrelative hfinite k)).optimalValue
        (method.stoppingIndexAt
          hrelative
          k
          (masterIterate method hrelative hfinite k)
          (parameter method hrelative hfinite k))
  exact
    (Nat.find_spec
      (method.selectedIndexAt_exists
        hrelative
        k
        (masterIterate method hrelative hfinite k)
        (parameter method hrelative hfinite k))).2

/-- The first stopping index satisfies the internal relative termination criterion. -/
theorem stopping_condition (k : ℕ) :
    stoppingCriterion method hrelative hfinite k
      (stoppingIndex method hrelative hfinite k) := by
  simpa [stoppingCriterion] using (stoppingIndex_isLeast method hrelative hfinite k).1

/-- No earlier internal iterate satisfies the relative stopping criterion. -/
theorem stopping_condition_min {k j : ℕ}
    (hj : j < stoppingIndex method hrelative hfinite k) :
    ¬ stoppingCriterion method hrelative hfinite k j := by
  intro hjStop
  exact (not_le_of_gt hj) ((stoppingIndex_isLeast method hrelative hfinite k).2 (by
    simpa [stoppingCriterion] using hjStop))

/-- The first global exact-value stopping index satisfies `f_j^*(X; t_k) ≤ ε`. -/
theorem global_stop_condition
    (k : ℕ) (hstop : globallyStopsAt method hrelative hfinite k) :
    globalStopCriterion method hrelative hfinite k
      (globalStopIndex method hrelative hfinite k hstop) := by
  exact (globalStopIndex_isLeast method hrelative hfinite k hstop).1

/-- No earlier internal iterate satisfies the global exact-value stopping criterion. -/
theorem global_stop_condition_min
    (k : ℕ) (hstop : globallyStopsAt method hrelative hfinite k)
    {j : ℕ} (hj : j < globalStopIndex method hrelative hfinite k hstop) :
    ¬ globalStopCriterion method hrelative hfinite k j := by
  intro hjStop
  exact (not_le_of_gt hj) ((globalStopIndex_isLeast method hrelative hfinite k hstop).2 hjStop)

/-- If master step `k` already satisfies the global stopping rule, the recursive outer state is
held fixed at step `k + 1`. -/
theorem masterIterate_succ_eq_self_of_globallyStopsAt
    (k : ℕ) (hstop : globallyStopsAt method hrelative hfinite k) :
    masterIterate method hrelative hfinite (k + 1) =
      masterIterate method hrelative hfinite k := by
  let statek := constrainedLevelMethodState method hrelative hfinite k
  let tk := finiteThresholdReal statek.2
  have hstop' : method.globallyStopsAtState k statek.1 tk := by
    simpa [globallyStopsAt, masterIterate, parameter, statek, tk] using hstop
  simp [masterIterate, constrainedLevelMethodState, statek, tk, hstop']

/-- If master step `k` already satisfies the global stopping rule, the recursive parameter is
held fixed at step `k + 1`. -/
theorem parameter_succ_eq_self_of_globallyStopsAt
    (k : ℕ) (hstop : globallyStopsAt method hrelative hfinite k) :
    parameter method hrelative hfinite (k + 1) =
      parameter method hrelative hfinite k := by
  let statek := constrainedLevelMethodState method hrelative hfinite k
  let tk := finiteThresholdReal statek.2
  have hstop' : method.globallyStopsAtState k statek.1 tk := by
    simpa [globallyStopsAt, masterIterate, parameter, statek, tk] using hstop
  have hstate :
      constrainedLevelMethodState method hrelative hfinite (k + 1) = statek := by
    simp [constrainedLevelMethodState, statek, tk, hstop']
  simpa [parameter, statek] using
    congrArg (fun s : E × FiniteThreshold ↦ finiteThresholdReal s.2) hstate

/-- On a continuing stage, the recursive outer update moves to the selected produced inner
iterate. -/
theorem masterIterate_succ_eq_selectedIterate_of_not_globallyStopsAt
    (k : ℕ) (hcont : ¬ globallyStopsAt method hrelative hfinite k) :
    masterIterate method hrelative hfinite (k + 1) =
      selectedIterate method hrelative hfinite k := by
  let statek := constrainedLevelMethodState method hrelative hfinite k
  let tk := finiteThresholdReal statek.2
  have hcont' : ¬ method.globallyStopsAtState k statek.1 tk := by
    simpa [globallyStopsAt, masterIterate, parameter, statek, tk] using hcont
  have hstep :
      (constrainedLevelMethodState method hrelative hfinite (k + 1)).1 =
        method.selectedIterateAt hrelative k statek.1 tk := by
    simp [constrainedLevelMethodState, statek, tk, hcont']
  calc
    masterIterate method hrelative hfinite (k + 1) =
        (constrainedLevelMethodState method hrelative hfinite (k + 1)).1 := rfl
    _ = method.selectedIterateAt hrelative k statek.1 tk := hstep
    _ = selectedIterate method hrelative hfinite k := by
          simp [selectedIterate, masterIterate, parameter, statek, tk]

/-- The selected threshold at master step `k` is finite. -/
theorem selectedThreshold_ne_top_bot (k : ℕ) :
    selectedThreshold method hrelative hfinite k ≠ ⊤ ∧
      selectedThreshold method hrelative hfinite k ≠ ⊥ := by
  simpa [selectedThreshold] using
    method.selectedThresholdAt_ne_top_bot
      hrelative
      hfinite
      k
      (masterIterate method hrelative hfinite k)
      (parameter method hrelative hfinite k)

/-- On a continuing stage, the recursive outer update sets the next parameter to the selected real
threshold `t_{j(k)}^*(X)`. -/
theorem parameter_succ_of_not_globallyStopsAt
    (k : ℕ) (hcont : ¬ globallyStopsAt method hrelative hfinite k) :
    parameter method hrelative hfinite (k + 1) =
      selectedParameter method hrelative hfinite k := by
  let statek := constrainedLevelMethodState method hrelative hfinite k
  let tk := finiteThresholdReal statek.2
  have hcont' : ¬ method.globallyStopsAtState k statek.1 tk := by
    simpa [globallyStopsAt, masterIterate, parameter, statek, tk] using hcont
  have hstep :
      (constrainedLevelMethodState method hrelative hfinite (k + 1)).2 =
        selectedFiniteThresholdAt method hrelative hfinite k statek.1 tk := by
    simp [constrainedLevelMethodState, statek, tk, hcont']
  calc
    parameter method hrelative hfinite (k + 1) =
        finiteThresholdReal
          ((constrainedLevelMethodState method hrelative hfinite (k + 1)).2) := rfl
    _ =
        finiteThresholdReal
          (selectedFiniteThresholdAt method hrelative hfinite k statek.1 tk) := by
            rw [hstep]
    _ = method.selectedParameterAt hrelative k statek.1 tk := rfl
    _ = selectedParameter method hrelative hfinite k := by
          simp [selectedParameter, masterIterate, parameter, statek, tk]

/-- On a continuing stage, coercing the next parameter back to `EReal` recovers the selected
threshold. -/
theorem coe_parameter_succ_of_not_globallyStopsAt
    (k : ℕ) (hcont : ¬ globallyStopsAt method hrelative hfinite k) :
    ((parameter method hrelative hfinite (k + 1) : ℝ) : EReal) =
      selectedThreshold method hrelative hfinite k := by
  rw [parameter_succ_of_not_globallyStopsAt method hrelative hfinite k hcont]
  exact coe_selectedParameter method hrelative hfinite k

/-- On a continuing stage, the recursive outer update selects a produced inner iterate up to the
first relative stopping index, and it realizes the selected exact record value. -/
theorem masterIterate_succ_of_not_globallyStopsAt
    (k : ℕ) (hcont : ¬ globallyStopsAt method hrelative hfinite k) :
    ∃ j : ℕ,
      j ≤ stoppingIndex method hrelative hfinite k ∧
        masterIterate method hrelative hfinite (k + 1) =
          internalIterate method hrelative hfinite k j ∧
        method.exactObjectiveAt (parameter method hrelative hfinite k)
            (masterIterate method hrelative hfinite (k + 1)) =
          (history method hrelative hfinite k).optimalValue
            (stoppingIndex method hrelative hfinite k) := by
  refine
    ⟨ selectedIndex method hrelative hfinite k
    , selectedIndex_le_stoppingIndex method hrelative hfinite k
    , ?_
    , ?_
    ⟩
  · calc
      masterIterate method hrelative hfinite (k + 1) =
          selectedIterate method hrelative hfinite k :=
            masterIterate_succ_eq_selectedIterate_of_not_globallyStopsAt
              method hrelative hfinite k hcont
      _ = internalIterate method hrelative hfinite k
            (selectedIndex method hrelative hfinite k) := rfl
  · rw [masterIterate_succ_eq_selectedIterate_of_not_globallyStopsAt
        method hrelative hfinite k hcont]
    exact selectedIterate_eq_optimalValue method hrelative hfinite k

end ConstrainedLevelMethod

end
