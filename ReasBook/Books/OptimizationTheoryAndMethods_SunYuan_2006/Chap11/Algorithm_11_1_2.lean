/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.WithTop
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Definition_11_1_extra_2

noncomputable section

section Chapter11Algorithm1112

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Layer triage:
-- * source-facing: `FeasibleDirectionArmijoState`, `feasibleDirectionArmijoStep`
-- * core/canonical reused from earlier project owners: `feasiblePointArmijoAccepts`
-- * bridge/view: the branch-characterization lemmas for `feasibleDirectionArmijoStep`

/-- The mutable state `(α_max, α)` used by Algorithm 11.1.2. -/
structure FeasibleDirectionArmijoState where
  upper : WithTop ℝ
  trial : ℝ

/-- Chapter11 Algorithm 11.1.2 (1): Step 1 initializes the feasible-direction Armijo search at
`(α_max, α) = (+∞, 1)`. -/
def feasibleDirectionArmijoInitialState : FeasibleDirectionArmijoState where
  upper := ⊤
  trial := 1

/-- Unfolding `feasibleDirectionArmijoInitialState` gives the concrete Step 1 values
`(α_max, α) = (+∞, 1)`. -/
theorem feasibleDirectionArmijoInitialState_eq :
    feasibleDirectionArmijoInitialState =
      { upper := (⊤ : WithTop ℝ)
        trial := 1 } :=
  rfl

/- #check feasibleDirectionArmijoInitialState
#check feasibleDirectionArmijoStep -/

/-- One Step 2/Step 3 update of Algorithm 11.1.2 either stops with an accepted step or produces
the next state `(α_max, α)`. -/
inductive FeasibleDirectionArmijoStepResult where
  | stop (acceptedStep : ℝ)
  | continueWith (nextState : FeasibleDirectionArmijoState)

/-- Chapter11 Algorithm 11.1.2 (2): under the Step 1 hypotheses that `d` is a feasible descent
direction at `x` and `c1 ∈ Set.Ioo (0 : ℝ) 1`, Steps 2 and 3 send the current state to the next
state prescribed by the feasible-point Armijo test: accepting trials with finite `α_max` stop;
accepting trials with `α_max = +∞` double `α`; rejected trials set `α_max := α` and
`α := α / 2`. -/
noncomputable def feasibleDirectionArmijoStep
    (f : Point → ℝ) (X : Set Point) (c1 : ℝ) (x d : Point)
    (state : FeasibleDirectionArmijoState) :
    FeasibleDirectionArmijoStepResult :=
  let _ : Decidable (feasiblePointArmijoAccepts f X c1 x d state.trial) :=
    Classical.decPred (fun α ↦ feasiblePointArmijoAccepts f X c1 x d α) state.trial
  if feasiblePointArmijoAccepts f X c1 x d state.trial then
    match state.upper with
    | ⊤ =>
        .continueWith
          { upper := ⊤
            trial := 2 * state.trial }
    | (_ : ℝ) =>
        .stop state.trial
  else
    .continueWith
      { upper := state.trial
        trial := state.trial / 2 }

/-- `feasibleDirectionArmijoStep` stops exactly when the current trial point passes the Step 2
test and the current upper bound `α_max` is finite. -/
theorem feasibleDirectionArmijoStep_eq_stop_iff
    {f : Point → ℝ} {X : Set Point} {c1 : ℝ} {x d : Point}
    {state : FeasibleDirectionArmijoState} :
    feasibleDirectionArmijoStep f X c1 x d state = .stop state.trial ↔
      feasiblePointArmijoAccepts f X c1 x d state.trial ∧
        ∃ αMax : ℝ, state.upper = αMax := by
  classical
  constructor
  · intro hStep
    by_cases hAccept : feasiblePointArmijoAccepts f X c1 x d state.trial
    · cases hUpper : state.upper with
      | top =>
          simp [feasibleDirectionArmijoStep, hAccept, hUpper] at hStep
      | coe αMax =>
          exact ⟨hAccept, ⟨αMax, rfl⟩⟩
    · simp [feasibleDirectionArmijoStep, hAccept] at hStep
  · rintro ⟨hAccept, αMax, hUpper⟩
    simp [feasibleDirectionArmijoStep, hAccept, hUpper]

/-- If the current trial point passes the Step 2 test and `α_max = +∞`, then
`feasibleDirectionArmijoStep` doubles the trial steplength and keeps the upper bound infinite. -/
theorem feasibleDirectionArmijoStep_eq_continueWith_infinity_iff
    {f : Point → ℝ} {X : Set Point} {c1 : ℝ} {x d : Point}
    {state : FeasibleDirectionArmijoState} :
    feasibleDirectionArmijoStep f X c1 x d state =
      FeasibleDirectionArmijoStepResult.continueWith
        { upper := (⊤ : WithTop ℝ)
          trial := 2 * state.trial } ↔
      feasiblePointArmijoAccepts f X c1 x d state.trial ∧
        state.upper = ⊤ := by
  classical
  constructor
  · intro hStep
    by_cases hAccept : feasiblePointArmijoAccepts f X c1 x d state.trial
    · cases hUpper : state.upper with
      | top =>
          exact ⟨hAccept, rfl⟩
      | coe αMax =>
          simp [feasibleDirectionArmijoStep, hAccept, hUpper] at hStep
    · simp [feasibleDirectionArmijoStep, hAccept] at hStep
  · rintro ⟨hAccept, hUpper⟩
    simp [feasibleDirectionArmijoStep, hAccept, hUpper]

/-- If the current trial point fails the Step 2 test, then `feasibleDirectionArmijoStep`
performs the Step 3 update `α_max := α` and `α := α / 2`. -/
theorem feasibleDirectionArmijoStep_eq_continueWith_reject_iff
    {f : Point → ℝ} {X : Set Point} {c1 : ℝ} {x d : Point}
    {state : FeasibleDirectionArmijoState} :
    feasibleDirectionArmijoStep f X c1 x d state =
      FeasibleDirectionArmijoStepResult.continueWith
        { upper := (state.trial : WithTop ℝ)
          trial := state.trial / 2 } ↔
      ¬ feasiblePointArmijoAccepts f X c1 x d state.trial := by
  classical
  constructor
  · intro hStep
    by_cases hAccept : feasiblePointArmijoAccepts f X c1 x d state.trial
    · cases hUpper : state.upper with
      | top =>
          simp [feasibleDirectionArmijoStep, hAccept, hUpper] at hStep
      | coe αMax =>
          simp [feasibleDirectionArmijoStep, hAccept, hUpper] at hStep
    · exact hAccept
  · intro hReject
    simp [feasibleDirectionArmijoStep, hReject]

/-- `feasibleDirectionArmijoStep` has exactly the three Step 2/Step 3 branches from the source:
accepting trials with `α_max = +∞` double `α`, accepting trials with finite `α_max` stop, and
rejected trials set `α_max := α` and `α := α / 2`. -/
theorem feasibleDirectionArmijoStep_spec
    (f : Point → ℝ) (X : Set Point) (c1 : ℝ) (x d : Point)
    (state : FeasibleDirectionArmijoState) :
    (feasibleDirectionArmijoStep f X c1 x d state =
        FeasibleDirectionArmijoStepResult.continueWith
          { upper := (⊤ : WithTop ℝ)
            trial := 2 * state.trial } ↔
      feasiblePointArmijoAccepts f X c1 x d state.trial ∧ state.upper = ⊤) ∧
      (feasibleDirectionArmijoStep f X c1 x d state = .stop state.trial ↔
        feasiblePointArmijoAccepts f X c1 x d state.trial ∧
          ∃ αMax : ℝ, state.upper = αMax) ∧
      (feasibleDirectionArmijoStep f X c1 x d state =
          FeasibleDirectionArmijoStepResult.continueWith
            { upper := (state.trial : WithTop ℝ)
              trial := state.trial / 2 } ↔
        ¬ feasiblePointArmijoAccepts f X c1 x d state.trial) := by
  refine ⟨feasibleDirectionArmijoStep_eq_continueWith_infinity_iff, ?_⟩
  exact ⟨feasibleDirectionArmijoStep_eq_stop_iff,
    feasibleDirectionArmijoStep_eq_continueWith_reject_iff⟩

#print axioms feasibleDirectionArmijoInitialState
#print axioms feasibleDirectionArmijoStep

end Chapter11Algorithm1112
