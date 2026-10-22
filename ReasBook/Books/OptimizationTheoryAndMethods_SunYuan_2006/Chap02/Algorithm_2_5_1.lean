/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.WithTop

-- Semantic recall: `lean_leansearch` did not surface a dedicated mathlib owner for the
-- Goldstein-rule control flow, so this file records the algorithm through explicit
-- state data, one-step dynamics, and a finite-run owner. The bracket upper endpoint
-- itself is the standard `WithTop ℝ` owner for a finite real cutoff or `+∞`.

/-- The mutable state `(a_k, b_k, α_k, k)` used by the Goldstein line-search algorithm. -/
structure GoldsteinLineSearchState where
  lower : ℝ
  upper : WithTop ℝ
  trial : ℝ
  iteration : ℕ

/-- The admissible Goldstein parameter satisfies `0 < ρ < 1 / 2`. -/
def GoldsteinParameters (ρ : ℝ) : Prop :=
  0 < ρ ∧ ρ < 1 / 2

/-- Expanding `GoldsteinParameters` gives the parameter bounds `0 < ρ < 1 / 2`. -/
theorem goldsteinParameters_iff {ρ : ℝ} :
    GoldsteinParameters ρ ↔ 0 < ρ ∧ ρ < 1 / 2 :=
  Iff.rfl

/-- The Armijo-type sufficient-decrease inequality used in Step 2 of Goldstein line search. -/
def goldsteinSufficientDecrease
    (φ : ℝ → ℝ) (φPrime0 ρ α : ℝ) : Prop :=
  φ α ≤ φ 0 + ρ * α * φPrime0

/-- The lower Goldstein inequality used in Step 3 of Goldstein line search. -/
def goldsteinLowerInequality
    (φ : ℝ → ℝ) (φPrime0 ρ α : ℝ) : Prop :=
  φ 0 + (1 - ρ) * α * φPrime0 ≤ φ α

/-- The textbook Goldstein rule is the conjunction of the Step 2 and Step 3 inequalities. -/
def goldsteinCondition
    (φ : ℝ → ℝ) (φPrime0 ρ α : ℝ) : Prop :=
  goldsteinSufficientDecrease φ φPrime0 ρ α ∧
    goldsteinLowerInequality φ φPrime0 ρ α

/-- Step 1 requires `α₀ ≤ b₀`, where the initial upper bracket `b₀` lives in `WithTop ℝ`.
For the unbounded case `b₀ = ⊤`, this imposes no upper-side restriction. -/
def goldsteinInitialWithinUpperBound
    (α0 : ℝ) (upper0 : WithTop ℝ) : Prop :=
  (α0 : WithTop ℝ) ≤ upper0

/-- Step 1 of Goldstein line search initializes `a₀ = 0`, `b₀`, `α₀`, and `k = 0`. -/
def goldsteinLineSearchInitialState
    (α0 : ℝ) (upper0 : WithTop ℝ) : GoldsteinLineSearchState where
  lower := 0
  upper := upper0
  trial := α0
  iteration := 0

/-- One iteration of Goldstein line search either stops with an accepted step or produces the
next algorithmic state. -/
inductive GoldsteinLineSearchStepResult where
  | stop (acceptedStep : ℝ)
  | continueWith (nextState : GoldsteinLineSearchState)

/-- One iteration of the Goldstein line-search algorithm. Step 2 tests sufficient decrease;
failure replaces the upper endpoint by `α_k` and bisects. Step 3 tests the lower Goldstein
inequality; success stops, while failure replaces the lower endpoint by `α_k` and either
bisects against the current finite upper endpoint or expands to `t * α_k` when `b_k = ⊤`. -/
noncomputable def goldsteinLineSearchStep
    (φ : ℝ → ℝ) (φPrime0 ρ t : ℝ) (state : GoldsteinLineSearchState) :
    GoldsteinLineSearchStepResult :=
  if φ state.trial ≤ φ 0 + ρ * state.trial * φPrime0 then
    if φ 0 + (1 - ρ) * state.trial * φPrime0 ≤ φ state.trial then
      .stop state.trial
    else
      match state.upper with
      | ⊤ =>
          .continueWith
            { lower := state.trial
              upper := ⊤
              trial := t * state.trial
              iteration := state.iteration + 1 }
      | (b : ℝ) =>
          .continueWith
            { lower := state.trial
              upper := b
              trial := (state.trial + b) / 2
              iteration := state.iteration + 1 }
  else
    .continueWith
      { lower := state.lower
        upper := state.trial
        trial := (state.lower + state.trial) / 2
        iteration := state.iteration + 1 }

/-- `goldsteinLineSearchStep` stops exactly when the current trial step satisfies both
Goldstein inequalities. -/
theorem goldsteinLineSearchStep_eq_stop_iff
    {φ : ℝ → ℝ} {φPrime0 ρ t : ℝ} {state : GoldsteinLineSearchState} :
    goldsteinLineSearchStep φ φPrime0 ρ t state = .stop state.trial ↔
      goldsteinCondition φ φPrime0 ρ state.trial := by
  -- Split on the Step 2 sufficient-decrease test.
  by_cases hDecrease : φ state.trial ≤ φ 0 + ρ * state.trial * φPrime0
  · -- Under sufficient decrease, split on the Step 3 lower Goldstein inequality.
    by_cases hLower : φ 0 + (1 - ρ) * state.trial * φPrime0 ≤ φ state.trial
    · -- If both inequalities hold, the algorithm stops exactly at the current trial step.
      simp [goldsteinLineSearchStep, goldsteinCondition, goldsteinSufficientDecrease,
        goldsteinLowerInequality, hDecrease, hLower]
    · -- If the lower inequality fails, every branch continues with a new state.
      cases hUpper : state.upper <;>
        simp [goldsteinLineSearchStep, goldsteinCondition, goldsteinSufficientDecrease,
          goldsteinLowerInequality, hDecrease, hLower, hUpper]
  · -- If sufficient decrease already fails, the step cannot stop.
    simp [goldsteinLineSearchStep, goldsteinCondition, goldsteinSufficientDecrease,
      goldsteinLowerInequality, hDecrease]

/-- Input data for the Goldstein line-search algorithm from Chapter02 Algorithm 2.5.1.
This packages the input data and
state-transition rules for Goldstein line search on a one-dimensional model `φ`.

Step 1 chooses `α₀`, `ρ`, `t`, and the initial bracket endpoints `a₀ = 0` and `b₀ = upper₀`,
with `0 ≤ α₀` and `α₀ ≤ upper₀` in the canonical `WithTop ℝ` order, so the bounded case
`upper₀ = (α_max : WithTop ℝ)` recovers the textbook side condition `α₀ ≤ α_max`. The stored
slope datum `φPrime0` is tied to the model by
`HasDerivAt φ φPrime0 0`, so it represents the computed quantity `φ'(0)`. Steps 2-4 are
encoded by `GoldsteinLineSearch.step`, which applies
`goldsteinLineSearchStep φ φPrime0 ρ t` to the current state. -/
structure GoldsteinLineSearch (φ : ℝ → ℝ) where
  φPrime0 : ℝ
  hasDerivAt_zero : HasDerivAt φ φPrime0 0
  ρ : ℝ
  t : ℝ
  α0 : ℝ
  upper0 : WithTop ℝ
  parameters : GoldsteinParameters ρ
  expansion_gt_one : 1 < t
  initial_nonneg : 0 ≤ α0
  initial_within_upper : goldsteinInitialWithinUpperBound α0 upper0

/-- The `ρ` stored in a Goldstein line-search datum satisfies the textbook Goldstein
parameter bounds. -/
theorem GoldsteinLineSearch.parameters_iff
    {φ : ℝ → ℝ} (search : GoldsteinLineSearch φ) :
    0 < search.ρ ∧ search.ρ < (1 / 2 : ℝ) := by
  exact goldsteinParameters_iff.mp search.parameters

/-- The Step 1 state attached to a Goldstein line-search input datum. -/
def GoldsteinLineSearch.initialState
    {φ : ℝ → ℝ} (search : GoldsteinLineSearch φ) : GoldsteinLineSearchState :=
  goldsteinLineSearchInitialState search.α0 search.upper0

/-- The Steps 2-4 transition map attached to a Goldstein line-search input datum. -/
noncomputable def GoldsteinLineSearch.step
    {φ : ℝ → ℝ} (search : GoldsteinLineSearch φ) (state : GoldsteinLineSearchState) :
    GoldsteinLineSearchStepResult :=
  goldsteinLineSearchStep φ search.φPrime0 search.ρ search.t state

/-- A Goldstein line-search input datum can be used as its Steps 2-4 transition map. -/
noncomputable instance {φ : ℝ → ℝ} :
    CoeFun (GoldsteinLineSearch φ)
      (fun _ ↦ GoldsteinLineSearchState → GoldsteinLineSearchStepResult) where
  coe search := search.step

/-- Evaluating a Goldstein line-search input datum as a function returns its transition map. -/
theorem GoldsteinLineSearch.coe_apply {φ : ℝ → ℝ} (search : GoldsteinLineSearch φ)
    (state : GoldsteinLineSearchState) :
    search state = search.step state := by
  -- The coercion to functions is defined to be the step map.
  rfl

/-- A terminating execution trace of Goldstein line search for a one-dimensional model `φ`.

The run extends a Step 1 input datum `GoldsteinLineSearch φ`, so the initial state
`a₀ = 0`, `b₀ = upper₀ : WithTop ℝ`, `α₀`, `k = 0`, the parameter bounds `0 < ρ < 1 / 2`,
the expansion factor `t > 1`, and the derivative witness `HasDerivAt φ φPrime0 0`
are inherited directly from the underlying search datum. For each nonterminal index `j`,
the next state is produced by the inherited transition map `GoldsteinLineSearch.step`.
The run stops at the first index `terminalIndex` where the current trial step satisfies
the Goldstein rule and is therefore accepted. -/
structure GoldsteinLineSearchRun (φ : ℝ → ℝ) extends GoldsteinLineSearch φ where
  terminalIndex : ℕ
  state : ℕ → GoldsteinLineSearchState
  state_zero : state 0 = toGoldsteinLineSearch.initialState
  step_continue :
    ∀ j : ℕ, j < terminalIndex →
      toGoldsteinLineSearch.step (state j) = .continueWith (state (j + 1))
  terminal_stop :
    toGoldsteinLineSearch.step (state terminalIndex) = .stop (state terminalIndex).trial

/-- A Goldstein line-search run coerces to its recorded state sequence `k ↦ (a_k, b_k, α_k, k)`. -/
instance {φ : ℝ → ℝ} : CoeFun (GoldsteinLineSearchRun φ)
    (fun _ ↦ ℕ → GoldsteinLineSearchState) where
  coe run := run.state

/-- Evaluating a Goldstein line-search run as a function returns its recorded state sequence. -/
theorem GoldsteinLineSearchRun.coe_apply {φ : ℝ → ℝ} (run : GoldsteinLineSearchRun φ)
    (k : ℕ) : run k = run.state k := by
  -- The coercion to functions is defined to be the stored state sequence.
  rfl

/-- The `ρ` stored in a Goldstein line-search run satisfies the textbook Goldstein
parameter bounds. -/
theorem GoldsteinLineSearchRun.parameters_iff
    {φ : ℝ → ℝ} (run : GoldsteinLineSearchRun φ) :
    0 < run.ρ ∧ run.ρ < (1 / 2 : ℝ) := by
  exact run.toGoldsteinLineSearch.parameters_iff

/-- Chapter02 Algorithm 2.5.1 (Inexact Line Search with Goldstein Rule): the accepted terminal
step in a Goldstein line-search run satisfies the Goldstein rule. -/
theorem GoldsteinLineSearchRun.terminal_goldsteinCondition
    {φ : ℝ → ℝ} (run : GoldsteinLineSearchRun φ) :
    goldsteinCondition φ run.φPrime0 run.ρ (run.state run.terminalIndex).trial := by
  -- Rewrite the terminal stop witness into the underlying one-step transition.
  have hStop :
      goldsteinLineSearchStep φ run.φPrime0 run.ρ run.t (run.state run.terminalIndex) =
        .stop (run.state run.terminalIndex).trial := by
    simpa [GoldsteinLineSearch.step] using run.terminal_stop
  -- The step-stop characterization yields the Goldstein inequalities at the terminal step.
  exact goldsteinLineSearchStep_eq_stop_iff.mp hStop
